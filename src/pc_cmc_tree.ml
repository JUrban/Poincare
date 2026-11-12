(* ========================================================================= *)
(* Unit pc_cmc_tree: the planar bubble tree (CM App. B, end of the proof of  *)
(* Prop B.6 and Prop A.3 in the standard chart) by induction on the          *)
(* concentration mass, and CMC_PLANAR_BUBBLES.  First: predicates; trace and *)
(* energy convergence from L^2 convergence; small balls and tails; bubble    *)
(* lists.                                                                    *)
(* ========================================================================= *)

needs "src/pc_cmc_ndl.ml";;
needs "src/pc_cmc_xfer.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Predicates.  cmc_gseq: the standing hypotheses on a sequence of planar   *)
(* maps (closed under subsequences and similarities).  cmc_bok: a list of   *)
(* bubbles.  cmc_tconv: convergence of all trace integrals on D to those of *)
(* the base map plus the bubbles.                                            *)
(* ------------------------------------------------------------------------- *)

let cmc_gseq = new_definition
 `cmc_gseq (S:real^K->bool) (G:real^K->real^K^K) e0 E (TT:real^K->bool)
           (eta:num->real) (V:num->real^2->real^K) <=>
    (eta ---> &0) sequentially /\ (!j x. V j x IN TT) /\
    (!j. cmc_pmap S (V j) /\ cmc_ah S G e0 (eta j) (V j) /\
         cmc_pen G (:real^2) (V j) <= E) /\
    (!e. &0 < e
         ==> eventually (\j. cmc_pen G (:real^2) (V j) - cmc_ptr G G (:real^2) (V j) < e)
                        sequentially)`;;

let cmc_bok = new_definition
 `cmc_bok (S:real^K->bool) (G:real^K->real^K^K) (TT:real^K->bool) p
          (bb:num->real^2->real^K) <=>
    !i. 1 <= i /\ i <= p
        ==> cmc_pharm S G (bb i) /\ cmc_pmap S (bb i) /\ (!x. bb i x IN TT)`;;

let cmc_tconv = new_definition
 `cmc_tconv (G:real^K->real^K^K) (V:num->real^2->real^K) (D:real^2->bool)
            (b:real^2->real^K) p (bb:num->real^2->real^K) <=>
    !Q:real^K->real^K^K.
       smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
       (!z. transp(Q z) = Q z)
       ==> ((\j. cmc_ptr G Q D (V j)) --->
            cmc_ptr G Q D b + sum(1..p) (\i. cmc_ptr G Q (:real^2) (bb i)))
           sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Trace and energy convergence from L^2 convergence on bounded sets.        *)
(* ------------------------------------------------------------------------- *)

let CMC_PMAP_LSPACE_BOUNDED = prove
 (`!S (w:real^2->real^K) E.
     compact S /\ cmc_pmap S w /\ measurable E ==> w IN lspace E (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?MS. !z:real^K. z IN S ==> norm z <= MS` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; bounded]; ALL_TAC] THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `w:real^2->real^K`; `MS:real`] CMC_BOUNDED_LNORM) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[cmc_pmap];
    ASM_MESON_TAC[cmc_pmap]]);;

let CMC_PHARM_WD_AE = prove
 (`!S (G:real^K->real^K^K) (b:real^2->real^K) i.
     cmc_pharm S G b /\ 1 <= i /\ i <= 2
     ==> negligible {x | ~(wan_wd (:real^2) i b x = partial_derivative i b x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_WD_EQ_AE THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_pharm]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC WAN_WPD_C1 THEN REWRITE_TAC[OPEN_UNIV] THEN
  UNDISCH_TAC `smooth_map_on (:real^2) (b:real^2->real^K)` THEN SIMP_TAC[smooth_map_on]);;

let CMC_L2CONV_PTR = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (V:num->real^2->real^K) b E.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\
     (!j. cmc_pmap S (V j)) /\ cmc_pharm S G b /\ cmc_pmap S b /\
     measurable E /\ cmc_l2conv E V b
     ==> ((\j. cmc_ptr G Q E (V j)) ---> cmc_ptr G Q E b) sequentially /\
         ((\j. cmc_pen G E (V j)) ---> cmc_pen G E b) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `lebesgue_measurable(E:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. partial_derivative i (b:real^2->real^K) x) IN lspace E (&2) /\
            !j. wan_wd (:real^2) i ((V:num->real^2->real^K) j) IN lspace E (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[cmc_pharm];
      GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[CMC_PMAP_WD]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `V:num->real^2->real^K`; `b:real^2->real^K`;
                 `\x. partial_derivative 1 (b:real^2->real^K) x`;
                 `\x. partial_derivative 2 (b:real^2->real^K) x`; `E:real^2->bool`]
                CMC_DENS_JET_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[cmc_pmap];
      ASM_MESON_TAC[cmc_pmap];
      GEN_TAC THEN MATCH_MP_TAC CMC_JET_LSPACE THEN ASM_SIMP_TAC[ARITH] THEN
      MATCH_MP_TAC CMC_PMAP_LSPACE_BOUNDED THEN EXISTS_TAC `S:real^K->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_JET_LSPACE THEN ASM_SIMP_TAC[ARITH] THEN
      MATCH_MP_TAC CMC_PMAP_LSPACE_BOUNDED THEN EXISTS_TAC `S:real^K->bool` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`V:num->real^2->real^K`;
                     `\j. wan_wd (:real^2) 1 ((V:num->real^2->real^K) j)`;
                     `\j. wan_wd (:real^2) 2 ((V:num->real^2->real^K) j)`;
                     `b:real^2->real^K`; `\x. partial_derivative 1 (b:real^2->real^K) x`;
                     `\x. partial_derivative 2 (b:real^2->real^K) x`; `E:real^2->bool`]
                    CMC_JET_TOZERO) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `cmc_l2conv E (V:num->real^2->real^K) b` THEN
      REWRITE_TAC[cmc_l2conv] THEN STRIP_TAC THEN
      MP_TAC(SPEC `1` (ASSUME
       `!i. 1 <= i /\ i <= 2
            ==> (!j. (\x. wan_wd (:real^2) i ((V:num->real^2->real^K) j) x -
                          partial_derivative i b x) IN lspace E (&2)) /\
                ((\j. lnorm E (&2) (\x. wan_wd (:real^2) i (V j) x -
                                        partial_derivative i b x)) ---> &0)
                sequentially`)) THEN
      MP_TAC(SPEC `2` (ASSUME
       `!i. 1 <= i /\ i <= 2
            ==> (!j. (\x. wan_wd (:real^2) i ((V:num->real^2->real^K) j) x -
                          partial_derivative i b x) IN lspace E (&2)) /\
                ((\j. lnorm E (&2) (\x. wan_wd (:real^2) i (V j) x -
                                        partial_derivative i b x)) ---> &0)
                sequentially`)) THEN
      REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> c) /\ (b <=> d) ==> a /\ b ==> c /\ d`) THEN
  CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[cmc_ptr; cmc_pen] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | ~(wan_wd (:real^2) 1 (b:real^2->real^K) x = partial_derivative 1 b x)} UNION
              {x | ~(wan_wd (:real^2) 2 (b:real^2->real^K) x = partial_derivative 2 b x)}` THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THEN MATCH_MP_TAC CMC_PHARM_WD_AE THEN
     MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`] THEN
     ASM_REWRITE_TAC[ARITH];
     ALL_TAC]) THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  REWRITE_TAC[GEN_ALL(CONJUNCT1(SPEC_ALL CMC_TDEN_3)); CMC_EDEN_3] THEN ASM_REWRITE_TAC[]);;

let CMC_PTR_UNION = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (w:real^2->real^K) E E'.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\
     cmc_pmap S w /\ lebesgue_measurable E /\ lebesgue_measurable E' /\ DISJOINT E E'
     ==> cmc_ptr G Q (E UNION E') w = cmc_ptr G Q E w + cmc_ptr G Q E' w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
                CMC_PTR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[cmc_ptr; GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNION THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{}:real^2->bool` THEN
  REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN ASM SET_TAC[]);;

let CMC_PTR_BOUND = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K).
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z)
     ==> ?M. &0 <= M /\
             !(w:real^2->real^K) E.
                cmc_pmap S w /\ lebesgue_measurable E
                ==> abs(cmc_ptr G Q E w) <= M * cmc_pen G E w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
                CMC_PTR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

let CMC_SMALL_BALLS = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) e.
     cm_target S G d /\ cmc_pmap S w /\ &0 < e
     ==> ?r. &0 < r /\ !y s. s <= r ==> cmc_pen G (cball(y,s)) w < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `(:real^2)`] CMC_PEN_INTEGRABLE) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift(trace(cmc_gram (G:real^K->real^K^K) (w:real^2->real^K) x))`;
                 `(:real^2)`; `e:real`] ABSOLUTELY_CONTINUOUS_INTEGRAL) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (&1) (dd / &8)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^2`; `s:real`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `s < &0` THENL
   [SUBGOAL_THEN `cball(y:real^2,s) = {}` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CBALL_EQ_EMPTY]; ALL_TAC] THEN
    ASM_REWRITE_TAC[cmc_pen; INTEGRAL_EMPTY; DROP_VEC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cball(y:real^2,s)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEASURABLE_CBALL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&2 * s) pow dimindex(:2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_CBALL_BOUND THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_2] THEN
    SUBGOAL_THEN `&0 <= s /\ s <= &1 /\ s <= dd / &8` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * s` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `s * s <= s * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[cmc_pen] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x = n ==> n < e ==> x < e`) THEN
  REWRITE_TAC[NORM_REAL; GSYM drop]);;

let CMC_TAIL = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) e.
     cm_target S G d /\ cmc_pmap S w /\ &0 < e
     ==> ?R. &0 < R /\ !R'. R <= R' ==> cmc_pen G {y:real^2 | R' < norm y} w < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `(:real^2)`] CMC_PEN_INTEGRABLE) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `h = \x. lift(trace(cmc_gram (G:real^K->real^K^K) (w:real^2->real^K) x))` THEN
  SUBGOAL_THEN `!t. lebesgue_measurable t ==> (h:real^2->real^1) integrable_on t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN EXPAND_TAC "h" THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real. lebesgue_measurable {y:real^2 | t < norm y}` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    SUBGOAL_THEN `{y:real^2 | t < norm y} = (:real^2) DIFF cball(vec 0,t)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN REAL_ARITH_TAC;
      SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k x. if x IN {y:real^2 | &k < norm y} then (h:real^2->real^1) x
                        else vec 0`;
                 `\x:real^2. vec 0:real^1`; `h:real^2->real^1`; `(:real^2)`]
                DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real^2`] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN EXPAND_TAC "h" THEN
      REWRITE_TAC[NORM_0; DROP_VEC; LIFT_DROP; NORM_LIFT] THEN
      ASM_SIMP_TAC[REAL_LE_REFL; real_abs];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; IN_ELIM_THM] THEN
      MP_TAC(SPEC `norm(x:real^2)` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(&k < norm(x:real^2))` (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `&N <= &k` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; INTEGRAL_0; LIM_SEQUENTIALLY; DIST_0] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  EXISTS_TAC `&N + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `R':real` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `cmc_pen G {y:real^2 | &N < norm y} (w:real^2->real^K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMC_PEN_MONO THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cmc_pen] THEN MATCH_MP_TAC(REAL_ARITH `!x e. abs x < e ==> x < e`) THEN
  UNDISCH_TAC `norm(integral {y:real^2 | &N < norm y} (h:real^2->real^1)) < e` THEN
  EXPAND_TAC "h" THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN DISCH_THEN ACCEPT_TAC);;

let CMC_LIM_APPROX = prove
 (`!(a:num->real) L.
     (!e. &0 < e
          ==> ?(c:num->real) C. (c ---> C) sequentially /\ abs(C - L) <= e /\
                                eventually (\j. abs(a j - c j) <= e) sequentially)
     ==> (a ---> L) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `((c:num->real) ---> C) sequentially` THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  UNDISCH_TAC `eventually (\j. abs((a:num->real) j - c j) <= e / &4) sequentially` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

let CMC_BLIST_CONCAT = prove
 (`!p1 (bb1:num->real^2->real^K) p2 bb2.
     ?p bb. (!f:(real^2->real^K)->real.
               sum(1..p) (\i. f(bb i)) =
               sum(1..p1) (\i. f(bb1 i)) + sum(1..p2) (\i. f(bb2 i))) /\
            (!P. (!i. 1 <= i /\ i <= p1 ==> P(bb1 i)) /\
                 (!i. 1 <= i /\ i <= p2 ==> P(bb2 i))
                 ==> !i. 1 <= i /\ i <= p ==> P(bb i))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`p1 + p2:num`;
    `\i. if i <= p1 then (bb1:num->real^2->real^K) i else bb2(i - p1)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:(real^2->real^K)->real` THEN
    SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= p1 + 1`] THEN BINOP_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[];
      SUBGOAL_THEN `p1 + 1 = 1 + p1 /\ p1 + p2 = p2 + p1` (fun th -> REWRITE_TAC[th]) THENL
       [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUM_OFFSET] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i + p1 <= p1)`; ADD_SUB]];
    GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CMC_GSEQ_SUBSEQ = prove
 (`!S (G:real^K->real^K^K) e0 E TT (eta:num->real) (V:num->real^2->real^K)
    (t:num->num).
     cmc_gseq S G e0 E TT eta V /\ (!m n. m < n ==> t m < t n)
     ==> cmc_gseq S G e0 E TT (\j. eta(t j)) (\j. V(t j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_gseq] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMD_REALLIM_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] EVENTUALLY_SUBSEQUENCE)) THEN
  DISCH_THEN(MP_TAC o SPEC `t:num->num`) THEN ASM_REWRITE_TAC[o_DEF]);;

let CMC_INV_MUL_LT = prove
 (`!lam t s.
     &0 < lam
     ==> (inv lam * t < s <=> t < lam * s) /\ (inv lam * t <= s <=> t <= lam * s) /\
         (s < inv lam * t <=> lam * s < t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ]);;

let CMC_SIM_MEM = prove
 (`!(a:real^2) lam E x.
     &0 < lam ==> (x IN IMAGE (\z. a + lam % z) E <=> inv lam % (x - a) IN E)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_SUB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    DISCH_TAC THEN EXISTS_TAC `inv lam % (x - a:real^2)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC]);;

let CMC_SIM_IMAGES = prove
 (`!(a:real^2) lam c s r1 r2.
     &0 < lam
     ==> IMAGE (\z. a + lam % z) (ball(c,s)) = ball(a + lam % c,lam * s) /\
         IMAGE (\z. a + lam % z) (cball(c,s)) = cball(a + lam % c,lam * s) /\
         IMAGE (\z. a + lam % z) (cmc_ann c r1 r2) =
         cmc_ann (a + lam % c) (lam * r1) (lam * r2) /\
         IMAGE (\z. a + lam % z) (:real^2) = (:real^2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EXTENSION] THEN ASM_SIMP_TAC[CMC_SIM_MEM] THEN
  SUBGOAL_THEN
   `!x:real^2. norm(inv lam % (x - a) - c) = inv lam * norm(x - (a + lam % c)) /\
               dist(c,inv lam % (x - a)) = inv lam * dist(a + lam % c,x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `inv lam % (x - a) - c:real^2 = inv lam % (x - (a + lam % c))`
    ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; real_abs; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[NORM_SUB];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_BALL; IN_CBALL; cmc_ann; IN_ELIM_THM; IN_UNIV] THEN
  ASM_SIMP_TAC[CMC_INV_MUL_LT]);;

let CMC_GSEQ_SIM = prove
 (`!S (G:real^K->real^K^K) d e0 E TT (eta:num->real) (V:num->real^2->real^K)
    (y:num->real^2) (r:num->real).
     cm_target S G d /\ cmc_gseq S G e0 E TT eta V /\ (!j. &0 < r j)
     ==> cmc_gseq S G e0 E TT eta (\j z. V j (y j + r j % z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_gseq] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(SPEC `(:K)` CMCX_SIM) THEN REWRITE_TAC[CMC_SIM_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. cmc_pmap S (\z. (V:num->real^2->real^K) j (y j + r j % z)) /\
        cmc_pen G (:real^2) (\z. V j (y j + r j % z)) = cmc_pen G (:real^2) (V j) /\
        cmc_ptr G G (:real^2) (\z. V j (y j + r j % z)) = cmc_ptr G G (:real^2) (V j) /\
        cmc_ah S G e0 (eta j) (\z. V j (y j + r j % z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(V:num->real^2->real^K) j`; `(y:num->real^2) j`;
                                  `(r:num->real) j`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV; CMC_SIM_IMAGES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Convergence away from the centre; shrinking the ball; no concentration    *)
(* (mass below e0).                                                          *)
(* ------------------------------------------------------------------------- *)

let CMC_REALLIM_EV_LT = prove
 (`!(f:num->real) l c.
     (f ---> l) sequentially /\ l < c ==> eventually (\j. f j < c) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `c - l:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMC_PUNCT_CONV = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (V:num->real^2->real^K) b x rho r R E.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\
     (!j. cmc_pmap S (V j)) /\ cmc_pharm S G b /\ cmc_pmap S b /\
     (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
     &0 < r /\ R < &2 * rho /\ lebesgue_measurable E /\ E SUBSET cball(x,R) DIFF ball(x,r)
     ==> ((\j. cmc_ptr G Q E (V j)) ---> cmc_ptr G Q E b) sequentially /\
         ((\j. cmc_pen G E (V j)) ---> cmc_pen G E b) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMC_L2CONV_PTR THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `cball(x:real^2,R)` THEN REWRITE_TAC[MEASURABLE_CBALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMC_L2CONV_SUBSET THEN EXISTS_TAC `cball(x:real^2,R) DIFF ball(x,r)` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_DELETE; IN_BALL; IN_CBALL] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN UNDISCH_TAC `~(dist(x:real^2,z) < r)` THEN
    ASM_REWRITE_TAC[DIST_REFL]]);;

let CMC_TCONV_SHRINK = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) b x rho rho' p bb.
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ cmc_pharm S G b /\ cmc_pmap S b /\
     (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
     &0 < rho' /\ rho' <= rho /\ cmc_tconv G V (ball(x,rho')) b p bb
     ==> cmc_tconv G V (ball(x,rho)) b p bb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_tconv] THEN STRIP_TAC THEN
  X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Q:real^K->real^K^K`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^2,rho) = ball(x,rho') UNION (ball(x,rho) DIFF ball(x,rho'))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`x:real^2`; `rho':real`; `rho:real`] SUBSET_BALL) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^2->real^K. cmc_pmap S w
        ==> cmc_ptr G Q (ball(x,rho') UNION (ball(x,rho) DIFF ball(x,rho'))) w =
            cmc_ptr G Q (ball(x,rho')) w + cmc_ptr G Q (ball(x,rho) DIFF ball(x,rho')) w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_PTR_UNION THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `(cmc_ptr G Q (ball(x,rho')) b + cmc_ptr G Q (ball(x,rho) DIFF ball(x,rho')) b) +
    sum(1..p) (\i. cmc_ptr G Q (:real^2) ((bb:num->real^2->real^K) i)) =
    (cmc_ptr G Q (ball(x,rho')) b + sum(1..p) (\i. cmc_ptr G Q (:real^2) (bb i))) +
    cmc_ptr G Q (ball(x:real^2,rho) DIFF ball(x,rho')) (b:real^2->real^K)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `V:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                 `rho':real`; `rho:real`; `ball(x:real^2,rho) DIFF ball(x,rho')`]
                CMC_PUNCT_CONV) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_DIFF] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  MP_TAC(ISPECL [`x:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN SET_TAC[]);;

let CMC_L2LIM_AGREE = prove
 (`!(V:num->real^2->real^K) u b O.
     open O /\ u continuous_on O /\ b continuous_on O /\
     (!z. z IN O ==> ?s. &0 < s /\ ball(z,s) SUBSET O /\
                         cmc_l2conv (ball(z,s)) V u /\ cmc_l2conv (ball(z,s)) V b)
     ==> !z. z IN O ==> u z = b z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ball(z:real^2,s)`; `u:real^2->real^K`; `b:real^2->real^K`]
                HMD_CONT_AE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC CMC_L2CONV_UNIQUE THEN EXISTS_TAC `V:num->real^2->real^K` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]]);;

let CMC_L2CONV_UNION2 = prove
 (`!S (V:num->real^2->real^K) b E1 E2 K.
     compact S /\ (!j. cmc_pmap S (V j)) /\ smooth_map_on (:real^2) b /\
     compact K /\ K SUBSET E1 UNION E2 /\ cmc_l2conv E1 V b /\ cmc_l2conv E2 V b
     ==> cmc_l2conv K V b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_L2CONV_COVER THEN
  MAP_EVERY EXISTS_TAC [`\m:num. if m = 0 then E1 else (E2:real^2->bool)`; `{0,1}`] THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH];
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; ARITH] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `(V:num->real^2->real^K) j`; `(:real^2)`;
                   `b:real^2->real^K`; `K:real^2->bool`] CMC_LSPACE_AUTO) THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `(V:num->real^2->real^K) j`; `(:real^2)`;
                   `b:real^2->real^K`; `K:real^2->bool`] CMC_LSPACE_AUTO) THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV]]);;

let CMC_BT_NOCONC = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 E TT (eta:num->real)
    (V:num->real^2->real^K) b x rho M.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\
     cmc_gseq S G e0 E TT eta V /\ &0 < rho /\ cmc_pharm S G b /\ cmc_pmap S b /\
     (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
     ((\j. cmc_pen G (ball(x,rho)) (V j)) ---> M) sequentially /\
     M - cmc_pen G (ball(x,rho)) b < e0
     ==> ?t. (!m n. m < n ==> t m < t n) /\ cmc_l2conv (cball(x,rho)) (\j. V(t j)) b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_gseq]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `!j. cmc_pmap S ((V:num->real^2->real^K) j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (b:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmc_pharm; cm_harmonic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `b:real^2->real^K`;
                 `(e0 - (M - cmc_pen G (ball(x:real^2,rho)) (b:real^2->real^K))) / &2`]
                CMC_SMALL_BALLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min r0 (rho / &2)` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ r < rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                 `V:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                 `r:real`; `rho:real`; `ball(x:real^2,rho) DIFF ball(x,r)`]
                CMC_PUNCT_CONV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LEBESGUE_MEASURABLE_BALL;
                 LEBESGUE_MEASURABLE_DIFF] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MP_TAC(ISPECL [`x:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
    DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `!w:real^2->real^K. cmc_pmap S w
        ==> cmc_pen G (ball(x,rho)) w =
            cmc_pen G (ball(x,r)) w + cmc_pen G (ball(x,rho) DIFF ball(x,r)) w`
  (LABEL_TAC "UN") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ball(x:real^2,rho) = ball(x,r) UNION (ball(x,rho) DIFF ball(x,r))`
    MP_TAC THENL
     [MP_TAC(ISPECL [`x:real^2`; `r:real`; `rho:real`] SUBSET_BALL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])] THEN
    MATCH_MP_TAC CMC_PEN_UNION THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\j. cmc_pen G (ball(x,r)) ((V:num->real^2->real^K) j)) --->
     M - cmc_pen G (ball(x,rho) DIFF ball(x,r)) b) sequentially`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!j. cmc_pen G (ball(x,r)) ((V:num->real^2->real^K) j) =
          cmc_pen G (ball(x,rho)) (V j) - cmc_pen G (ball(x,rho) DIFF ball(x,r)) (V j)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN USE_THEN "UN" (MP_TAC o SPEC `(V:num->real^2->real^K) j`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `M - cmc_pen G (ball(x:real^2,rho) DIFF ball(x,r)) (b:real^2->real^K) < e0`
  ASSUME_TAC THENL
   [USE_THEN "UN" (MP_TAC o SPEC `b:real^2->real^K`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `cmc_pen G (ball(x:real^2,r)) (b:real^2->real^K) <
      (e0 - (M - cmc_pen G (ball(x,rho)) b)) / &2`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `cmc_pen G (cball(x:real^2,r)) (b:real^2->real^K)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
        ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL;
                        BALL_SUBSET_CBALL];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `eventually (\j. wan_gdir (ball(x,r)) G ((V:num->real^2->real^K) j) < e0) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\j. cmc_pen G (ball(x:real^2,r)) ((V:num->real^2->real^K) j)`;
                   `M - cmc_pen G (ball(x:real^2,rho) DIFF ball(x,r)) (b:real^2->real^K)`;
                   `e0:real`] CMC_REALLIM_EV_LT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(V:num->real^2->real^K) j`; `ball(x:real^2,r)`] CMC_GDIR_PEN) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`; `V:num->real^2->real^K`; `eta:num->real`; `x:real^2`; `r:real`]
                CMC_LOCAL_EV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `u:real^2->real^K`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `t:num->num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on ball(x,r / &32) /\
                (b:real^2->real^K) continuous_on ball(x,r / &32)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[cm_harmonic; SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(x,r / &32) DELETE x ==> (u:real^2->real^K) z = b z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_L2LIM_AGREE THEN
    EXISTS_TAC `\j. (V:num->real^2->real^K) ((t:num->num) j)` THEN
    SIMP_TAC[OPEN_DELETE; OPEN_BALL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `ball(x:real^2,r / &32) DELETE x` OPEN_CONTAINS_CBALL) THEN
    SIMP_TAC[OPEN_DELETE; OPEN_BALL] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ball(z:real^2,s) SUBSET cball(z,s)` ASSUME_TAC THENL
     [REWRITE_TAC[BALL_SUBSET_CBALL]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:real^2,s)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_L2CONV_SUBSET THEN EXISTS_TAC `ball(x:real^2,r / &32)` THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:real^2,s)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^2,r / &32) DELETE x` THEN
      ASM_REWRITE_TAC[DELETE_SUBSET];
      MATCH_MP_TAC CMC_L2CONV_SUBSET THEN EXISTS_TAC `cball(z:real^2,s)` THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
      MATCH_MP_TAC CMC_L2CONV_SUBSEQ THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^2,r / &32) DELETE x` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DELETE (x:real^2) SUBSET t DELETE x`) THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(x,r / &32) ==> (u:real^2->real^K) z = b z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_CONT_AE_EQ THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{x:real^2}` THEN
    REWRITE_TAC[NEGLIGIBLE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DELETE")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmc_l2conv (ball(x,r / &32)) (\j. (V:num->real^2->real^K) ((t:num->num) j)) b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_L2CONV_CONG THEN EXISTS_TAC `u:real^2->real^K` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC CMC_L2CONV_UNION2 THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `ball(x:real^2,r / &32)`;
                        `cball(x:real^2,rho) DIFF ball(x,r / &64)`] THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`x:real^2`; `r / &64`; `r / &32`] SUBSET_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
    MATCH_MP_TAC CMC_L2CONV_SUBSEQ THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_DELETE; IN_BALL; IN_CBALL] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `~(dist(x:real^2,z) < r / &64)` THEN
      ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC]]);;

let CMC_TCONV_L2 = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) b x rho (bb:num->real^2->real^K).
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ cmc_pharm S G b /\ cmc_pmap S b /\
     cmc_l2conv (cball(x,rho)) V b
     ==> cmc_tconv G V (ball(x,rho)) b 0 bb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_tconv; SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_RID] THEN
  X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `V:num->real^2->real^K`; `b:real^2->real^K`; `ball(x:real^2,rho)`]
                CMC_L2CONV_PTR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; MEASURABLE_BALL] THEN
    MATCH_MP_TAC CMC_L2CONV_SUBSET THEN EXISTS_TAC `cball(x:real^2,rho)` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; BALL_SUBSET_CBALL];
    SIMP_TAC[]]);;

let CMC_PTR_UNIONS_GEN = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (w:real^2->real^K)
    (B:A->real^2->bool) Y.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\ cmc_pmap S w /\ FINITE Y /\
     (!y. y IN Y ==> lebesgue_measurable(B y)) /\
     (!y y'. y IN Y /\ y' IN Y /\ ~(y = y') ==> DISJOINT (B y) (B y'))
     ==> sum Y (\y. cmc_ptr G Q (B y) w) = cmc_ptr G Q (UNIONS (IMAGE B Y)) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!Y. FINITE Y
        ==> ((!y. y IN Y ==> lebesgue_measurable((B:A->real^2->bool) y)) /\
             (!y y'. y IN Y /\ y' IN Y /\ ~(y = y') ==> DISJOINT (B y) (B y'))
             ==> sum Y (\y. cmc_ptr G Q (B y) (w:real^2->real^K)) =
                 cmc_ptr G Q (UNIONS (IMAGE B Y)) w)`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES; IMAGE_CLAUSES; UNIONS_0; cmc_ptr; INTEGRAL_EMPTY; DROP_VEC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `Z:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES; IMAGE_CLAUSES; UNIONS_INSERT] THEN
  SUBGOAL_THEN `sum Z (\y. cmc_ptr G Q ((B:A->real^2->bool) y) (w:real^2->real^K)) =
                cmc_ptr G Q (UNIONS (IMAGE B Z)) w` SUBST1_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMC_PTR_UNION THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let CMC_COMBINE = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) b X s c R p
    (bb:num->real^2->real^K).
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ cmc_pharm S G b /\ cmc_pmap S b /\
     FINITE X /\ (!K. compact K /\ K SUBSET (:real^2) DIFF X ==> cmc_l2conv K V b) /\
     &0 < s /\ (!z. z IN X ==> ball(z,s) SUBSET cball(c,R)) /\
     (!z z'. z IN X /\ z' IN X /\ ~(z = z') ==> DISJOINT (ball(z,s)) (ball(z',s))) /\
     (!Q:real^K->real^K^K.
         smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
         (!z. transp(Q z) = Q z)
         ==> ((\j. sum X (\y. cmc_ptr G Q (ball(y,s)) (V j))) --->
              sum X (\y. cmc_ptr G Q (ball(y,s)) b) +
              sum(1..p) (\i. cmc_ptr G Q (:real^2) (bb i))) sequentially)
     ==> cmc_tconv G V (cball(c,R)) b p bb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmc_tconv] THEN
  X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Q:real^K->real^K^K`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS (IMAGE (\y:real^2. ball(y,s)) X)` THEN
  SUBGOAL_THEN `U SUBSET cball(c:real^2,R) /\ open U /\ (!z:real^2. z IN X ==> z IN U)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^2->real^K. cmc_pmap S w
        ==> cmc_ptr G Q (cball(c,R)) w =
            cmc_ptr G Q (cball(c,R) DIFF U) w + sum X (\y. cmc_ptr G Q (ball(y,s)) w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `w:real^2->real^K`; `\y:real^2. ball(y,s)`; `X:real^2->bool`]
                  CMC_PTR_UNIONS_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `w:real^2->real^K`; `cball(c:real^2,R) DIFF U`; `U:real^2->bool`]
                  CMC_PTR_UNION) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; LEBESGUE_MEASURABLE_DIFF;
                   LEBESGUE_MEASURABLE_CBALL] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `U SUBSET cball(c:real^2,R)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `V:num->real^2->real^K`; `b:real^2->real^K`; `cball(c:real^2,R) DIFF U`]
                CMC_L2CONV_PTR) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  SUBGOAL_THEN `compact(cball(c:real^2,R) DIFF U)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `!z:real^2. z IN X ==> z IN U` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The blow-up scales: within a factor 2 the least radius r such that some *)
(* ball cball(y,r), y near x, carries all but eps3 of the energy.          *)
(* ------------------------------------------------------------------------- *)

let CMC_INF_CHOICE = prove
 (`!(Fn:real^2->real->real) A c rho e good.
     &0 < rho /\ c IN A /\ Fn c rho <= e /\
     (good ==> ?r0. &0 < r0 /\ !y r. y IN A /\ &0 < r /\ r <= r0 ==> e < Fn y r)
     ==> ?r y. &0 < r /\ y IN A /\ Fn y r <= e /\
               (good ==> (!y' r'. y' IN A /\ &0 < r' /\ r' <= r / &2 ==> e < Fn y' r') /\
                         (!y' dd. y' IN A /\ &0 < dd /\ Fn y' dd <= e ==> r < &2 * dd))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `good:bool` THENL
   [ALL_TAC; MAP_EVERY EXISTS_TAC [`rho:real`; `c:real^2`] THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LB"))) THEN
  ABBREV_TAC `R = {r | &0 < r /\ ?y. y IN A /\ (Fn:real^2->real->real) y r <= e}` THEN
  SUBGOAL_THEN `!r. r IN R <=> &0 < r /\ ?y. y IN A /\ (Fn:real^2->real->real) y r <= e`
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN R ==> r0 < r` ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "LB" (MP_TAC o SPECL [`y:real^2`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho:real) IN R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `R:real->bool` INF) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
      EXISTS_TAC `r0:real` THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "I2"))] THEN
  SUBGOAL_THEN `r0 <= inf R` ASSUME_TAC THENL
   [USE_THEN "I2" MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `?r. r IN R /\ r < &2 * inf R` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?r. r IN R /\ r < &2 * inf R` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&2 * inf R <= inf R` MP_TAC THENL
     [USE_THEN "I2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(r:real) IN R` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `y:real^2`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y':real^2`; `r':real`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "I1" (MP_TAC o SPEC `r':real`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `y':real^2` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`y':real^2`; `dd:real`] THEN STRIP_TAC THEN
    USE_THEN "I1" (MP_TAC o SPEC `dd:real`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `y':real^2` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

let CMC_PEN_DIFF_GE = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) A B.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable A /\ lebesgue_measurable B
     ==> cmc_pen G A w <= cmc_pen G (A DIFF B) w + cmc_pen G B w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cmc_pen G ((A DIFF B) UNION B) (w:real^2->real^K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNION; LEBESGUE_MEASURABLE_DIFF] THEN SET_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC CMC_PEN_UNION THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF] THEN SET_TAC[]]);;

let CMC_BLOWUP_SCALES = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) x rho eps3.
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ &0 < rho /\ &0 < eps3 /\
     eventually (\j. eps3 < cmc_pen G (ball(x,rho)) (V j)) sequentially /\
     (!dl. &0 < dl /\ dl < rho
           ==> eventually (\j. cmc_pen G (ball(x,rho) DIFF cball(x,dl)) (V j) < eps3)
                          sequentially) /\
     (!dl. &0 < dl /\ dl < rho
           ==> eventually (\j. eps3 < cmc_pen G (ball(x,dl)) (V j)) sequentially)
     ==> ?(r:num->real) (y:num->real^2).
           (!j. &0 < r j /\ y j IN cball(x,rho / &4) /\
                cmc_pen G (ball(x,rho) DIFF cball(y j,r j)) (V j) <= eps3) /\
           eventually (\j. !y' r'. y' IN cball(x,rho / &4) /\ &0 < r' /\ r' <= r j / &2
                                   ==> eps3 < cmc_pen G (ball(x,rho) DIFF cball(y',r')) (V j))
                      sequentially /\
           (!dl. &0 < dl ==> eventually (\j. r j < dl) sequentially) /\
           (!dl. &0 < dl ==> eventually (\j. dist(y j,x) < dl) sequentially)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "GOOD") (CONJUNCTS_THEN2 (LABEL_TAC "OUT")
    (LABEL_TAC "IN"))))))) THEN
  SUBGOAL_THEN
   `!j. ?r y. &0 < r /\ y IN cball(x:real^2,rho / &4) /\
              cmc_pen G (ball(x,rho) DIFF cball(y,r)) ((V:num->real^2->real^K) j) <= eps3 /\
              (eps3 < cmc_pen G (ball(x,rho)) (V j)
               ==> (!y' r'. y' IN cball(x,rho / &4) /\ &0 < r' /\ r' <= r / &2
                            ==> eps3 < cmc_pen G (ball(x,rho) DIFF cball(y',r')) (V j)) /\
                   (!y' dd. y' IN cball(x,rho / &4) /\ &0 < dd /\
                            cmc_pen G (ball(x,rho) DIFF cball(y',dd)) (V j) <= eps3
                            ==> r < &2 * dd))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`\y r. cmc_pen G (ball(x:real^2,rho) DIFF cball(y,r))
                                    ((V:num->real^2->real^K) j)`;
                   `cball(x:real^2,rho / &4)`; `x:real^2`; `rho:real`; `eps3:real`;
                   `eps3 < cmc_pen G (ball(x:real^2,rho)) ((V:num->real^2->real^K) j)`]
                  CMC_INF_CHOICE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `ball(x:real^2,rho) DIFF cball(x,rho) = {}` SUBST1_TAC THENL
       [MP_TAC(ISPECL [`x:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
        ASM_SIMP_TAC[cmc_pen; INTEGRAL_EMPTY; DROP_VEC; REAL_LT_IMP_LE]];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `(V:num->real^2->real^K) j`;
                     `cmc_pen G (ball(x:real^2,rho)) ((V:num->real^2->real^K) j) - eps3`]
                    CMC_SMALL_BALLS) THEN
      ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r0:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`y':real^2`; `r':real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `(V:num->real^2->real^K) j`; `ball(x:real^2,rho)`;
                     `cball(y':real^2,r')`] CMC_PEN_DIFF_GE) THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y':real^2`; `r':real`]) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->real` (X_CHOOSE_THEN `y:num->real^2` (LABEL_TAC "RY"))) THEN
  EXISTS_TAC `r:num->real` THEN EXISTS_TAC `y:num->real^2` THEN
  SUBGOAL_THEN `!dl. &0 < dl ==> eventually (\j. (r:num->real) j < dl) sequentially`
  (LABEL_TAC "P3") THENL
   [X_GEN_TAC `dl:real` THEN DISCH_TAC THEN
    USE_THEN "OUT" (MP_TAC o SPEC `min dl rho / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(CONJ (ASSUME `eventually (\j. cmc_pen G (ball(x:real^2,rho) DIFF
                                           cball(x,min dl rho / &2))
                                           ((V:num->real^2->real^K) j) < eps3) sequentially`)
                (ASSUME `eventually (\j. eps3 < cmc_pen G (ball(x:real^2,rho))
                                           ((V:num->real^2->real^K) j)) sequentially`)) THEN
    REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "RY" (MP_TAC o MATCH_MP
      (TAUT `a /\ b /\ c /\ (g ==> p /\ q) ==> g ==> q`) o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^2`; `min dl rho / &2`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "RY" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    USE_THEN "GOOD" MP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "RY" (MP_TAC o MATCH_MP
      (TAUT `a /\ b /\ c /\ (g ==> p /\ q) ==> g ==> p`) o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    USE_THEN "P3" ACCEPT_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `dl:real` THEN DISCH_TAC THEN
  USE_THEN "P3" (MP_TAC o SPEC `min dl rho / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "IN" (MP_TAC o SPEC `min dl rho / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(CONJ (ASSUME `eventually (\j. (r:num->real) j < min dl rho / &2) sequentially`)
              (ASSUME `eventually (\j. eps3 < cmc_pen G (ball(x:real^2,min dl rho / &2))
                                         ((V:num->real^2->real^K) j)) sequentially`)) THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  USE_THEN "RY" (MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `cmc_pen G (ball(x:real^2,min dl rho / &2)) ((V:num->real^2->real^K) j) <=
    cmc_pen G (ball(x,rho) DIFF cball((y:num->real^2) j,(r:num->real) j)) (V j)`
  MP_TAC THENL
   [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_CBALL] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `dl <= dist((y:num->real^2) j,x)` THEN
    UNDISCH_TAC `dist(x:real^2,z) < min dl rho / &2` THEN
    UNDISCH_TAC `(r:num->real) j < min dl rho / &2` THEN CONV_TAC NORM_ARITH;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The rescaled maps U_j(z) = V_j(y_j + r_j z): mass bound at every point,   *)
(* the neck inequality and the splitting of the trace integrals.             *)
(* ------------------------------------------------------------------------- *)

let CMC_SIM_PEN_PTR = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) (a:real^2) lam E.
     cm_target S G d /\ cmc_pmap S w /\ &0 < lam /\ lebesgue_measurable E
     ==> cmc_pmap S (\z. w(a + lam % z)) /\
         cmc_pen G E (\z. w(a + lam % z)) = cmc_pen G (IMAGE (\z. a + lam % z) E) w /\
         !Q:real^K->real^K^K.
            ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K)
            ==> cmc_ptr G Q E (\z. w(a + lam % z)) =
                cmc_ptr G Q (IMAGE (\z. a + lam % z) E) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `(:K)` CMCX_SIM) THEN REWRITE_TAC[CMC_SIM_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:real^2->real^K`; `a:real^2`; `lam:real`]) THEN
  ASM_SIMP_TAC[]);;

let CMC_BLOWUP_MASS = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) x rho eps3 (r:num->real)
    (y:num->real^2) z0 s.
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ &0 < rho /\ (!j. &0 < r j) /\
     eventually (\j. !y' r'. y' IN cball(x,rho / &4) /\ &0 < r' /\ r' <= r j / &2
                             ==> eps3 < cmc_pen G (ball(x,rho) DIFF cball(y',r')) (V j))
                sequentially /\
     (!dl. &0 < dl ==> eventually (\j. r j < dl) sequentially) /\
     (!dl. &0 < dl ==> eventually (\j. dist(y j,x) < dl) sequentially) /\
     &0 < s /\ s <= &1 / &2
     ==> eventually (\j. cmc_pen G (ball(z0,s)) (\z. V j (y j + r j % z)) + eps3 <
                         cmc_pen G (ball(x,rho)) (V j)) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "P3")
   (CONJUNCTS_THEN2 (LABEL_TAC "P4") STRIP_ASSUME_TAC))))))) THEN
  USE_THEN "P3" (MP_TAC o SPEC `rho / (&8 * (norm(z0:real^2) + &1))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    MP_TAC(ISPEC `z0:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  USE_THEN "P4" (MP_TAC o SPEC `rho / &8`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
     not (is_forall(concl th)))) THEN
  UNDISCH_TAC `eventually (\j. dist((y:num->real^2) j,x) < rho / &8) sequentially` THEN
  UNDISCH_TAC `eventually (\j. (r:num->real) j < rho / (&8 * (norm(z0:real^2) + &1)))
                          sequentially` THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "P2")) THEN
  ABBREV_TAC `c = (y:num->real^2) j + (r:num->real) j % z0` THEN
  SUBGOAL_THEN `&0 < norm(z0:real^2) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z0:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(r:num->real) j * (norm(z0:real^2) + &1) < rho / &8` ASSUME_TAC THENL
   [UNDISCH_TAC `(r:num->real) j < rho / (&8 * (norm(z0:real^2) + &1))` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < a ==> &0 < &8 * a`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(r:num->real) j < rho / (&8 * (norm(z0:real^2) + &1))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `dist(x:real^2,c) <= dist(x,(y:num->real^2) j) + (r:num->real) j * norm(z0:real^2)`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    SUBGOAL_THEN `norm((r:num->real) j % (z0:real^2)) = r j * norm z0` MP_TAC THENL
     [ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < x ==> abs x = x`]; ALL_TAC] THEN
    SPEC_TAC(`(r:num->real) j * norm(z0:real^2)`,`m:real`) THEN
    SPEC_TAC(`(r:num->real) j % (z0:real^2)`,`v:real^2`) THEN
    SPEC_TAC(`(y:num->real^2) j`,`yj:real^2`) THEN
    REPEAT GEN_TAC THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (r:num->real) j * norm(z0:real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (r:num->real) j * s /\ r j * s <= r j / &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL] THEN
    SUBGOAL_THEN `(r:num->real) j * s <= r j * (&1 / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "P2" (MP_TAC o SPECL [`c:real^2`; `(r:num->real) j * s`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_CBALL] THEN
    MP_TAC(ISPECL [`x:real^2`; `(y:num->real^2) j`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `ball(c:real^2,(r:num->real) j * s) SUBSET ball(x,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `z:real^2` THEN
    MP_TAC(ISPECL [`x:real^2`; `c:real^2`; `z:real^2`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`x:real^2`; `(y:num->real^2) j`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmc_pen G (ball(c,(r:num->real) j * s)) ((V:num->real^2->real^K) j) +
    cmc_pen G (ball(x,rho) DIFF cball(c,r j * s)) (V j) <= cmc_pen G (ball(x,rho)) (V j)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(V:num->real^2->real^K) j`; `ball(c:real^2,(r:num->real) j * s)`;
                   `ball(x:real^2,rho) DIFF cball(c,(r:num->real) j * s)`] CMC_PEN_UNION) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_DIFF;
                   LEBESGUE_MEASURABLE_CBALL] THEN
      MP_TAC(ISPECL [`c:real^2`; `(r:num->real) j * s`] BALL_SUBSET_CBALL) THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNION; LEBESGUE_MEASURABLE_BALL;
                 LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_CBALL] THEN
    UNDISCH_TAC `ball(c:real^2,(r:num->real) j * s) SUBSET ball(x,rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmc_pen G (ball(z0,s)) (\z. (V:num->real^2->real^K) j ((y:num->real^2) j +
                                                         (r:num->real) j % z)) =
    cmc_pen G (ball(c,r j * s)) (V j)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(V:num->real^2->real^K) j`; `(y:num->real^2) j`; `(r:num->real) j`;
                   `ball(z0:real^2,s)`] CMC_SIM_PEN_PTR) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; CMC_SIM_IMAGES];
    ASM_REAL_ARITH_TAC]);;

let CMC_BLOWUP_NECK = prove
 (`!S (G:real^K->real^K^K) d e0 E TT (eta:num->real) (V:num->real^2->real^K) x rho eps3
    (r:num->real) (y:num->real^2) L e2 Kc R dl.
     cm_target S G d /\ cmc_gseq S G e0 E TT eta V /\ &0 < rho /\ &0 < e0 /\
     &0 < L /\ eps3 <= e2 /\ &0 <= Kc /\
     (!(w:real^2->real^K) eta (y:real^2) a b.
         cmc_pmap S w /\ cmc_ah S G e0 eta w /\ &0 < a /\ a * exp L <= b /\
         cmc_pen G (cmc_ann y a b) w <= e2
         ==> cmc_pen G (cmc_ann y a b) w <=
             &2 * cmc_pen G (cmc_ann y a (a * exp L)) w +
             &2 * cmc_pen G (cmc_ann y (b * exp(--L)) b) w +
             Kc * (eta + (cmc_pen G (cmc_ann y a b) w - cmc_ptr G G (cmc_ann y a b) w))) /\
     (!j. &0 < r j /\ cmc_pen G (ball(x,rho) DIFF cball(y j,r j)) (V j) <= eps3) /\
     (!dl. &0 < dl ==> eventually (\j. r j < dl) sequentially) /\
     (!dl. &0 < dl ==> eventually (\j. dist(y j,x) < dl) sequentially) /\
     &1 <= R /\ &0 < dl /\ &3 * dl < rho
     ==> eventually
           (\j. cmc_pen G (cmc_ann (y j) (r j * R) (&2 * dl)) (V j) <=
                &2 * cmc_pen G (cmc_ann (vec 0) R (R * exp L)) (\z. V j (y j + r j % z)) +
                &2 * cmc_pen G (cmc_ann x (dl * exp(--L)) (&3 * dl)) (V j) +
                Kc * (eta j + (cmc_pen G (:real^2) (V j) - cmc_ptr G G (:real^2) (V j))))
           sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "NE") (CONJUNCTS_THEN2 (LABEL_TAC "RY")
   (CONJUNCTS_THEN2 (LABEL_TAC "P3") (CONJUNCTS_THEN2 (LABEL_TAC "P4")
    STRIP_ASSUME_TAC))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_gseq]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `&0 < exp(--L) /\ exp(--L) <= &1 /\ &0 < exp L` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R * exp L /\ &0 < dl * exp(--L) /\ dl * exp(--L) <= dl`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `dl * e <= dl * &1 ==> dl * e <= dl`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "P3" (MP_TAC o SPEC `(&2 * dl) / (R * exp L)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "P4" (MP_TAC o SPEC `dl * exp(--L)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((r:num->real) j * R) * exp L <= &2 * dl` ASSUME_TAC THENL
   [UNDISCH_TAC `(r:num->real) j < (&2 * dl) / (R * exp L)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(r:num->real) j < (&2 * dl) / (R * exp L)` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < (r:num->real) j /\ r j <= r j * R /\ &0 < r j * R` STRIP_ASSUME_TAC THENL
   [USE_THEN "RY" (MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `r * &1 <= r * R ==> r <= r * R`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "NE" (MP_TAC o SPECL [`(V:num->real^2->real^K) j`; `(eta:num->real) j`;
                                 `(y:num->real^2) j`; `(r:num->real) j * R`; `&2 * dl`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps3:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmc_pen G (ball(x:real^2,rho) DIFF cball((y:num->real^2) j,(r:num->real) j))
                          ((V:num->real^2->real^K) j)` THEN
    CONJ_TAC THENL
     [ALL_TAC; USE_THEN "RY" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[]] THEN
    MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL] THEN
    REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM; IN_DIFF; IN_BALL; IN_CBALL] THEN
    X_GEN_TAC `z:real^2` THEN
    UNDISCH_TAC `dist((y:num->real^2) j,x) < dl * exp(--L)` THEN
    UNDISCH_TAC `dl * exp(--L) <= dl` THEN UNDISCH_TAC `&3 * dl < rho` THEN
    UNDISCH_TAC `(r:num->real) j <= r j * R` THEN
    SPEC_TAC(`dl * exp(--L)`,`dl1:real`) THEN SPEC_TAC(`(r:num->real) j * R`,`a:real`) THEN
    SPEC_TAC(`(r:num->real) j`,`rr:real`) THEN SPEC_TAC(`(y:num->real^2) j`,`yj:real^2`) THEN
    REPEAT GEN_TAC THEN CONV_TAC NORM_ARITH;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `cmc_pen G (cmc_ann ((y:num->real^2) j) ((r:num->real) j * R) ((r j * R) * exp L))
             ((V:num->real^2->real^K) j) =
    cmc_pen G (cmc_ann (vec 0) R (R * exp L)) (\z. V j (y j + r j % z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(V:num->real^2->real^K) j`; `(y:num->real^2) j`; `(r:num->real) j`;
                   `cmc_ann (vec 0:real^2) R (R * exp L)`] CMC_SIM_PEN_PTR) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN; CMC_SIM_IMAGES] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmc_pen G (cmc_ann ((y:num->real^2) j) ((&2 * dl) * exp(--L)) (&2 * dl))
             ((V:num->real^2->real^K) j) <=
    cmc_pen G (cmc_ann x (dl * exp(--L)) (&3 * dl)) (V j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN
    REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    SUBGOAL_THEN `(&2 * dl) * exp(--L) = &2 * (dl * exp(--L))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `dist((y:num->real^2) j,x) < dl * exp(--L)` THEN
    UNDISCH_TAC `dl * exp(--L) <= dl` THEN
    SPEC_TAC(`dl * exp(--L)`,`dl1:real`) THEN SPEC_TAC(`(y:num->real^2) j`,`yj:real^2`) THEN
    REPEAT GEN_TAC THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `(V:num->real^2->real^K) j`;
                 `cmc_ann ((y:num->real^2) j) ((r:num->real) j * R) (&2 * dl)`;
                 `(:real^2)`] CMC_DEFECT_MONO) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN; LEBESGUE_MEASURABLE_UNIV;
               SUBSET_UNIV] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (eta:num->real) j` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_AH_ETA_POS THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`;
                          `(V:num->real^2->real^K) j`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Kc * ((eta:num->real) j +
          (cmc_pen G (cmc_ann ((y:num->real^2) j) ((r:num->real) j * R) (&2 * dl))
                     ((V:num->real^2->real^K) j) -
           cmc_ptr G G (cmc_ann (y j) (r j * R) (&2 * dl)) (V j))) <=
    Kc * (eta j + (cmc_pen G (:real^2) (V j) - cmc_ptr G G (:real^2) (V j)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMC_BLOWUP_SPLIT = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) M (V:num->real^2->real^K) x rho
    (r:num->real) (y:num->real^2) R dl.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\ &0 <= M /\
     (!(w:real^2->real^K) E. cmc_pmap S w /\ lebesgue_measurable E
                             ==> abs(cmc_ptr G Q E w) <= M * cmc_pen G E w) /\
     (!j. cmc_pmap S (V j)) /\ (!j. &0 < r j) /\
     (!dl. &0 < dl ==> eventually (\j. r j < dl) sequentially) /\
     (!dl. &0 < dl ==> eventually (\j. dist(y j,x) < dl) sequentially) /\
     &0 < R /\ &0 < dl /\ dl <= rho
     ==> eventually
           (\j. cmc_ptr G Q (ball(x,rho)) (V j) =
                cmc_ptr G Q (ball(x,rho) DIFF ball(x,dl)) (V j) +
                cmc_ptr G Q (ball(x,dl) DIFF cball(y j,r j * R)) (V j) +
                cmc_ptr G Q (cball(vec 0,R)) (\z. V j (y j + r j % z)) /\
                abs(cmc_ptr G Q (ball(x,dl) DIFF cball(y j,r j * R)) (V j)) <=
                M * cmc_pen G (cmc_ann (y j) (r j * R) (&2 * dl)) (V j))
           sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "BD") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "P3")
   (CONJUNCTS_THEN2 (LABEL_TAC "P4") STRIP_ASSUME_TAC))))))))) THEN
  USE_THEN "P3" (MP_TAC o SPEC `dl / (&2 * R)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "P4" (MP_TAC o SPEC `dl / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:num->real) j * R < dl / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `(r:num->real) j < dl / (&2 * R)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < R ==> &0 < &2 * R`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(r:num->real) j < dl / (&2 * R)` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < (r:num->real) j * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cball((y:num->real^2) j,(r:num->real) j * R) SUBSET ball(x,dl)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN X_GEN_TAC `z:real^2` THEN
    MP_TAC(ISPECL [`x:real^2`; `(y:num->real^2) j`; `z:real^2`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`x:real^2`; `(y:num->real^2) j`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^2,dl) SUBSET ball(x,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^2->real^K. cmc_pmap S w
       ==> cmc_ptr G Q (ball(x,rho)) w =
           cmc_ptr G Q (ball(x,rho) DIFF ball(x,dl)) w +
           cmc_ptr G Q (ball(x,dl) DIFF cball((y:num->real^2) j,(r:num->real) j * R)) w +
           cmc_ptr G Q (cball(y j,r j * R)) w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `w:real^2->real^K`;
                   `ball(x:real^2,dl) DIFF cball((y:num->real^2) j,(r:num->real) j * R)`;
                   `cball((y:num->real^2) j,(r:num->real) j * R)`] CMC_PTR_UNION) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL;
                   LEBESGUE_MEASURABLE_CBALL] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `w:real^2->real^K`; `ball(x:real^2,rho) DIFF ball(x,dl)`;
                   `(ball(x:real^2,dl) DIFF cball((y:num->real^2) j,(r:num->real) j * R))
                    UNION cball(y j,r j * R)`] CMC_PTR_UNION) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL;
                   LEBESGUE_MEASURABLE_CBALL; LEBESGUE_MEASURABLE_UNION] THEN
      UNDISCH_TAC `cball((y:num->real^2) j,(r:num->real) j * R) SUBSET ball(x,dl)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(ball(x:real^2,rho) DIFF ball(x,dl)) UNION
      ((ball(x,dl) DIFF cball((y:num->real^2) j,(r:num->real) j * R)) UNION
       cball(y j,r j * R)) = ball(x,rho)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `cball((y:num->real^2) j,(r:num->real) j * R) SUBSET ball(x,dl)` THEN
      UNDISCH_TAC `ball(x:real^2,dl) SUBSET ball(x,rho)` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmc_ptr G Q (cball(vec 0,R)) (\z. (V:num->real^2->real^K) j ((y:num->real^2) j +
                                                              (r:num->real) j % z)) =
    cmc_ptr G Q (cball(y j,r j * R)) (V j)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(V:num->real^2->real^K) j`; `(y:num->real^2) j`; `(r:num->real) j`;
                   `cball(vec 0:real^2,R)`] CMC_SIM_PEN_PTR) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CBALL; CMC_SIM_IMAGES] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `M * cmc_pen G (ball(x:real^2,dl) DIFF cball((y:num->real^2) j,(r:num->real) j * R))
                            ((V:num->real^2->real^K) j)` THEN
  CONJ_TAC THENL
   [USE_THEN "BD" (MP_TAC o SPECL [`(V:num->real^2->real^K) j`;
                    `ball(x:real^2,dl) DIFF cball((y:num->real^2) j,(r:num->real) j * R)`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL;
                   LEBESGUE_MEASURABLE_CBALL];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL;
               LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN
  REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM; IN_DIFF; IN_BALL; IN_CBALL] THEN
  X_GEN_TAC `z:real^2` THEN
  UNDISCH_TAC `dist((y:num->real^2) j,x) < dl / &2` THEN
  SPEC_TAC(`(r:num->real) j * R`,`a:real`) THEN SPEC_TAC(`(y:num->real^2) j`,`yj:real^2`) THEN
  REPEAT GEN_TAC THEN CONV_TAC NORM_ARITH);;

(* ------------------------------------------------------------------------- *)
(* The hypotheses of the bubble tree step at a point, closed under           *)
(* subsequences, and the combination over a finite set of points.            *)
(* ------------------------------------------------------------------------- *)

let cmc_bthyp = new_definition
 `cmc_bthyp (S:real^K->bool) (G:real^K->real^K^K) e0 E (TT:real^K->bool)
            (eta:num->real) (V:num->real^2->real^K) (x:real^2) rho (b:real^2->real^K) Mb <=>
    cmc_gseq S G e0 E TT eta V /\ &0 < rho /\ cmc_pharm S G b /\ cmc_pmap S b /\
    (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
    (!e. &0 < e
         ==> eventually (\j. cmc_pen G (ball(x,rho)) (V j) <= Mb + e) sequentially)`;;

let CMC_BTHYP_SUBSEQ = prove
 (`!S (G:real^K->real^K^K) e0 E TT (eta:num->real) (V:num->real^2->real^K) x rho b Mb
    (t:num->num).
     cmc_bthyp S G e0 E TT eta V x rho b Mb /\ (!m n. m < n ==> t m < t n)
     ==> cmc_bthyp S G e0 E TT (\j. eta(t j)) (\j. V(t j)) x rho b Mb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_bthyp] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMC_GSEQ_SUBSEQ THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_L2CONV_SUBSEQ THEN ASM_SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] EVENTUALLY_SUBSEQUENCE)) THEN
    DISCH_THEN(MP_TAC o SPEC `t:num->num`) THEN ASM_REWRITE_TAC[o_DEF]]);;

let CMC_BT_FINITE = prove
 (`!S (G:real^K->real^K^K) d e0 E TT rho (b:real^2->real^K) Mb.
     cm_target S G d /\
     (!(eta:num->real) (V:num->real^2->real^K) x.
         cmc_bthyp S G e0 E TT eta V x rho b Mb
         ==> ?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                                 cmc_tconv G (\j. V(t j)) (ball(x,rho)) b p bb)
     ==> !X. FINITE X
             ==> !(eta:num->real) (V:num->real^2->real^K).
                   (!x. x IN X ==> cmc_bthyp S G e0 E TT eta V x rho b Mb)
                   ==> ?(t:num->num) p bb.
                         (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                         !Q:real^K->real^K^K.
                            smooth_map_on (:real^K)
                              ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
                            (!z. transp(Q z) = Q z)
                            ==> ((\j. sum X (\x. cmc_ptr G Q (ball(x,rho)) (V(t j)))) --->
                                 sum X (\x. cmc_ptr G Q (ball(x,rho)) b) +
                                 sum(1..p) (\i. cmc_ptr G Q (:real^2) (bb i))) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BT")) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`\j:num. j`; `0`; `\i:num. b:real^2->real^K`] THEN
    REWRITE_TAC[cmc_bok; SUM_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_RID] THEN
    REWRITE_TAC[REALLIM_CONST] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `X:real^2->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`eta:num->real`; `V:num->real^2->real^K`] THEN
  DISCH_THEN(LABEL_TAC "H") THEN
  USE_THEN "BT" (MP_TAC o SPECL [`eta:num->real`; `V:num->real^2->real^K`; `x:real^2`]) THEN
  ANTS_TAC THENL [USE_THEN "H" (MP_TAC o SPEC `x:real^2`) THEN SIMP_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:num->num` (X_CHOOSE_THEN `p1:num`
    (X_CHOOSE_THEN `bb1:num->real^2->real^K` STRIP_ASSUME_TAC))) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`\j. (eta:num->real) ((t1:num->num) j)`;
                                 `\j. (V:num->real^2->real^K) ((t1:num->num) j)`]) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC CMC_BTHYP_SUBSEQ THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:num->num` (X_CHOOSE_THEN `p2:num`
    (X_CHOOSE_THEN `bb2:num->real^2->real^K` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`p1:num`; `bb1:num->real^2->real^K`; `p2:num`; `bb2:num->real^2->real^K`]
                CMC_BLIST_CONCAT) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `bb:num->real^2->real^K`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PB")))) THEN
  MAP_EVERY EXISTS_TAC [`(t1:num->num) o (t2:num->num)`; `p:num`;
                        `bb:num->real^2->real^K`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `cmc_bok S (G:real^K->real^K^K) TT p1 bb1` THEN
    UNDISCH_TAC `cmc_bok S (G:real^K->real^K^K) TT p2 bb2` THEN
    REWRITE_TAC[cmc_bok] THEN REPEAT DISCH_TAC THEN
    USE_THEN "PB" (MATCH_MP_TAC o BETA_RULE o ISPEC
      `\c:real^2->real^K. cmc_pharm S G c /\ cmc_pmap S c /\ (!x. c x IN TT)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES; o_THM] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a + s) + c1 + c2:real = (a + c1) + (s + c2)`] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [UNDISCH_TAC `cmc_tconv G (\j. (V:num->real^2->real^K) ((t1:num->num) j))
                   (ball(x,rho)) b p1 bb1` THEN
    REWRITE_TAC[cmc_tconv] THEN DISCH_THEN(MP_TAC o SPEC `Q:real^K->real^K^K`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] HMD_REALLIM_SUBSEQ)) THEN
    DISCH_THEN(MP_TAC o SPEC `t2:num->num`) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:real^K->real^K^K` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The limit of the trace integrals over the blown-up ball: base map on the  *)
(* outer part, rescaled limit and its bubbles inside, no neck energy.        *)
(* ------------------------------------------------------------------------- *)

let CMC_GSEQ_TOZERO = prove
 (`!S (G:real^K->real^K^K) d e0 E TT (eta:num->real) (V:num->real^2->real^K).
     cm_target S G d /\ cmc_gseq S G e0 E TT eta V
     ==> (eta ---> &0) sequentially /\
         ((\j. cmc_pen G (:real^2) (V j) - cmc_ptr G G (:real^2) (V j)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_gseq] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `(V:num->real^2->real^K) n`; `(:real^2)`; `(:real^2)`] CMC_DEFECT_MONO) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; SUBSET_REFL] THEN REAL_ARITH_TAC);;

let CMC_PTR_SPLIT2 = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (w:real^2->real^K) A B.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\ cmc_pmap S w /\
     lebesgue_measurable A /\ lebesgue_measurable B /\ B SUBSET A
     ==> cmc_ptr G Q A w = cmc_ptr G Q (A DIFF B) w + cmc_ptr G Q B w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `w:real^2->real^K`; `A DIFF B:real^2->bool`; `B:real^2->bool`]
                CMC_PTR_UNION) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let cmc_neckc = new_definition
 `cmc_neckc (S:real^K->bool) (G:real^K->real^K^K) e0 L e2 Kc <=>
    &0 < L /\ &0 < e2 /\ &0 <= Kc /\
    !(w:real^2->real^K) eta (y:real^2) a b.
       cmc_pmap S w /\ cmc_ah S G e0 eta w /\ &0 < a /\ a * exp L <= b /\
       cmc_pen G (cmc_ann y a b) w <= e2
       ==> cmc_pen G (cmc_ann y a b) w <=
           &2 * cmc_pen G (cmc_ann y a (a * exp L)) w +
           &2 * cmc_pen G (cmc_ann y (b * exp(--L)) b) w +
           Kc * (eta + (cmc_pen G (cmc_ann y a b) w - cmc_ptr G G (cmc_ann y a b) w))`;;

let CMC_NECKC_EXISTS = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0
     ==> ?L e2 Kc. cmc_neckc S G e0 L e2 Kc`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_neckc] THEN
  MATCH_MP_TAC CMC_NECK_ENERGY THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `eL:real`; `C:num->real`] THEN ASM_REWRITE_TAC[]);;

let CMC_LABELS =
  let rec go ls =
    match ls with
      [] -> ASSUME_TAC
    | [l] -> if l = "" then STRIP_ASSUME_TAC else LABEL_TAC l
    | l::t -> CONJUNCTS_THEN2 (if l = "" then ASSUME_TAC else LABEL_TAC l) (go t) in
  go;;

let CMC_ANN_MEASURABLE = prove
 (`!(y:real^2) r1 r2. measurable(cmc_ann y r1 r2) /\ lebesgue_measurable(cmc_ann y r1 r2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN
  MATCH_MP_TAC MEASURABLE_OPEN THEN REWRITE_TAC[CMC_OPEN_ANN] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(y:real^2,r2)` THEN
  REWRITE_TAC[BOUNDED_CBALL; SUBSET; cmc_ann; IN_ELIM_THM; IN_CBALL; dist] THEN
  X_GEN_TAC `z:real^2` THEN MP_TAC(ISPECL [`y:real^2`; `z:real^2`] NORM_SUB) THEN
  REAL_ARITH_TAC);;

let CMC_NORM_GT_SET = prove
 (`!t. {z:real^2 | t < norm z} = (:real^2) DIFF cball(vec 0,t) /\
       open {z:real^2 | t < norm z} /\ lebesgue_measurable {z:real^2 | t < norm z}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{z:real^2 | t < norm z} = (:real^2) DIFF cball(vec 0,t)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN REAL_ARITH_TAC;
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL; LEBESGUE_MEASURABLE_OPEN]]);;

let CMC_BLOWUP_LIMIT = prove
 (`!S (G:real^K->real^K^K) d e0 E TT (eta:num->real) (W:num->real^2->real^K) b om x rho
    eps3 (r:num->real) (y:num->real^2) L e2 Kc X R0 p (bb:num->real^2->real^K).
     cm_target S G d /\ cmc_gseq S G e0 E TT eta W /\ &0 < e0 /\ &0 < rho /\
     cmc_pharm S G b /\ cmc_pmap S b /\ cmc_pharm S G om /\ cmc_pmap S om /\
     (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K W b) /\
     cmc_neckc S G e0 L e2 Kc /\ eps3 <= e2 /\
     (!j. &0 < r j /\ cmc_pen G (ball(x,rho) DIFF cball(y j,r j)) (W j) <= eps3) /\
     (!dl. &0 < dl ==> eventually (\j. r j < dl) sequentially) /\
     (!dl. &0 < dl ==> eventually (\j. dist(y j,x) < dl) sequentially) /\
     (!z. z IN X ==> norm z < R0) /\ &1 <= R0 /\
     (!K. compact K /\ K SUBSET (:real^2) DIFF X
          ==> cmc_l2conv K (\j z. W j (y j + r j % z)) om) /\
     (!R. R0 <= R ==> cmc_tconv G (\j z. W j (y j + r j % z)) (cball(vec 0,R)) om p bb)
     ==> !Q:real^K->real^K^K.
            smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
            (!z. transp(Q z) = Q z)
            ==> ((\j. cmc_ptr G Q (ball(x,rho)) (W j)) --->
                 cmc_ptr G Q (ball(x,rho)) b +
                 (cmc_ptr G Q (:real^2) om + sum(1..p) (\i. cmc_ptr G Q (:real^2) (bb i))))
                sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CMC_LABELS ["";"";"";"";"";"";"";"";"HB";"NC";"";"RY";"P3";"P4";"XN";"";
                         "UL";"TC"]) THEN
  X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  USE_THEN "NC" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_neckc]) THEN
  SUBGOAL_THEN `!j. cmc_pmap S ((W:num->real^2->real^K) j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmc_gseq]; ALL_TAC] THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
                CMC_PTR_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD"))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `E:real`;
                 `TT:real^K->bool`; `eta:num->real`; `W:num->real^2->real^K`]
                CMC_GSEQ_TOZERO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. cmc_pmap S (\z. (W:num->real^2->real^K) j ((y:num->real^2) j + (r:num->real) j % z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(W:num->real^2->real^K) j`; `(y:num->real^2) j`; `(r:num->real) j`;
                   `(:real^2)`] CMC_SIM_PEN_PTR) THEN
    USE_THEN "RY" (MP_TAC o SPEC `j:num`) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC CMC_LIM_APPROX THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `e1 = e / (&8 * (M + &1))` THEN
  SUBGOAL_THEN `&0 < e1 /\ M * e1 <= e / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN
    SUBGOAL_THEN `&0 < M + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M * e / (&8 * (M + &1)) = (e / &8) * (M / (M + &1))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < M + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a * x <= a * &1 ==> a * x <= a`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `b:real^2->real^K`;
                 `e1:real`] CMC_SMALL_BALLS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rb:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `dl = min (rb / &3) (rho / &4)` THEN
  SUBGOAL_THEN `&0 < dl /\ &3 * dl <= rb /\ &3 * dl < rho /\ dl <= rho /\ &3 * dl < &2 * rho`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cmc_pen G (cball(x:real^2,&3 * dl)) (b:real^2->real^K) < e1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `om:real^2->real^K`;
                 `e1:real`] CMC_TAIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Rt:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R = max R0 Rt` THEN
  SUBGOAL_THEN `R0 <= R /\ Rt <= R /\ &1 <= R /\ &0 < R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cmc_pen G ((:real^2) DIFF cball(vec 0,R)) (om:real^2->real^K) < e1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `R:real`) THEN ASM_REWRITE_TAC[CMC_NORM_GT_SET];
    ALL_TAC] THEN
  EXISTS_TAC `\j. cmc_ptr G Q (ball(x,rho) DIFF ball(x,dl)) ((W:num->real^2->real^K) j) +
                  cmc_ptr G Q (cball(vec 0,R))
                    (\z. W j ((y:num->real^2) j + (r:num->real) j % z))` THEN
  EXISTS_TAC `cmc_ptr G Q (ball(x,rho) DIFF ball(x,dl)) (b:real^2->real^K) +
              (cmc_ptr G Q (cball(vec 0,R)) (om:real^2->real^K) +
               sum(1..p) (\i. cmc_ptr G Q (:real^2) ((bb:num->real^2->real^K) i)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                     `W:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                     `dl:real`; `rho:real`; `ball(x:real^2,rho) DIFF ball(x,dl)`]
                    CMC_PUNCT_CONV) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL] THEN
        REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
        MP_TAC(ISPECL [`x:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
        SIMP_TAC[]];
      USE_THEN "TC" (MP_TAC o SPEC `R:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[cmc_tconv]] THEN
      DISCH_THEN(MP_TAC o SPEC `Q:real^K->real^K^K`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `b:real^2->real^K`; `ball(x:real^2,rho)`; `ball(x:real^2,dl)`]
                  CMC_PTR_SPLIT2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; SUBSET_BALL]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `om:real^2->real^K`; `(:real^2)`; `cball(vec 0:real^2,R)`]
                  CMC_PTR_SPLIT2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV; LEBESGUE_MEASURABLE_CBALL; SUBSET_UNIV];
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "BD" (MP_TAC o SPECL [`b:real^2->real^K`; `ball(x:real^2,dl)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]; DISCH_TAC] THEN
    USE_THEN "BD" (MP_TAC o SPECL [`om:real^2->real^K`; `(:real^2) DIFF cball(vec 0,R)`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
                   LEBESGUE_MEASURABLE_CBALL];
      DISCH_TAC] THEN
    SUBGOAL_THEN `cmc_pen G (ball(x:real^2,dl)) (b:real^2->real^K) <= e1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmc_pen G (cball(x:real^2,&3 * dl)) (b:real^2->real^K)` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC CMC_PEN_MONO THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,dl)` THEN
      REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `M * cmc_pen G (ball(x:real^2,dl)) (b:real^2->real^K) <= M * e1 /\
      M * cmc_pen G ((:real^2) DIFF cball(vec 0,R)) (om:real^2->real^K) <= M * e1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `M:real`; `W:num->real^2->real^K`; `x:real^2`; `rho:real`;
                 `r:num->real`; `y:num->real^2`; `R:real`; `dl:real`] CMC_BLOWUP_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "RY" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `E:real`;
                 `TT:real^K->bool`; `eta:num->real`; `W:num->real^2->real^K`; `x:real^2`;
                 `rho:real`; `eps3:real`; `r:num->real`; `y:num->real^2`; `L:real`;
                 `e2:real`; `Kc:real`; `R:real`; `dl:real`] CMC_BLOWUP_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\j. &2 * cmc_pen G (cmc_ann (vec 0) R (R * exp L))
               (\z. (W:num->real^2->real^K) j ((y:num->real^2) j + (r:num->real) j % z)) +
          &2 * cmc_pen G (cmc_ann x (dl * exp(--L)) (&3 * dl)) (W j) +
          Kc * ((eta:num->real) j +
                (cmc_pen G (:real^2) (W j) - cmc_ptr G G (:real^2) (W j)))) --->
     &2 * cmc_pen G (cmc_ann (vec 0) R (R * exp L)) (om:real^2->real^K) +
     &2 * cmc_pen G (cmc_ann x (dl * exp(--L)) (&3 * dl)) (b:real^2->real^K) +
     Kc * (&0 + &0)) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_LMUL THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                     `\j z. (W:num->real^2->real^K) j ((y:num->real^2) j +
                                                       (r:num->real) j % z)`;
                     `om:real^2->real^K`; `cmc_ann (vec 0:real^2) R (R * exp L)`]
                    CMC_L2CONV_PTR) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMC_ANN_MEASURABLE] THEN
        MATCH_MP_TAC CMC_L2CONV_SUBSET THEN
        EXISTS_TAC `cball(vec 0:real^2,R * exp L) DIFF ball(vec 0,R)` THEN
        REWRITE_TAC[CMC_ANN_MEASURABLE] THEN CONJ_TAC THENL
         [USE_THEN "UL" MATCH_MP_TAC THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
          REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL_0] THEN X_GEN_TAC `z:real^2` THEN
          STRIP_TAC THEN DISCH_TAC THEN
          USE_THEN "XN" (MP_TAC o SPEC `z:real^2`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
          REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0;
                      VECTOR_SUB_RZERO] THEN REAL_ARITH_TAC];
        SIMP_TAC[]];
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_LMUL THEN
        MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                       `W:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                       `dl * exp(--L)`; `&3 * dl`;
                       `cmc_ann (x:real^2) (dl * exp(--L)) (&3 * dl)`] CMC_PUNCT_CONV) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMC_ANN_MEASURABLE] THEN
          REPEAT CONJ_TAC THEN
          TRY(MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_EXP_POS_LT] THEN NO_TAC) THEN
          REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM; IN_DIFF; IN_CBALL; IN_BALL; dist] THEN
          X_GEN_TAC `z:real^2` THEN MP_TAC(ISPECL [`x:real^2`; `z:real^2`] NORM_SUB) THEN
          REAL_ARITH_TAC;
          SIMP_TAC[]];
        MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_ADD THEN
        ASM_REWRITE_TAC[ETA_AX]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&5 * e1` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] CMC_REALLIM_EV_LT)) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `cmc_pen G (cmc_ann (vec 0) R (R * exp L)) (om:real^2->real^K) <=
      cmc_pen G ((:real^2) DIFF cball(vec 0,R)) om /\
      cmc_pen G (cmc_ann x (dl * exp(--L)) (&3 * dl)) (b:real^2->real^K) <=
      cmc_pen G (cball(x,&3 * dl)) b`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CMC_PEN_MONO THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_SIMP_TAC[CMC_ANN_MEASURABLE; LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
                   LEBESGUE_MEASURABLE_CBALL] THEN
      REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0; IN_CBALL;
                  VECTOR_SUB_RZERO; dist] THEN
      X_GEN_TAC `z:real^2` THEN TRY(MP_TAC(ISPECL [`x:real^2`; `z:real^2`] NORM_SUB)) THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `M * cmc_pen G (cmc_ann ((y:num->real^2) j) ((r:num->real) j * R) (&2 * dl))
                  ((W:num->real^2->real^K) j) <= M * (&5 * e1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The blow-up step of the bubble tree (mass at least e0).                   *)
(* ------------------------------------------------------------------------- *)

let CMC_REALLIM_EV_GT = prove
 (`!(f:num->real) l c.
     (f ---> l) sequentially /\ c < l ==> eventually (\j. c < f j) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `l - c:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMC_EV_SUBSEQ = prove
 (`!P (t:num->num).
     (!m n. m < n ==> t m < t n) /\ eventually P sequentially
     ==> eventually (\j. P(t j)) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:num->bool`; `t:num->num`] EVENTUALLY_SUBSEQUENCE) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let CMC_FINITE_NORM_BOUND = prove
 (`!X:real^2->bool. FINITE X ==> ?R0. &1 <= R0 /\ !z. z IN X ==> norm z + &1 <= R0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_BOUNDED) THEN REWRITE_TAC[bounded] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `abs B + &1` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMC_BT_PRE = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) b x rho M eps3 e0.
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ &0 < rho /\
     cmc_pharm S G b /\ cmc_pmap S b /\
     (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
     ((\j. cmc_pen G (ball(x,rho)) (V j)) ---> M) sequentially /\
     cmc_pen G (ball(x,&2 * rho)) b <= eps3 / &2 /\ &0 < eps3 /\ eps3 < e0 /\
     e0 <= M - cmc_pen G (ball(x,rho)) b
     ==> eventually (\j. eps3 < cmc_pen G (ball(x,rho)) (V j)) sequentially /\
         (!dl. &0 < dl /\ dl < rho
               ==> eventually (\j. cmc_pen G (ball(x,rho) DIFF cball(x,dl)) (V j) < eps3)
                              sequentially) /\
         (!dl. &0 < dl /\ dl < rho
               ==> eventually (\j. eps3 < cmc_pen G (ball(x,dl)) (V j)) sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cmc_pen G (ball(x:real^2,rho)) (b:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_PEN_POS THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMC_REALLIM_EV_GT THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `dl:real` THEN STRIP_TAC THEN MATCH_MP_TAC CMC_REALLIM_EV_LT THEN
    EXISTS_TAC `cmc_pen G (ball(x:real^2,rho) DIFF cball(x,dl)) (b:real^2->real^K)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                     `V:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                     `dl:real`; `rho:real`; `ball(x:real^2,rho) DIFF cball(x,dl)`]
                    CMC_PUNCT_CONV) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL;
                     LEBESGUE_MEASURABLE_CBALL] THEN
        REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
        MP_TAC(ISPECL [`x:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN
        MP_TAC(ISPECL [`x:real^2`; `dl:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
        SIMP_TAC[]];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `cmc_pen G (ball(x:real^2,&2 * rho)) (b:real^2->real^K)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL;
                   LEBESGUE_MEASURABLE_CBALL] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^2->bool) SUBSET t ==> s DIFF u SUBSET t`) THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `dl:real` THEN STRIP_TAC THEN MATCH_MP_TAC CMC_REALLIM_EV_GT THEN
    EXISTS_TAC `M - cmc_pen G (ball(x:real^2,rho) DIFF ball(x,dl)) (b:real^2->real^K)` THEN
    SUBGOAL_THEN
     `!w:real^2->real^K. cmc_pmap S w
        ==> cmc_pen G (ball(x,dl)) w =
            cmc_pen G (ball(x,rho)) w - cmc_pen G (ball(x,rho) DIFF ball(x,dl)) w`
    (LABEL_TAC "UN") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                     `ball(x:real^2,rho) DIFF ball(x,dl)`; `ball(x:real^2,dl)`]
                    CMC_PEN_UNION) THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL] THEN
      ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(ball(x:real^2,rho) DIFF ball(x,dl)) UNION ball(x,dl) = ball(x,rho)`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`x:real^2`; `dl:real`; `rho:real`] SUBSET_BALL) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `!j. cmc_pen G (ball(x:real^2,dl)) ((V:num->real^2->real^K) j) =
            cmc_pen G (ball(x,rho)) (V j) - cmc_pen G (ball(x,rho) DIFF ball(x,dl)) (V j)`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN USE_THEN "UN" (MP_TAC o SPEC `(V:num->real^2->real^K) j`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                     `V:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                     `dl:real`; `rho:real`; `ball(x:real^2,rho) DIFF ball(x,dl)`]
                    CMC_PUNCT_CONV) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL] THEN
        REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
        MP_TAC(ISPECL [`x:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
        SIMP_TAC[]];
      USE_THEN "UN" (MP_TAC o SPEC `b:real^2->real^K`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= cmc_pen G (ball(x:real^2,dl)) (b:real^2->real^K)` MP_TAC THENL
       [MATCH_MP_TAC CMC_PEN_POS THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
        ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
        ASM_REAL_ARITH_TAC]]]);;

let CMC_BT_BLOWUP = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 E TT L e2 Kc eps3 n.
     CM_REMOVABLE_STATEMENT (:K) /\
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\ closed TT /\
     cmc_neckc S G e0 L e2 Kc /\ &0 < eps3 /\ eps3 <= e2 /\ eps3 < e0 /\
     (!(eta:num->real) (V:num->real^2->real^K) x rho b.
         cmc_bthyp S G e0 E TT eta V x rho b (&n * eps3)
         ==> ?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                                 cmc_tconv G (\j. V(t j)) (ball(x,rho)) b p bb)
     ==> !(eta:num->real) (V:num->real^2->real^K) x rho b M.
            cmc_gseq S G e0 E TT eta V /\ &0 < rho /\ cmc_pharm S G b /\ cmc_pmap S b /\
            (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
            ((\j. cmc_pen G (ball(x,rho)) (V j)) ---> M) sequentially /\
            M <= &(SUC n) * eps3 /\
            cmc_pen G (ball(x,&2 * rho)) b <= eps3 / &2 /\
            e0 <= M - cmc_pen G (ball(x,rho)) b
            ==> ?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                                    cmc_tconv G (\j. V(t j)) (ball(x,rho)) b p bb`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CMC_LABELS ["REM";"";"";"";"";"";"NC";"";"";"";"BT"]) THEN
  MAP_EVERY X_GEN_TAC [`eta:num->real`; `V:num->real^2->real^K`; `x:real^2`; `rho:real`;
                       `b:real^2->real^K`; `M:real`] THEN
  DISCH_THEN(CMC_LABELS ["GS";"";"";"";"HB";"ML";"";"";""]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  USE_THEN "GS" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_gseq]) THEN
  SUBGOAL_THEN `!j. cmc_pmap S ((V:num->real^2->real^K) j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `V:num->real^2->real^K`;
                 `b:real^2->real^K`; `x:real^2`; `rho:real`; `M:real`; `eps3:real`;
                 `e0:real`] CMC_BT_PRE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `V:num->real^2->real^K`;
                 `x:real^2`; `rho:real`; `eps3:real`] CMC_BLOWUP_SCALES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->real` (X_CHOOSE_THEN `y:num->real^2`
    (CMC_LABELS ["RY";"P2";"P3";"P4"]))) THEN
  SUBGOAL_THEN
   `cmc_gseq S G e0 E TT eta
      (\j z. (V:num->real^2->real^K) j ((y:num->real^2) j + (r:num->real) j % z))`
  (LABEL_TAC "GU") THENL
   [MATCH_MP_TAC CMC_GSEQ_SIM THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "RY" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "GU" (STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [cmc_gseq]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`;
                 `\j z. (V:num->real^2->real^K) j ((y:num->real^2) j + (r:num->real) j % z)`;
                 `eta:num->real`; `E:real`; `TT:real^K->bool`] CMC_GLOBAL_PHARM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `\z. (V:num->real^2->real^K) j ((y:num->real^2) j + (r:num->real) j % z)`;
                   `(:real^2)`] CMC_GDIR_PEN) THEN
    ASM_SIMP_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:num->num` (X_CHOOSE_THEN `Uo:real^2->bool`
    (X_CHOOSE_THEN `om:real^2->real^K` (STRIP_ASSUME_TAC o BETA_RULE)))) THEN
  ABBREV_TAC `X = (:real^2) DIFF Uo` THEN
  SUBGOAL_THEN `!z:real^2. z IN Uo <=> ~(z IN X)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^2->bool` CMC_FINITE_SEPARATED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEP"))) THEN
  ABBREV_TAC `s = min (&1 / &4) (e1 / &4)` THEN
  SUBGOAL_THEN `&0 < s /\ s <= &1 / &4 /\ &4 * s <= e1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^2->bool` CMC_FINITE_NORM_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "XN"))) THEN
  SUBGOAL_THEN
   `!q. q IN X
        ==> cmc_bthyp S G e0 E TT (\j. (eta:num->real) ((t1:num->num) j))
              (\j z. (V:num->real^2->real^K) (t1 j) ((y:num->real^2) (t1 j) +
                                                       (r:num->real) (t1 j) % z))
              q s om (&n * eps3)`
  (LABEL_TAC "BH") THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN REWRITE_TAC[cmc_bthyp] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`; `E:real`;
                     `TT:real^K->bool`; `eta:num->real`;
                     `\j z. (V:num->real^2->real^K) j ((y:num->real^2) j +
                                                       (r:num->real) j % z)`;
                     `t1:num->num`] CMC_GSEQ_SUBSEQ) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `K:real^2->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cmc_l2conv"))
            (concl th) &&
        can (find_term ((=) `Uo:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^2` THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^2) IN ball(q,&2 * s) DELETE q` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_DELETE; IN_BALL] THEN STRIP_TAC THEN
      USE_THEN "SEP" (MP_TAC o SPECL [`q:real^2`; `w:real^2`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `dist(q:real^2,w) < &2 * s` THEN REWRITE_TAC[dist] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `e':real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\j. cmc_pen G (ball(q:real^2,s))
                            (\z. (V:num->real^2->real^K) j ((y:num->real^2) j +
                                                            (r:num->real) j % z)) <=
                          &n * eps3 + e'`; `t1:num->num`] CMC_EV_SUBSEQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `V:num->real^2->real^K`; `x:real^2`; `rho:real`; `eps3:real`;
                     `r:num->real`; `y:num->real^2`; `q:real^2`; `s:real`]
                    CMC_BLOWUP_MASS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`\j. cmc_pen G (ball(x:real^2,rho)) ((V:num->real^2->real^K) j)`;
                     `M:real`; `M + e'`] CMC_REALLIM_EV_LT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `M <= &(SUC n) * eps3` THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `E:real`;
                 `TT:real^K->bool`; `s:real`; `om:real^2->real^K`; `&n * eps3`]
                CMC_BT_FINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "BT" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `X:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`\j. (eta:num->real) ((t1:num->num) j)`;
    `\j z. (V:num->real^2->real^K) ((t1:num->num) j) ((y:num->real^2) (t1 j) +
                                            (r:num->real) (t1 j) % z)`]) THEN
  ANTS_TAC THENL [USE_THEN "BH" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:num->num` (X_CHOOSE_THEN `p2:num`
    (X_CHOOSE_THEN `bb2:num->real^2->real^K` (CMC_LABELS ["";"";"SC"])))) THEN
  SUBGOAL_THEN
   `!K. compact K /\ K SUBSET (:real^2) DIFF X
        ==> cmc_l2conv K (\j z. (V:num->real^2->real^K) ((t1:num->num) ((t2:num->num) j))
                                  ((y:num->real^2) (t1 (t2 j)) + (r:num->real) (t1 (t2 j)) % z))
                       om`
  (LABEL_TAC "UL") THENL
   [X_GEN_TAC `K:real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:real^2->bool`;
                   `\j z. (V:num->real^2->real^K) ((t1:num->num) j)
                            ((y:num->real^2) (t1 j) + (r:num->real) (t1 j) % z)`;
                   `om:real^2->real^K`; `t2:num->num`] CMC_L2CONV_SUBSEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cmc_l2conv")) (concl th) &&
      can (find_term ((=) `Uo:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[SUBSET] THEN
    UNDISCH_TAC `K SUBSET (:real^2) DIFF X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!R. R0 <= R
        ==> cmc_tconv G (\j z. (V:num->real^2->real^K) ((t1:num->num) ((t2:num->num) j))
                                 ((y:num->real^2) (t1 (t2 j)) + (r:num->real) (t1 (t2 j)) % z))
                      (cball(vec 0,R)) om p2 bb2`
  (LABEL_TAC "TC") THENL
   [X_GEN_TAC `R:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMC_COMBINE THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `X:real^2->bool`; `s:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
      USE_THEN "XN" (MP_TAC o SPEC `q:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL_0] THEN X_GEN_TAC `w:real^2` THEN
      UNDISCH_TAC `norm(q:real^2) + &1 <= R0` THEN UNDISCH_TAC `R0 <= R` THEN
      UNDISCH_TAC `s <= &1 / &4` THEN CONV_TAC NORM_ARITH;
      MAP_EVERY X_GEN_TAC [`q:real^2`; `q':real^2`] THEN STRIP_TAC THEN
      USE_THEN "SEP" (MP_TAC o SPECL [`q:real^2`; `q':real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
      X_GEN_TAC `w:real^2` THEN
      UNDISCH_TAC `e1 <= norm(q - q':real^2)` THEN UNDISCH_TAC `&4 * s <= e1` THEN
      CONV_TAC NORM_ARITH;
      USE_THEN "SC" (fun th -> ACCEPT_TAC(BETA_RULE th))];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (t1:num->num) ((t2:num->num) m) < t1 (t2 n)`
  (LABEL_TAC "SUB") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!m n. m < n ==> (t1:num->num) m < t1 n` THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `!m n. m < n ==> (t2:num->num) m < t2 n` THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `E:real`;
                 `TT:real^K->bool`;
                 `\j. (eta:num->real) ((t1:num->num) ((t2:num->num) j))`;
                 `\j. (V:num->real^2->real^K) ((t1:num->num) ((t2:num->num) j))`;
                 `b:real^2->real^K`; `om:real^2->real^K`; `x:real^2`; `rho:real`;
                 `eps3:real`;
                 `\j. (r:num->real) ((t1:num->num) ((t2:num->num) j))`;
                 `\j. (y:num->real^2) ((t1:num->num) ((t2:num->num) j))`;
                 `L:real`; `e2:real`; `Kc:real`; `X:real^2->bool`; `R0:real`; `p2:num`;
                 `bb2:num->real^2->real^K`] CMC_BLOWUP_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`; `E:real`;
                     `TT:real^K->bool`; `eta:num->real`; `V:num->real^2->real^K`;
                     `\j. (t1:num->num) ((t2:num->num) j)`] CMC_GSEQ_SUBSEQ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `K:real^2->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`K:real^2->bool`; `V:num->real^2->real^K`; `b:real^2->real^K`;
                     `\j. (t1:num->num) ((t2:num->num) j)`] CMC_L2CONV_SUBSEQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "HB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      X_GEN_TAC `dl:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\j. (r:num->real) j < dl`; `\j. (t1:num->num) ((t2:num->num) j)`]
                    CMC_EV_SUBSEQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "P3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `dl:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\j. dist((y:num->real^2) j,x) < dl`;
                     `\j. (t1:num->num) ((t2:num->num) j)`] CMC_EV_SUBSEQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "P4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      USE_THEN "XN" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`1`; `\i:num. (om:real^2->real^K)`; `p2:num`; `bb2:num->real^2->real^K`]
                CMC_BLIST_CONCAT) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `bb:num->real^2->real^K`
    (CONJUNCTS_THEN2 (LABEL_TAC "SUMC") (LABEL_TAC "PB")))) THEN
  MAP_EVERY EXISTS_TAC [`\j. (t1:num->num) ((t2:num->num) j)`; `p:num`;
                        `bb:num->real^2->real^K`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[] THEN USE_THEN "SUB" ACCEPT_TAC;
    REWRITE_TAC[cmc_bok] THEN
    USE_THEN "PB" (MATCH_MP_TAC o BETA_RULE o ISPEC
      `\c:real^2->real^K. cmc_pharm S G c /\ cmc_pmap S c /\ (!x. c x IN TT)`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `cmc_bok S (G:real^K->real^K^K) TT p2 bb2` THEN REWRITE_TAC[cmc_bok]];
    REWRITE_TAC[cmc_tconv] THEN X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
    USE_THEN "SUMC" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SUM_SING_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:real^K->real^K^K` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `ball(x:real^2,rho)`)) (concl th) &&
      can (find_term ((=) `om:real^2->real^K`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The bubble tree at a point by induction on the mass bound n eps3.         *)
(* ------------------------------------------------------------------------- *)

let CMC_BT_EXTRACT = prove
 (`!S (G:real^K->real^K^K) d e0 E TT (eta:num->real) (V:num->real^2->real^K) x rho b Mb.
     cm_target S G d /\ cmc_bthyp S G e0 E TT eta V x rho b Mb
     ==> ?(t:num->num) M. (!m n. m < n ==> t m < t n) /\
                          ((\j. cmc_pen G (ball(x,rho)) (V(t j))) ---> M) sequentially /\
                          M <= Mb /\
                          cmc_bthyp S G e0 E TT (\j. eta(t j)) (\j. V(t j)) x rho b Mb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_bthyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_gseq]) THEN
  MP_TAC(ISPECL [`\j. cmc_pen G (ball(x:real^2,rho)) ((V:num->real^2->real^K) j)`; `E:real`]
                CMC_BOUNDED_SUBSEQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMC_PEN_POS THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmc_pen G (:real^2) ((V:num->real^2->real^K) j)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMC_PEN_MONO THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_UNIV; SUBSET_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`t:num->num`; `M:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cmc_bthyp S G e0 E TT (\j. (eta:num->real) ((t:num->num) j))
                  (\j. (V:num->real^2->real^K) (t j)) x rho b Mb` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_BTHYP_SUBSEQ THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `!e. &0 < e ==> M <= Mb + e` MP_TAC THENL
   [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `(M - Mb) / &2`) THEN REAL_ARITH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\j. cmc_pen G (ball(x:real^2,rho)) ((V:num->real^2->real^K) ((t:num->num) j))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  UNDISCH_TAC `cmc_bthyp S G e0 E TT (\j. (eta:num->real) ((t:num->num) j))
                 (\j. (V:num->real^2->real^K) (t j)) x rho b Mb` THEN
  REWRITE_TAC[cmc_bthyp] THEN DISCH_THEN(MP_TAC o SPEC `e:real` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[]);;

let CMC_BT_SMALL = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 E TT (eta:num->real)
    (V:num->real^2->real^K) x rho b Mb M.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\
     cmc_bthyp S G e0 E TT eta V x rho b Mb /\
     ((\j. cmc_pen G (ball(x,rho)) (V j)) ---> M) sequentially /\
     M - cmc_pen G (ball(x,rho)) b < e0
     ==> ?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                             cmc_tconv G (\j. V(t j)) (ball(x,rho)) b p bb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_bthyp]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`; `E:real`; `TT:real^K->bool`; `eta:num->real`;
                 `V:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                 `M:real`] CMC_BT_NOCONC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t:num->num`; `0`; `\i:num. (b:real^2->real^K)`] THEN
  ASM_REWRITE_TAC[cmc_bok] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CMC_TCONV_L2 THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cmc_gseq]);;

let CMC_PEN_SUBBALL_CONV = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) b x rho rho1 M.
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ cmc_pharm S G b /\ cmc_pmap S b /\
     (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
     ((\j. cmc_pen G (ball(x,rho)) (V j)) ---> M) sequentially /\
     &0 < rho1 /\ rho1 <= rho
     ==> ((\j. cmc_pen G (ball(x,rho1)) (V j)) --->
          M - cmc_pen G (ball(x,rho) DIFF ball(x,rho1)) b) sequentially /\
         cmc_pen G (ball(x,rho)) b =
         cmc_pen G (ball(x,rho) DIFF ball(x,rho1)) b + cmc_pen G (ball(x,rho1)) b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `!w:real^2->real^K. cmc_pmap S w
        ==> cmc_pen G (ball(x,rho)) w =
            cmc_pen G (ball(x,rho) DIFF ball(x,rho1)) w + cmc_pen G (ball(x,rho1)) w`
  (LABEL_TAC "UN") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                   `ball(x:real^2,rho) DIFF ball(x,rho1)`; `ball(x:real^2,rho1)`]
                  CMC_PEN_UNION) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL] THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(ball(x:real^2,rho) DIFF ball(x,rho1)) UNION ball(x,rho1) = ball(x,rho)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`x:real^2`; `rho1:real`; `rho:real`] SUBSET_BALL) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC; USE_THEN "UN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!j. cmc_pen G (ball(x:real^2,rho1)) ((V:num->real^2->real^K) j) =
        cmc_pen G (ball(x,rho)) (V j) - cmc_pen G (ball(x,rho) DIFF ball(x,rho1)) (V j)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN USE_THEN "UN" (MP_TAC o SPEC `(V:num->real^2->real^K) j`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                 `V:num->real^2->real^K`; `b:real^2->real^K`; `x:real^2`; `rho:real`;
                 `rho1:real`; `rho:real`; `ball(x:real^2,rho) DIFF ball(x,rho1)`]
                CMC_PUNCT_CONV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_BALL] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MP_TAC(ISPECL [`x:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
    SIMP_TAC[]]);;

let CMC_BT_LARGE = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 E TT L e2 Kc eps3 n.
     CM_REMOVABLE_STATEMENT (:K) /\
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\ closed TT /\
     cmc_neckc S G e0 L e2 Kc /\ &0 < eps3 /\ eps3 <= e2 /\ eps3 < e0 /\
     (!(eta:num->real) (V:num->real^2->real^K) x rho b.
         cmc_bthyp S G e0 E TT eta V x rho b (&n * eps3)
         ==> ?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                                 cmc_tconv G (\j. V(t j)) (ball(x,rho)) b p bb)
     ==> !(eta:num->real) (V:num->real^2->real^K) x rho b M.
            cmc_gseq S G e0 E TT eta V /\ &0 < rho /\ cmc_pharm S G b /\ cmc_pmap S b /\
            (!K. compact K /\ K SUBSET ball(x,&2 * rho) DELETE x ==> cmc_l2conv K V b) /\
            ((\j. cmc_pen G (ball(x,rho)) (V j)) ---> M) sequentially /\
            M <= &(SUC n) * eps3 /\ e0 <= M - cmc_pen G (ball(x,rho)) b
            ==> ?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                                    cmc_tconv G (\j. V(t j)) (ball(x,rho)) b p bb`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "CTX") THEN
  MAP_EVERY X_GEN_TAC [`eta:num->real`; `V:num->real^2->real^K`; `x:real^2`; `rho:real`;
                       `b:real^2->real^K`; `M:real`] THEN
  DISCH_THEN(CMC_LABELS ["GS";"";"";"";"HB";"ML";"";""]) THEN
  USE_THEN "CTX" (CMC_LABELS ["";"";"";"";"";"";"";"";"";""; "BT"]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `!j. cmc_pmap S ((V:num->real^2->real^K) j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmc_gseq]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `b:real^2->real^K`;
                 `eps3 / &2`] CMC_SMALL_BALLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho1 = min rho (rb / &2)` THEN
  SUBGOAL_THEN `&0 < rho1 /\ rho1 <= rho /\ &2 * rho1 <= rb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `V:num->real^2->real^K`;
                 `b:real^2->real^K`; `x:real^2`; `rho:real`; `rho1:real`; `M:real`]
                CMC_PEN_SUBBALL_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= cmc_pen G (ball(x:real^2,rho) DIFF ball(x,rho1)) (b:real^2->real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_PEN_POS THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`; `E:real`; `TT:real^K->bool`; `L:real`; `e2:real`; `Kc:real`;
                 `eps3:real`; `n:num`] CMC_BT_BLOWUP) THEN
  USE_THEN "CTX" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(MP_TAC o SPECL [`eta:num->real`; `V:num->real^2->real^K`; `x:real^2`;
    `rho1:real`; `b:real^2->real^K`;
    `M - cmc_pen G (ball(x:real^2,rho) DIFF ball(x,rho1)) (b:real^2->real^K)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `K:real^2->bool` THEN STRIP_TAC THEN USE_THEN "HB" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^2,&2 * rho1) DELETE x` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DELETE (x:real^2) SUBSET t DELETE x`) THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmc_pen G (cball(x:real^2,rb)) (b:real^2->real^K)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
        ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,&2 * rho1)` THEN
        REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_CBALL THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `p:num`
    (X_CHOOSE_THEN `bb:num->real^2->real^K` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t:num->num`; `p:num`; `bb:num->real^2->real^K`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMC_TCONV_SHRINK THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `rho1:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_L2CONV_SUBSEQ THEN
  ASM_SIMP_TAC[]);;

let CMC_BT = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 E TT L e2 Kc eps3.
     CM_REMOVABLE_STATEMENT (:K) /\
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\ closed TT /\
     cmc_neckc S G e0 L e2 Kc /\ &0 < eps3 /\ eps3 <= e2 /\ eps3 < e0
     ==> !n (eta:num->real) (V:num->real^2->real^K) x rho b.
            cmc_bthyp S G e0 E TT eta V x rho b (&n * eps3)
            ==> ?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                                    cmc_tconv G (\j. V(t j)) (ball(x,rho)) b p bb`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "CTX") THEN
  USE_THEN "CTX" STRIP_ASSUME_TAC THEN
  INDUCT_TAC THEN
  MAP_EVERY X_GEN_TAC [`eta:num->real`; `V:num->real^2->real^K`; `x:real^2`; `rho:real`;
                       `b:real^2->real^K`] THEN
  DISCH_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `E:real`;
                   `TT:real^K->bool`; `eta:num->real`; `V:num->real^2->real^K`; `x:real^2`;
                   `rho:real`; `b:real^2->real^K`; `&0 * eps3`] CMC_BT_EXTRACT);
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `E:real`;
                   `TT:real^K->bool`; `eta:num->real`; `V:num->real^2->real^K`; `x:real^2`;
                   `rho:real`; `b:real^2->real^K`; `&(SUC n) * eps3`] CMC_BT_EXTRACT)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:num->num` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN `&0 <= cmc_pen G (ball(x:real^2,rho)) (b:real^2->real^K)` ASSUME_TAC THENL
    [MATCH_MP_TAC CMC_PEN_POS THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
     ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN ASM_MESON_TAC[cmc_bthyp];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `?(t:num->num) p bb. (!m n. m < n ==> t m < t n) /\ cmc_bok S G TT p bb /\
                         cmc_tconv G (\j. (V:num->real^2->real^K) ((t0:num->num) (t j)))
                                   (ball(x,rho)) b p bb`
   MP_TAC THENL
    [ALL_TAC;
     DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `p:num`
       (X_CHOOSE_THEN `bb:num->real^2->real^K` STRIP_ASSUME_TAC))) THEN
     MAP_EVERY EXISTS_TAC [`\j. (t0:num->num) ((t:num->num) j)`; `p:num`;
                           `bb:num->real^2->real^K`] THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]) THEN
  ASM_CASES_TAC `M - cmc_pen G (ball(x:real^2,rho)) (b:real^2->real^K) < e0` THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                   `C:num->real`; `e0:real`; `E:real`; `TT:real^K->bool`;
                   `\j. (eta:num->real) ((t0:num->num) j)`;
                   `\j. (V:num->real^2->real^K) ((t0:num->num) j)`; `x:real^2`; `rho:real`;
                   `b:real^2->real^K`] CMC_BT_SMALL) THEN
    DISCH_THEN(MP_TAC o SPECL [`&0 * eps3`; `M:real`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    UNDISCH_TAC `cmc_bthyp S G e0 E TT (\j. (eta:num->real) ((t0:num->num) j))
                   (\j. (V:num->real^2->real^K) (t0 j)) x rho b (&0 * eps3)` THEN
    REWRITE_TAC[cmc_bthyp] THEN SIMP_TAC[];
    ALL_TAC;
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                   `C:num->real`; `e0:real`; `E:real`; `TT:real^K->bool`;
                   `\j. (eta:num->real) ((t0:num->num) j)`;
                   `\j. (V:num->real^2->real^K) ((t0:num->num) j)`; `x:real^2`; `rho:real`;
                   `b:real^2->real^K`] CMC_BT_SMALL) THEN
    DISCH_THEN(MP_TAC o SPECL [`&(SUC n) * eps3`; `M:real`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    UNDISCH_TAC `cmc_bthyp S G e0 E TT (\j. (eta:num->real) ((t0:num->num) j))
                   (\j. (V:num->real^2->real^K) (t0 j)) x rho b (&(SUC n) * eps3)` THEN
    REWRITE_TAC[cmc_bthyp] THEN SIMP_TAC[];
    ALL_TAC] THENL
   [UNDISCH_TAC `M <= &0 * eps3` THEN UNDISCH_TAC `~(M - cmc_pen G (ball(x:real^2,rho))
                                                     (b:real^2->real^K) < e0)` THEN
    UNDISCH_TAC `&0 < e0` THEN
    UNDISCH_TAC `&0 <= cmc_pen G (ball(x:real^2,rho)) (b:real^2->real^K)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`; `E:real`; `TT:real^K->bool`; `L:real`; `e2:real`; `Kc:real`;
                 `eps3:real`; `n:num`] CMC_BT_LARGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`\j. (eta:num->real) ((t0:num->num) j)`;
    `\j. (V:num->real^2->real^K) ((t0:num->num) j)`; `x:real^2`; `rho:real`;
    `b:real^2->real^K`; `M:real`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  UNDISCH_TAC `cmc_bthyp S G e0 E TT (\j. (eta:num->real) ((t0:num->num) j))
                 (\j. (V:num->real^2->real^K) (t0 j)) x rho b (&(SUC n) * eps3)` THEN
  REWRITE_TAC[cmc_bthyp] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The planar bubble theorem CMC_PLANAR_BUBBLES_STATEMENT.                   *)
(* ------------------------------------------------------------------------- *)

let CMC_TOP_LIMIT = prove
 (`!S (G:real^K->real^K^K) d (W:num->real^2->real^K) b0 R0 p (bb:num->real^2->real^K).
     cm_target S G d /\ (!j. cmc_pmap S (W j)) /\ cmc_pharm S G b0 /\ cmc_pmap S b0 /\
     (!e. &0 < e
          ==> ?r. &0 < r /\
                  eventually (\j. cmc_pen G {y:real^2 | r < norm y} (W j) < e) sequentially) /\
     (!R. R0 <= R ==> cmc_tconv G W (cball(vec 0,R)) b0 p bb)
     ==> !Q:real^K->real^K^K.
            smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
            (!z. transp(Q z) = Q z)
            ==> ((\j. cmc_ptr G Q (:real^2) (W j)) --->
                 cmc_ptr G Q (:real^2) b0 + sum(1..p) (\i. cmc_ptr G Q (:real^2) (bb i)))
                sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CMC_LABELS ["";"";"";"";"TI";"TC"]) THEN
  X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
                CMC_PTR_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD"))) THEN
  MATCH_MP_TAC CMC_LIM_APPROX THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `e1 = e / (&4 * (M + &1))` THEN
  SUBGOAL_THEN `&0 < e1 /\ M * e1 <= e / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN
    SUBGOAL_THEN `&0 < M + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M * e / (&4 * (M + &1)) = (e / &4) * (M / (M + &1))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < M + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a * x <= a * &1 ==> a * x <= a`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "TI" (MP_TAC o SPEC `e1:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[CMC_NORM_GT_SET]] THEN
  DISCH_THEN(X_CHOOSE_THEN `rt:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `b0:real^2->real^K`;
                 `e1:real`] CMC_TAIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Rt:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R = max R0 (max rt Rt)` THEN
  SUBGOAL_THEN `R0 <= R /\ rt <= R /\ Rt <= R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cmc_pen G ((:real^2) DIFF cball(vec 0,R)) (b0:real^2->real^K) < e1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `R:real`) THEN ASM_REWRITE_TAC[CMC_NORM_GT_SET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2->real^K. cmc_pmap S w
                  ==> cmc_ptr G Q (:real^2) w =
                      cmc_ptr G Q ((:real^2) DIFF cball(vec 0,R)) w +
                      cmc_ptr G Q (cball(vec 0,R)) w`
  (LABEL_TAC "SP") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_PTR_SPLIT2 THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; LEBESGUE_MEASURABLE_CBALL; SUBSET_UNIV];
    ALL_TAC] THEN
  EXISTS_TAC `\j. cmc_ptr G Q (cball(vec 0,R)) ((W:num->real^2->real^K) j)` THEN
  EXISTS_TAC `cmc_ptr G Q (cball(vec 0,R)) (b0:real^2->real^K) +
              sum(1..p) (\i. cmc_ptr G Q (:real^2) ((bb:num->real^2->real^K) i))` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "TC" (MP_TAC o SPEC `R:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[cmc_tconv]] THEN
    DISCH_THEN(MP_TAC o SPEC `Q:real^K->real^K^K`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    USE_THEN "SP" (MP_TAC o SPEC `b0:real^2->real^K`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "BD" (MP_TAC o SPECL [`b0:real^2->real^K`; `(:real^2) DIFF cball(vec 0,R)`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
                   LEBESGUE_MEASURABLE_CBALL];
      DISCH_TAC] THEN
    SUBGOAL_THEN `M * cmc_pen G ((:real^2) DIFF cball(vec 0,R)) (b0:real^2->real^K) <= M * e1`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    can (find_term ((=) `rt:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "eventually")) (concl th))) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "SP" (MP_TAC o SPEC `(W:num->real^2->real^K) j`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "BD" (MP_TAC o SPECL [`(W:num->real^2->real^K) j`;
                                 `(:real^2) DIFF cball(vec 0,R)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
                 LEBESGUE_MEASURABLE_CBALL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `cmc_pen G ((:real^2) DIFF cball(vec 0,R)) ((W:num->real^2->real^K) j) <=
    cmc_pen G ((:real^2) DIFF cball(vec 0,rt)) (W j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
                 LEBESGUE_MEASURABLE_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `M * cmc_pen G ((:real^2) DIFF cball(vec 0,R)) ((W:num->real^2->real^K) j) <= M * e1`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMC_PLANAR_BUBBLES = prove
 (`CM_EPS_REG_STATEMENT (:K) /\ CM_REPLACEMENT_STATEMENT (:K) /\
   CM_REMOVABLE_STATEMENT (:K)
   ==> CMC_PLANAR_BUBBLES_STATEMENT (:K)`,
  DISCH_THEN(CMC_LABELS ["EPS";"REP";"REM"]) THEN
  REWRITE_TAC[CMC_PLANAR_BUBBLES_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMC_REGC_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eL:real` (X_CHOOSE_TAC `C:num->real`)) THEN
  EXISTS_TAC `eL:real` THEN CONJ_TAC THENL [ASM_MESON_TAC[cmc_regc]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e0:real`; `E:real`; `w:num->real^2->real^K`; `eta:num->real`;
                       `TT:real^K->bool`] THEN
  DISCH_THEN(CMC_LABELS ["";"";"";"";"";"WS";"DEF";"TI"]) THEN
  SUBGOAL_THEN
   `!j. cmc_pmap S ((w:num->real^2->real^K) j) /\
        cmc_pen G (:real^2) (w j) = wan_gdir (:real^2) G (w j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "WS" (MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMC_GDIR_PEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmc_gseq S G e0 E TT eta (w:num->real^2->real^K)` (LABEL_TAC "GS") THENL
   [REWRITE_TAC[cmc_gseq] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "WS" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "DEF" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`] CMC_NECKC_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN `e2:real` (X_CHOOSE_TAC `Kc:real`))) THEN
  SUBGOAL_THEN `&0 < e2` ASSUME_TAC THENL [ASM_MESON_TAC[cmc_neckc]; ALL_TAC] THEN
  ABBREV_TAC `eps3 = min e2 (e0 / &2)` THEN
  SUBGOAL_THEN `&0 < eps3 /\ eps3 <= e2 /\ eps3 < e0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`; `E:real`; `TT:real^K->bool`; `L:real`; `e2:real`; `Kc:real`;
                 `eps3:real`] CMC_BT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_THEN(LABEL_TAC "BT")] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`; `w:num->real^2->real^K`; `eta:num->real`; `E:real`;
                 `TT:real^K->bool`] CMC_GLOBAL_PHARM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN USE_THEN "WS" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:num->num` (X_CHOOSE_THEN `Uo:real^2->bool`
    (X_CHOOSE_THEN `b0:real^2->real^K` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `X = (:real^2) DIFF Uo` THEN
  SUBGOAL_THEN `!z:real^2. z IN Uo <=> ~(z IN X)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^2->bool` CMC_FINITE_SEPARATED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEP"))) THEN
  ABBREV_TAC `s = min (&1) (e1 / &4)` THEN
  SUBGOAL_THEN `&0 < s /\ s <= &1 /\ &4 * s <= e1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^2->bool` CMC_FINITE_NORM_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "XN"))) THEN
  MP_TAC(SPEC `E / eps3` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `E <= &n * eps3` ASSUME_TAC THENL
   [UNDISCH_TAC `E / eps3 <= &n` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN X
        ==> cmc_bthyp S G e0 E TT (\j. (eta:num->real) ((t1:num->num) j))
              (\j. (w:num->real^2->real^K) (t1 j)) q s b0 (&n * eps3)`
  (LABEL_TAC "BH") THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN REWRITE_TAC[cmc_bthyp] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMC_GSEQ_SUBSEQ THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `K:real^2->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cmc_l2conv"))
            (concl th) &&
        can (find_term ((=) `Uo:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^2` THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(v:real^2) IN ball(q,&2 * s) DELETE q` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_DELETE; IN_BALL] THEN STRIP_TAC THEN
      USE_THEN "SEP" (MP_TAC o SPECL [`q:real^2`; `v:real^2`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `dist(q:real^2,v) < &2 * s` THEN REWRITE_TAC[dist] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `e':real` THEN DISCH_TAC THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
      X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmc_pen G (:real^2) ((w:num->real^2->real^K) ((t1:num->num) j))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
        ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_UNIV; SUBSET_UNIV];
        USE_THEN "WS" (STRIP_ASSUME_TAC o SPEC `(t1:num->num) j`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `E:real`;
                 `TT:real^K->bool`; `s:real`; `b0:real^2->real^K`; `&n * eps3`]
                CMC_BT_FINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "BT" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `X:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`\j. (eta:num->real) ((t1:num->num) j)`;
                             `\j. (w:num->real^2->real^K) ((t1:num->num) j)`]) THEN
  ANTS_TAC THENL [USE_THEN "BH" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:num->num` (X_CHOOSE_THEN `p:num`
    (X_CHOOSE_THEN `bb:num->real^2->real^K` (CMC_LABELS ["";"";"SC"])))) THEN
  SUBGOAL_THEN `!m n. m < n ==> (t1:num->num) ((t2:num->num) m) < t1 (t2 n)`
  (LABEL_TAC "SUB") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!m n. m < n ==> (t1:num->num) m < t1 n` THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `!m n. m < n ==> (t2:num->num) m < t2 n` THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!R. R0 <= R
        ==> cmc_tconv G (\j. (w:num->real^2->real^K) ((t1:num->num) ((t2:num->num) j)))
                      (cball(vec 0,R)) b0 p bb`
  (LABEL_TAC "TC") THENL
   [X_GEN_TAC `R:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMC_COMBINE THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `X:real^2->bool`; `s:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `K:real^2->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`K:real^2->bool`; `\j. (w:num->real^2->real^K) ((t1:num->num) j)`;
                     `b0:real^2->real^K`; `t2:num->num`] CMC_L2CONV_SUBSEQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cmc_l2conv"))
            (concl th) &&
        can (find_term ((=) `Uo:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[SUBSET] THEN
      UNDISCH_TAC `K SUBSET (:real^2) DIFF X` THEN SET_TAC[];
      X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
      USE_THEN "XN" (MP_TAC o SPEC `q:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL_0] THEN X_GEN_TAC `v:real^2` THEN
      UNDISCH_TAC `norm(q:real^2) + &1 <= R0` THEN UNDISCH_TAC `R0 <= R` THEN
      UNDISCH_TAC `s <= &1` THEN CONV_TAC NORM_ARITH;
      MAP_EVERY X_GEN_TAC [`q:real^2`; `q':real^2`] THEN STRIP_TAC THEN
      USE_THEN "SEP" (MP_TAC o SPECL [`q:real^2`; `q':real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
      X_GEN_TAC `v:real^2` THEN
      UNDISCH_TAC `e1 <= norm(q - q':real^2)` THEN UNDISCH_TAC `&4 * s <= e1` THEN
      CONV_TAC NORM_ARITH;
      USE_THEN "SC" (fun th -> ACCEPT_TAC(BETA_RULE th))];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\j. (w:num->real^2->real^K) ((t1:num->num) ((t2:num->num) j))`;
                 `b0:real^2->real^K`; `R0:real`; `p:num`; `bb:num->real^2->real^K`]
                CMC_TOP_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "TI" (MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `rt:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\j. cmc_pen G {y:real^2 | rt < norm y} ((w:num->real^2->real^K) j) < e`;
                   `\j. (t1:num->num) ((t2:num->num) j)`] CMC_EV_SUBSEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\j. (t1:num->num) ((t2:num->num) j)`; `p:num`;
    `\i. if i = 0 then (b0:real^2->real^K) else (bb:num->real^2->real^K) i`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "SUB" ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cmc_bok S (G:real^K->real^K^K) TT p bb` THEN REWRITE_TAC[cmc_bok] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
    SUBGOAL_THEN
     `sum(1..p) (\i. cmc_ptr G Q (:real^2)
                       (if i = 0 then (b0:real^2->real^K) else (bb:num->real^2->real^K) i)) =
      sum(1..p) (\i. cmc_ptr G Q (:real^2) (bb i))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:real^K->real^K^K` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `b0:real^2->real^K`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sum")) (concl th) &&
      not (can (find_term ((=) `X:real^2->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[]]);;

