(* ========================================================================= *)
(* Unit pc_cmr_l339 (a unit of the replacement chain of pc_cm_replacement):  *)
(* the maximal improvement e(t) of CM (3.33), the uniform continuity of      *)
(* replacement energies (CM (3.36)), CM Lemma 3.34 and CM Lemma 3.39.        *)
(*                                                                           *)
(* The improvement cmr_e, its basic facts, and the splitting                 *)
(* of a sequential replacement into two consecutive blocks.                  *)
(* ========================================================================= *)

needs "src/pc_cmr_l312.ml";;

prioritize_real();;
type_invention_error := true;;

(* The set of improvements of u by replacement on the half caps of a        *)
(* disjoint family of energy at most eps, and its supremum (CM (3.33)).      *)

let cmr_eset = new_definition
 `cmr_eset S (G:real^K->real^K^K) eps (u:real^3->real^K) =
    {x:real | ?n (Q:num->real^3^3) (c:num->real^2) (r:num->real).
                cmr_dfam n Q c r /\ cmr_sen_on G u (cmr_fop n Q c r) <= eps /\
                x = cm_sen G u - cm_sen G (cmr_repn S G n Q c (\j. r j / &2) u)}`;;

let cmr_e = new_definition
 `cmr_e S (G:real^K->real^K^K) eps (u:real^3->real^K) = sup(cmr_eset S G eps u)`;;

(* The improvement on one admissible family lies in [0, eps].               *)

let CMR_ESET_ELEMENT = prove
 (`!S (G:real^K->real^K^K) e Lam eps n Q (c:num->real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ &2 * eps <= e /\
     cmr_dfam n Q c r /\ cmr_sen_on G u (cmr_fop n Q c r) <= eps
     ==> &0 <= cm_sen G u - cm_sen G (cmr_repn S G n Q c (\j. r j / &2) u) /\
         cm_sen G u - cm_sen G (cmr_repn S G n Q c (\j. r j / &2) u) <= eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`;
                 `eps:real`; `&1 / &2`] CMR_FAM_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `k:num`]
                  CMR_FAM_CAP_BOUND) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    REWRITE_TAC[cm_gen] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\j. &1 / &2 * (r:num->real) j) = (\j. r j / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let CMR_ESET_FACTS = prove
 (`!S (G:real^K->real^K^K) e Lam eps (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ &0 <= eps /\ &2 * eps <= e
     ==> &0 IN cmr_eset S G eps u /\
         (!x. x IN cmr_eset S G eps u ==> &0 <= x /\ x <= eps) /\
         ~(cmr_eset S G eps u = {}) /\
         &0 <= cmr_e S G eps u /\ cmr_e S G eps u <= eps /\
         (!x. x IN cmr_eset S G eps u ==> x <= cmr_e S G eps u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN cmr_eset S G eps (u:real^3->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`0`; `\k:num. mat 1:real^3^3`; `\k:num. vec 0:real^2`;
                          `\k:num. &0`] THEN
    REWRITE_TAC[cmr_dfam; cmr_repn; CMR_FAM_SETS0; REAL_SUB_REFL] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`]
                  CMR_SEN_ON_BASICS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN cmr_eset S G eps (u:real^3->real^K) ==> &0 <= x /\ x <= eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `Q:num->real^3^3`
      (X_CHOOSE_THEN `c:num->real^2` (X_CHOOSE_THEN `r:num->real` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_ESET_ELEMENT THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cmr_eset S G eps (u:real^3->real^K) = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[cmr_e] THEN
  SUBGOAL_THEN `!x. x IN cmr_eset S G eps (u:real^3->real^K) ==> x <= sup(cmr_eset S G eps u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_SUP_LE THEN ASM_MESON_TAC[]]);;

(* Monotonicity in eps, and near-optimal families.                          *)

let CMR_E_MONO = prove
 (`!S (G:real^K->real^K^K) e Lam eps1 eps2 (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ &0 <= eps1 /\ eps1 <= eps2 /\
     &2 * eps2 <= e
     ==> cmr_e S G eps1 u <= cmr_e S G eps2 u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps1:real`;
                 `u:real^3->real^K`] CMR_ESET_FACTS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps2:real`;
                 `u:real^3->real^K`] CMR_ESET_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[cmr_e] THEN MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM cmr_e] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `x IN cmr_eset S G eps1 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMR_E_APPROX = prove
 (`!S (G:real^K->real^K^K) e Lam eps (u:real^3->real^K) a.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ &0 <= eps /\ &2 * eps <= e /\
     a < cmr_e S G eps u
     ==> ?n Q (c:num->real^2) r.
           cmr_dfam n Q c r /\ cmr_sen_on G u (cmr_fop n Q c r) <= eps /\
           a < cm_sen G u - cm_sen G (cmr_repn S G n Q c (\j. r j / &2) u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps:real`;
                 `u:real^3->real^K`] CMR_ESET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmr_eset S G eps (u:real^3->real^K)`; `a:real`] SUP_APPROACH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM cmr_e] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* A sequential replacement whose positive radii split into two blocks, the *)
(* first block before the second, is replacement on the first block         *)
(* followed by replacement on the second.                                   *)

let CMR_REPN_SPLIT = prove
 (`!S (G:real^K->real^K^K) (Q:num->real^3^3) (c:num->real^2) R R1 R2 (u:real^3->real^K).
     (!j. (R1 j <= &0 /\ R j = R2 j) \/ (R2 j <= &0 /\ R j = R1 j)) /\
     (!j k. &0 < R1 j /\ &0 < R2 k ==> j < k)
     ==> !m. cmr_repn S G m Q c R u = cmr_repn S G m Q c R2 (cmr_repn S G m Q c R1 u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC[cmr_repn] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o SPEC `SUC m`) THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_SIMP_TAC[CMR_REP1_NONPOS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_SIMP_TAC[CMR_REP1_NONPOS] THEN
  ASM_CASES_TAC `&0 < (R1:num->real) (SUC m)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    ASM_SIMP_TAC[CMR_REP1_NONPOS]] THEN
  SUBGOAL_THEN `!w:real^3->real^K. cmr_repn S G m Q c R2 w = w` (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN
  SUBGOAL_THEN `!k. k <= m ==> cmr_repn S G k Q c R2 (w:real^3->real^K) = w`
   (fun th -> MATCH_MP_TAC th THEN ARITH_TAC) THEN
  INDUCT_TAC THEN REWRITE_TAC[cmr_repn] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(R2:num->real) (SUC k) <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`SUC m`; `SUC k`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMR_REP1_NONPOS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* The G-energies of two W^{1,2} maps on an open set differ by               *)
(* at most Lam1 sqrt(dir(u - v)) (sqrt(dir u) + sqrt(dir v)) + C3 M dir(v),  *)
(* and the sums of these bounds over the caps of a disjoint family.          *)
(* ========================================================================= *)

let CMR_GDIR_DIFF_W12 = prove
 (`!S (G:real^K->real^K^K) Lam Lam1 C3 (A:real^2->bool) (u:real^2->real^K) v M.
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z w. &0 <= w dot (G z ** w) /\ w dot (G z ** w) <= Lam * norm w pow 2) /\
     (!z xi. z IN S ==> norm(G z ** xi) <= Lam1 * norm xi) /\
     (!y z xi. y IN S /\ z IN S ==> norm((G y - G z) ** xi) <= C3 * norm(y - z) * norm xi) /\
     (!z. transp(G z) = G z) /\ &0 <= Lam1 /\ &0 <= C3 /\
     open A /\ wan_w12 A u /\ wan_w12 A v /\
     (!x. x IN A ==> u x IN S /\ v x IN S /\ norm(u x - v x) <= M)
     ==> abs(wan_gdir A G u - wan_gdir A G v)
         <= Lam1 * sqrt(wan_dir A (\x. u x - v x)) *
                   (sqrt(wan_dir A u) + sqrt(wan_dir A v)) +
            C3 * M * wan_dir A v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2->real^K) measurable_on A /\ (v:real^2->real^K) measurable_on A`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[wan_w12; lspace; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^2->bool`; `A:real^2->bool`; `G:real^K->real^K^K`;
                 `u:real^2->real^K`] CMR_GDIR_RESTRICT) THEN
  MP_TAC(ISPECL [`A:real^2->bool`; `A:real^2->bool`; `G:real^K->real^K^K`;
                 `v:real^2->real^K`] CMR_GDIR_RESTRICT) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; DIMINDEX_2; SUM_2] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_wd A i (u:real^2->real^K) IN lspace A (&2) /\
            wan_wd A i (v:real^2->real^K) IN lspace A (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `S:real^K->bool`; `Lam:real`; `Lam1:real`; `C3:real`;
                 `M:real`; `A:real^2->bool`; `A:real^2->bool`;
                 `wan_wd A 1 (u:real^2->real^K)`; `wan_wd A 1 (v:real^2->real^K)`;
                 `u:real^2->real^K`; `v:real^2->real^K`] CMR_QUAD_DIFF_BOUND) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `S:real^K->bool`; `Lam:real`; `Lam1:real`; `C3:real`;
                 `M:real`; `A:real^2->bool`; `A:real^2->bool`;
                 `wan_wd A 2 (u:real^2->real^K)`; `wan_wd A 2 (v:real^2->real^K)`;
                 `u:real^2->real^K`; `v:real^2->real^K`] CMR_QUAD_DIFF_BOUND) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; SUBSET_REFL; ARITH] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`A:real^2->bool`;
                 `\x. wan_wd A 1 (u:real^2->real^K) x - wan_wd A 1 (v:real^2->real^K) x`;
                 `\x. wan_wd A 2 (u:real^2->real^K) x - wan_wd A 2 (v:real^2->real^K) x`;
                 `wan_wd A 1 (u:real^2->real^K)`;
                 `wan_wd A 2 (u:real^2->real^K)`] CMR_HOELDER_SUM2) THEN
  MP_TAC(ISPECL [`A:real^2->bool`;
                 `\x. wan_wd A 1 (u:real^2->real^K) x - wan_wd A 1 (v:real^2->real^K) x`;
                 `\x. wan_wd A 2 (u:real^2->real^K) x - wan_wd A 2 (v:real^2->real^K) x`;
                 `wan_wd A 1 (v:real^2->real^K)`;
                 `wan_wd A 2 (v:real^2->real^K)`] CMR_HOELDER_SUM2) THEN
  ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ARITH; ETA_AX] THEN
  REPEAT(DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    ASSUME_TAC(MATCH_MP REAL_LE_LMUL (CONJ (ASSUME `&0 <= Lam1`) (last (CONJUNCTS th)))))) THEN
  SUBGOAL_THEN
   `drop(integral A (\x. lift(norm(wan_wd A 1 (u:real^2->real^K) x -
                                   wan_wd A 1 (v:real^2->real^K) x) pow 2))) +
    drop(integral A (\x. lift(norm(wan_wd A 2 u x - wan_wd A 2 v x) pow 2))) =
    wan_dir A (\x. u x - v x) /\
    drop(integral A (\x. lift(norm(wan_wd A 1 (u:real^2->real^K) x) pow 2))) +
    drop(integral A (\x. lift(norm(wan_wd A 2 u x) pow 2))) = wan_dir A u /\
    drop(integral A (\x. lift(norm(wan_wd A 1 (v:real^2->real^K) x) pow 2))) +
    drop(integral A (\x. lift(norm(wan_wd A 2 v x) pow 2))) = wan_dir A v`
  (fun th -> MAP_EVERY (ASSUME_TAC o SYM) (CONJUNCTS th)) THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2] THEN
    MP_TAC(ISPECL [`A:real^2->bool`; `\x. (u:real^2->real^K) x - v x`;
                   `\i x. wan_wd A i (u:real^2->real^K) x - wan_wd A i (v:real^2->real^K) x`]
                  WAN_DIR_EQ) THEN
    MP_TAC(ISPECL [`A:real^2->bool`; `u:real^2->real^K`; `v:real^2->real^K`]
                  WAN_W12_SUB_WD) THEN
    ASM_SIMP_TAC[DIMINDEX_2; SUM_2; wan_dir];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> C3 * drop(integral A (\x. lift(norm((u:real^2->real^K) x - v x) *
                                          norm(wan_wd A i (v:real^2->real^K) x) pow 2)))
            <= C3 * (M * drop(integral A (\x. lift(norm(wan_wd A i v x) pow 2))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x. lift(norm(wan_wd A i (v:real^2->real^K) x) pow 2)) integrable_on A`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm((u:real^2->real^K) x - v x) *
                norm(wan_wd A i (v:real^2->real^K) x) pow 2)) integrable_on A`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `i = 1 \/ i = 2` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM DROP_CMUL] THEN
    SUBGOAL_THEN
     `M % integral A (\x. lift(norm(wan_wd A i (v:real^2->real^K) x) pow 2)) =
      integral A (\x. M % lift(norm(wan_wd A i v x) pow 2))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(SIMP_RULE[ARITH; LE_REFL]) THEN
  SUBGOAL_THEN
   `&0 <= wan_dir A (\x. (u:real^2->real^K) x - v x) /\ &0 <= wan_dir A u /\
    &0 <= wan_dir A (v:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN ASM_SIMP_TAC[WAN_W12_SUB];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) o
    check (fun th -> is_forall(concl th) && free_in `C3:real` (concl th) &&
                     free_in `M:real` (concl th))) THEN
  REWRITE_TAC[ARITH; LE_REFL] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The Dirichlet energies of the chart pictures over the caps of a disjoint *)
(* family add up to at most twice the S^2 Dirichlet energy.                  *)

let CMR_CAP_DIR_SUM = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r (f:real^3->real^K).
     cmr_dfam n Q c r /\ wan_s2_w12 f
     ==> sum(1..n) (\k. wan_dir (ball(c k,r k)) (\x. f(cm_capmap (Q k) x)))
         <= &2 * cm_sen (\y:real^K. mat 1) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `&1`; `f:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] CMR_SEN_FAM_SUM) THEN
  ASM_REWRITE_TAC[CMR_GCOND_ID] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[cm_gen; WAN_GDIR_ID; real_div; SUM_RMUL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `f:real^3->real^K`; `&1`;
                 `cmr_fop n (Q:num->real^3^3) (c:num->real^2) r`] CMR_SEN_ON_LE_SEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CMR_GCOND_ID] THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC CMR_CONE_OPEN THEN MATCH_MP_TAC CMR_FOP_OPEN_IN THEN
    ASM_MESON_TAC[cmr_dfam];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Real arithmetic for the family bound.                                     *)

let CMR_FGD_ARITH = prove
 (`!L C3 M D A B X Y Z SDA SDB.
     &0 <= L /\ &0 <= C3 /\ &0 <= M /\ &0 <= D /\ &0 <= A /\ &0 <= B /\
     D <= &2 * X /\ A <= &2 * Y /\ B <= &2 * Z /\
     SDA <= sqrt D * sqrt A /\ SDB <= sqrt D * sqrt B
     ==> (L * SDA + L * SDB + C3 * M * B) / &2
         <= (&2 * L + C3 + &1) * (sqrt X * (sqrt Y + sqrt Z) + M * Z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p q. sqrt(&2 * p) * sqrt(&2 * q) = &2 * sqrt p * sqrt q` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[SQRT_MUL] THEN
    SUBGOAL_THEN `sqrt(&2) * sqrt(&2) = &2` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= X /\ &0 <= Y /\ &0 <= Z` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt D /\ &0 <= sqrt A /\ &0 <= sqrt B /\
                &0 <= sqrt X /\ &0 <= sqrt Y /\ &0 <= sqrt Z`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt D * sqrt A <= &2 * sqrt X * sqrt Y /\
                sqrt D * sqrt B <= &2 * sqrt X * sqrt Z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    REWRITE_TAC[GSYM(ASSUME `!p q. sqrt(&2 * p) * sqrt(&2 * q) = &2 * sqrt p * sqrt q`)] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_MONO_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `L * SDA <= L * (&2 * sqrt X * sqrt Y) /\
                L * SDB <= L * (&2 * sqrt X * sqrt Z) /\
                (C3 * M) * B <= (C3 * M) * (&2 * Z)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= L * sqrt X * sqrt Y /\ &0 <= L * sqrt X * sqrt Z /\ &0 <= L * M * Z /\
    &0 <= C3 * sqrt X * sqrt Y /\ &0 <= C3 * sqrt X * sqrt Z /\
    &0 <= sqrt X * sqrt Y /\ &0 <= sqrt X * sqrt Z /\ &0 <= M * Z`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `L * SDA <= L * (&2 * sqrt X * sqrt Y)` THEN
  UNDISCH_TAC `L * SDB <= L * (&2 * sqrt X * sqrt Z)` THEN
  UNDISCH_TAC `(C3 * M) * B <= (C3 * M) * (&2 * Z)` THEN
  UNDISCH_TAC `&0 <= L * sqrt X * sqrt Y` THEN UNDISCH_TAC `&0 <= L * sqrt X * sqrt Z` THEN
  UNDISCH_TAC `&0 <= L * M * Z` THEN UNDISCH_TAC `&0 <= C3 * sqrt X * sqrt Y` THEN
  UNDISCH_TAC `&0 <= C3 * sqrt X * sqrt Z` THEN UNDISCH_TAC `&0 <= sqrt X * sqrt Y` THEN
  UNDISCH_TAC `&0 <= sqrt X * sqrt Z` THEN UNDISCH_TAC `&0 <= M * Z` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN REAL_ARITH_TAC);;

(* The sum over the caps of a disjoint family of the differences of the cap *)
(* energies of two maps, bounded by S^2 quantities.                          *)

let CMR_FAM_GEN_DIFF = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?K1. &0 < K1 /\
           !n (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K) v M.
             cm_smap S u /\ cm_smap S v /\ cmr_dfam n Q c r /\ &0 <= M /\
             (!y. y IN sphere(vec 0,&1) ==> norm(u y - v y) <= M)
             ==> sum(1..n) (\k. abs(cm_gen G (ball(c k,r k)) (\x. u(cm_capmap (Q k) x)) -
                                    cm_gen G (ball(c k,r k)) (\x. v(cm_capmap (Q k) x))))
                 <= K1 * (sqrt(cm_sen (\y. mat 1) (\y. u y - v y)) *
                          (sqrt(cm_sen (\y. mat 1) u) + sqrt(cm_sen (\y. mat 1) v)) +
                          M * cm_sen (\y. mat 1) v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. transp((G:real^K->real^K^K) z) = G z` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  EXISTS_TAC `&2 * Lam1 + C3 + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `dd = \k. wan_dir (ball((c:num->real^2) k,r k))
                         (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x) -
                              (v:real^3->real^K)(cm_capmap (Q k) x))` THEN
  ABBREV_TAC `aa = \k. wan_dir (ball((c:num->real^2) k,r k))
                         (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))` THEN
  ABBREV_TAC `bb = \k. wan_dir (ball((c:num->real^2) k,r k))
                         (\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))` THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n
        ==> &0 <= (dd:num->real) k /\ &0 <= (aa:num->real) k /\ &0 <= (bb:num->real) k /\
            abs(cm_gen G (ball((c:num->real^2) k,r k))
                  (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) -
                cm_gen G (ball(c k,r k)) (\x. (v:real^3->real^K)(cm_capmap (Q k) x)))
            <= (Lam1 * sqrt(dd k) * sqrt(aa k) + Lam1 * sqrt(dd k) * sqrt(bb k) +
                C3 * M * bb k) / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["dd"; "aa"; "bb"] THEN
    SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    ASM_CASES_TAC `&0 < (r:num->real) k` THENL
     [ALL_TAC;
      SUBGOAL_THEN `ball((c:num->real^2) k,r k) = {}` SUBST1_TAC THENL
       [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[CMR_CM_GEN_EMPTY; wan_dir; INTEGRAL_EMPTY; DROP_VEC; SUM_0] THEN
      REWRITE_TAC[SQRT_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_REFL] THEN
      REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `(Q:num->real^3^3) k`;
                   `(c:num->real^2) k`; `(r:num->real) k`] CMR_CHART_CMAP) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `v:real^3->real^K`; `(Q:num->real^3^3) k`;
                   `(c:num->real^2) k`; `(r:num->real) k`] CMR_CHART_CMAP) THEN
    ASM_REWRITE_TAC[cm_cmap] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[cm_gen] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(a - b) <= x ==> abs(a / &2 - b / &2) <= x / &2`) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `Lam1:real`; `C3:real`;
                   `ball((c:num->real^2) k,r k)`;
                   `\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`;
                   `\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`; `M:real`]
                  CMR_GDIR_DIFF_W12) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `cm_capmap ((Q:num->real^3^3) k) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
       [ASM_MESON_TAC[CMR_CAPMAP_FACTS]; ALL_TAC] THEN
      ASM_MESON_TAC[cm_smap];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. (Lam1 * sqrt((dd:num->real) k) * sqrt((aa:num->real) k) +
                              Lam1 * sqrt(dd k) * sqrt((bb:num->real) k) + C3 * M * bb k) / &2)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; SUM_RMUL; SUM_ADD_NUMSEG; SUM_LMUL] THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC CMR_FGD_ARITH THEN
  MAP_EVERY EXISTS_TAC [`sum(1..n) (dd:num->real)`; `sum(1..n) (aa:num->real)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    EXPAND_TAC "dd" THEN
    MP_TAC(ISPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `\y. (u:real^3->real^K) y - v y`] CMR_CAP_DIR_SUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC CMR_S2_W12_SUB THEN ASM_MESON_TAC[cm_smap]];
    EXPAND_TAC "aa" THEN
    MP_TAC(ISPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `u:real^3->real^K`] CMR_CAP_DIR_SUM) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[cm_smap]];
    EXPAND_TAC "bb" THEN
    MP_TAC(ISPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `v:real^3->real^K`] CMR_CAP_DIR_SUM) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[cm_smap]];
    MATCH_MP_TAC CMR_SUM_SQRT_CS THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CMR_SUM_SQRT_CS THEN ASM_SIMP_TAC[]]);;

(* The energy estimate (3.6) of CM_REPLACEMENT for the minimizers on one   *)
(* ball, named.                                                             *)

let cmr_repest = new_definition
 `cmr_repest S (G:real^K->real^K^K) e C <=>
    !(a:real^2) r (u1:real^2->real^K) u2 w1 w2 E.
       &0 < r /\
       cm_cmap S (ball(a,r)) u1 /\ cm_cmap S (ball(a,r)) u2 /\
       wan_gdir (ball(a,r)) G u1 <= E /\ wan_gdir (ball(a,r)) G u2 <= E /\ E <= e /\
       cm_minimizer S G (ball(a,r)) w1 /\ wan_w120 (ball(a,r)) (\x. w1 x - u1 x) /\
       cm_minimizer S G (ball(a,r)) w2 /\ wan_w120 (ball(a,r)) (\x. w2 x - u2 x)
       ==> abs(cm_gen G (ball(a,r)) w1 - cm_gen G (ball(a,r)) w2)
           <= C * sup {norm(u1 x - u2 x) | x IN cball(a,r)} * E +
              C * sqrt(wan_dir (ball(a,r)) (\x. u1 x - u2 x)) * sqrt E`;;

(* The G-energies of the chart pictures over the caps of a disjoint family  *)
(* add up to at most twice the S^2 energy.                                   *)

let CMR_CAP_GDIR_SUM = prove
 (`!(G:real^K->real^K^K) Lam n (Q:num->real^3^3) (c:num->real^2) r (f:real^3->real^K).
     CMR_GCOND G Lam /\ cmr_dfam n Q c r /\ wan_s2_w12 f
     ==> sum(1..n) (\k. wan_gdir (ball(c k,r k)) G (\x. f(cm_capmap (Q k) x)))
         <= &2 * cm_sen G f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `f:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] CMR_SEN_FAM_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[cm_gen; real_div; SUM_RMUL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`;
                 `cmr_fop n (Q:num->real^3^3) (c:num->real^2) r`] CMR_SEN_ON_LE_SEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC CMR_CONE_OPEN THEN MATCH_MP_TAC CMR_FOP_OPEN_IN THEN
    ASM_MESON_TAC[cmr_dfam];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMR_FMD_ARITH = prove
 (`!C M X D EE Y SDE.
     &0 <= C /\ &0 <= M /\ &0 <= D /\ &0 <= EE /\ D <= &2 * X /\ EE <= &2 * Y /\
     SDE <= sqrt D * sqrt EE
     ==> C * M * EE + C * SDE <= &2 * C * (M * Y + sqrt X * sqrt Y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&2 * X) * sqrt(&2 * Y) = &2 * sqrt X * sqrt Y` ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN
    SUBGOAL_THEN `sqrt(&2) * sqrt(&2) = &2` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt D * sqrt EE <= &2 * sqrt X * sqrt Y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * SDE <= C * (&2 * sqrt X * sqrt Y) /\ (C * M) * EE <= (C * M) * (&2 * Y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `C * SDE <= C * (&2 * sqrt X * sqrt Y)` THEN
  UNDISCH_TAC `(C * M) * EE <= (C * M) * (&2 * Y)` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN REAL_ARITH_TAC);;

(* The sum over the caps of the differences of the energies of the         *)
(* replacements.                                                            *)

let CMR_FAM_MINW_DIFF = prove
 (`!S (G:real^K->real^K^K) e Lam C n (Q:num->real^3^3) (c:num->real^2) r
    (u:real^3->real^K) v M.
     cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\ CMR_GCOND G Lam /\
     cm_smap S u /\ cm_smap S v /\ cmr_dfam n Q c r /\ &0 <= M /\
     (!y. y IN sphere(vec 0,&1) ==> norm(u y - v y) <= M) /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) +
              wan_gdir (ball(c k,r k)) G (\x. v(cm_capmap (Q k) x)) <= e)
     ==> sum(1..n) (\k. if &0 < r k
                        then abs(cm_gen G (ball(c k,r k))
                                   (cmr_minw S G (c k) (r k) (\x. u(cm_capmap (Q k) x))) -
                                 cm_gen G (ball(c k,r k))
                                   (cmr_minw S G (c k) (r k) (\x. v(cm_capmap (Q k) x))))
                        else &0)
         <= &2 * C * (M * (cm_sen G u + cm_sen G v) +
                      sqrt(cm_sen (\y. mat 1) (\y. u y - v y)) *
                      sqrt(cm_sen G u + cm_sen G v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN
  REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  ABBREV_TAC `dd = \k. wan_dir (ball((c:num->real^2) k,r k))
                         (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x) -
                              (v:real^3->real^K)(cm_capmap (Q k) x))` THEN
  ABBREV_TAC `ee = \k. wan_gdir (ball((c:num->real^2) k,r k)) G
                         (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) +
                       wan_gdir (ball(c k,r k)) G (\x. (v:real^3->real^K)(cm_capmap (Q k) x))` THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n
        ==> &0 <= (dd:num->real) k /\ &0 <= (ee:num->real) k /\
            (if &0 < r k
             then abs(cm_gen G (ball((c:num->real^2) k,r k))
                        (cmr_minw S G (c k) (r k)
                           (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))) -
                      cm_gen G (ball(c k,r k))
                        (cmr_minw S G (c k) (r k) (\x. (v:real^3->real^K)(cm_capmap (Q k) x))))
             else &0)
            <= C * M * ee k + C * sqrt(dd k) * sqrt(ee k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["dd"; "ee"] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    ASM_CASES_TAC `&0 < (r:num->real) k` THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `ball((c:num->real^2) k,r k) = {}` SUBST1_TAC THENL
       [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[wan_dir; wan_gdir; INTEGRAL_EMPTY; DROP_VEC; SUM_0] THEN
      REWRITE_TAC[SQRT_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_LE_REFL]] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `(Q:num->real^3^3) k`;
                   `(c:num->real^2) k`; `(r:num->real) k`] CMR_CHART_CMAP) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `v:real^3->real^K`; `(Q:num->real^3^3) k`;
                   `(c:num->real^2) k`; `(r:num->real) k`] CMR_CHART_CMAP) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= wan_gdir (ball((c:num->real^2) k,r k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) /\
      &0 <= wan_gdir (ball(c k,r k)) G (\x. (v:real^3->real^K)(cm_capmap (Q k) x))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CMW_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[cm_cmap];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_MESON_TAC[cm_cmap];
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `E = wan_gdir (ball((c:num->real^2) k,r k)) G
                      (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) +
                    wan_gdir (ball(c k,r k)) G (\x. (v:real^3->real^K)(cm_capmap (Q k) x))` THEN
    SUBGOAL_THEN `E <= e` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `(c:num->real^2) k`;
                   `(r:num->real) k`; `\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`]
                  CMR_MINW_WORKS) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `(c:num->real^2) k`;
                   `(r:num->real) k`; `\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`]
                  CMR_MINW_WORKS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `cmr_repest S (G:real^K->real^K^K) e C` THEN REWRITE_TAC[cmr_repest] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(c:num->real^2) k`; `(r:num->real) k`;
      `\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`;
      `\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`;
      `cmr_minw S G ((c:num->real^2) k) (r k)
         (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))`;
      `cmr_minw S G ((c:num->real^2) k) (r k)
         (\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))`; `E:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a + y ==> x <= b + y`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      EXISTS_TAC `norm((u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) ((c:num->real^2) k)) -
                       (v:real^3->real^K)(cm_capmap (Q k) (c k)))` THEN
      EXISTS_TAC `(c:num->real^2) k` THEN REWRITE_TAC[CENTRE_IN_CBALL] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. C * M * (ee:num->real) k + C * sqrt((dd:num->real) k) * sqrt(ee k))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  MATCH_MP_TAC CMR_FMD_ARITH THEN EXISTS_TAC `sum(1..n) (dd:num->real)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    EXPAND_TAC "dd" THEN
    MP_TAC(ISPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `\y. (u:real^3->real^K) y - v y`] CMR_CAP_DIR_SUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC CMR_S2_W12_SUB THEN ASM_MESON_TAC[cm_smap]];
    EXPAND_TAC "ee" THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `n:num`; `Q:num->real^3^3`;
                   `c:num->real^2`; `r:num->real`; `u:real^3->real^K`] CMR_CAP_GDIR_SUM) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `n:num`; `Q:num->real^3^3`;
                   `c:num->real^2`; `r:num->real`; `v:real^3->real^K`] CMR_CAP_GDIR_SUM) THEN
    ASM_REWRITE_TAC[CMR_GCOND] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CMR_SUM_SQRT_CS THEN ASM_SIMP_TAC[]]);;

(* CM (3.36): the energies after replacement on a disjoint family depend   *)
(* continuously on the map, uniformly in the family.                         *)

let CMR_REPN_UNIF = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?K1. &0 < K1 /\
           !e Lam C n (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K) v M.
             cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\ CMR_GCOND G Lam /\
             cm_smap S u /\ cm_smap S v /\ cmr_dfam n Q c r /\ &0 <= M /\
             (!y. y IN sphere(vec 0,&1) ==> norm(u y - v y) <= M) /\
             (!k. 1 <= k /\ k <= n /\ &0 < r k
                  ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) +
                      wan_gdir (ball(c k,r k)) G (\x. v(cm_capmap (Q k) x)) <= e)
             ==> abs(cm_sen G (cmr_repn S G n Q c r u) - cm_sen G (cmr_repn S G n Q c r v))
                 <= abs(cm_sen G u - cm_sen G v) +
                    K1 * (sqrt(cm_sen (\y. mat 1) (\y. u y - v y)) *
                          (sqrt(cm_sen (\y. mat 1) u) + sqrt(cm_sen (\y. mat 1) v)) +
                          M * cm_sen (\y. mat 1) v) +
                    &2 * C * (M * (cm_sen G u + cm_sen G v) +
                              sqrt(cm_sen (\y. mat 1) (\y. u y - v y)) *
                              sqrt(cm_sen G u + cm_sen G v))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K1:real` STRIP_ASSUME_TAC o MATCH_MP CMR_FAM_GEN_DIFF) THEN
  EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n /\ &0 < r k
        ==> wan_gdir (ball((c:num->real^2) k,r k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) <= e /\
            wan_gdir (ball(c k,r k)) G (\x. (v:real^3->real^K)(cm_capmap (Q k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= wan_gdir (ball((c:num->real^2) k,r k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) /\
      &0 <= wan_gdir (ball(c k,r k)) G (\x. (v:real^3->real^K)(cm_capmap (Q k) x))`
    MP_TAC THENL
     [UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN REWRITE_TAC[CMR_GCOND] THEN
      STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC CMW_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN
      MATCH_MP_TAC(MESON[cm_cmap]
        `cm_cmap (S:real^K->bool) s (f:real^2->real^K) ==> wan_w12 s f`) THEN
      MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      free_in `e:real` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `v:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                                `u:real^3->real^K`; `v:real^3->real^K`; `M:real`] o
    check (fun th -> is_forall(concl th) && free_in `K1:real` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `C:real`;
                 `n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                 `u:real^3->real^K`; `v:real^3->real^K`; `M:real`] CMR_FAM_MINW_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `abs(sum(1..n) (\k. if &0 < r k
                       then cmr_dec S G ((Q:num->real^3^3) k) ((c:num->real^2) k) (r k)
                              (u:real^3->real^K)
                       else &0) -
        sum(1..n) (\k. if &0 < r k then cmr_dec S G (Q k) (c k) (r k) (v:real^3->real^K)
                       else &0))
    <= sum(1..n) (\k. abs(cm_gen G (ball(c k,r k)) (\x. u(cm_capmap (Q k) x)) -
                          cm_gen G (ball(c k,r k)) (\x. v(cm_capmap (Q k) x)))) +
       sum(1..n) (\k. if &0 < r k
                      then abs(cm_gen G (ball(c k,r k))
                                 (cmr_minw S G (c k) (r k) (\x. u(cm_capmap (Q k) x))) -
                               cm_gen G (ball(c k,r k))
                                 (cmr_minw S G (c k) (r k) (\x. v(cm_capmap (Q k) x))))
                      else &0)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
    W(MP_TAC o PART_MATCH lhand SUM_ABS_NUMSEG o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[cmr_dec] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `sum(1..n) (\k. abs(cm_gen G (ball((c:num->real^2) k,r k))
                         (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) -
                       cm_gen G (ball(c k,r k)) (\x. (v:real^3->real^K)(cm_capmap (Q k) x))))
    <= K1 * (sqrt(cm_sen (\y. mat 1) (\y. u y - v y)) *
             (sqrt(cm_sen (\y. mat 1) u) + sqrt(cm_sen (\y. mat 1) v)) +
             M * cm_sen (\y. mat 1) v)` THEN
  UNDISCH_TAC
   `sum(1..n) (\k. if &0 < r k
                   then abs(cm_gen G (ball((c:num->real^2) k,r k))
                              (cmr_minw S G (c k) (r k)
                                 (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))) -
                            cm_gen G (ball(c k,r k))
                              (cmr_minw S G (c k) (r k) (\x. (v:real^3->real^K)(cm_capmap (Q k) x))))
                   else &0)
    <= &2 * C * (M * (cm_sen G u + cm_sen G v) +
                 sqrt(cm_sen (\y. mat 1) (\y. u y - v y)) * sqrt(cm_sen G u + cm_sen G v))` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Quantitative closeness of energies and replacement energies               *)
(* for maps close in C^0 and in Dirichlet energy, and the closeness of the  *)
(* slices of a sweepout at nearby times.                                    *)
(* ========================================================================= *)

(* Comparison of the G-energy and the Dirichlet energy on S^2.             *)

let CMR_SEN_BOUNDS = prove
 (`!(G:real^K->real^K^K) lam Lam (u:real^3->real^K).
     CMR_GCOND G Lam /\ &0 <= lam /\ (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
     wan_s2_w12 u
     ==> lam * cm_sen (\y. mat 1) u <= cm_sen G u /\
         cm_sen G u <= Lam * cm_sen (\y. mat 1) u /\
         &0 <= cm_sen (\y. mat 1) u /\ &0 <= cm_sen G u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMR_GCOND; wan_s2_w12] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wan_shell`; `G:real^K->real^K^K`; `wan_rext (u:real^3->real^K)`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ASM_SIMP_TAC[CMT_SHELL_OPEN] THEN STRIP_TAC THEN
  REWRITE_TAC[cm_sen; WAN_GDIR_ID] THEN
  SUBGOAL_THEN `&0 <= wan_dir wan_shell (wan_rext (u:real^3->real^K))` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMR_SEN_ID_SUB = prove
 (`!(u:real^3->real^K) v.
     wan_s2_w12 u /\ wan_s2_w12 v
     ==> cm_sen (\y. mat 1) v <=
         &2 * cm_sen (\y. mat 1) u + &2 * cm_sen (\y. mat 1) (\y. u y - v y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_s2_w12] THEN STRIP_TAC THEN
  REWRITE_TAC[cm_sen; WAN_GDIR_ID; GSYM CMR_REXT_SUB] THEN
  MP_TAC(ISPECL [`wan_shell`; `wan_rext (u:real^3->real^K)`;
                 `\z. wan_rext (v:real^3->real^K) z - wan_rext (u:real^3->real^K) z`]
                WAN_DIR_ADD_LE) THEN
  ASM_SIMP_TAC[CMT_SHELL_OPEN; WAN_W12_SUB; VECTOR_ARITH `u + (v - u):real^N = v`; ETA_AX] THEN
  MP_TAC(ISPECL [`wan_shell`; `wan_rext (u:real^3->real^K)`; `wan_rext (v:real^3->real^K)`]
                CMW_DIR_SUB_SYM) THEN
  ASM_REWRITE_TAC[CMT_SHELL_OPEN] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* The energies of two maps of S^2 into S differ by at most                 *)
(* K0 (sqrt(D(u - v)) (sqrt D(u) + sqrt D(v)) + M D(v)), D the Dirichlet      *)
(* energy on S^2 and M the C^0 distance.                                     *)

let CMR_SEN_DIFF = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?K0. &0 < K0 /\
           !(u:real^3->real^K) v M.
             cm_smap S u /\ cm_smap S v /\ &0 <= M /\
             (!y. y IN sphere(vec 0,&1) ==> norm(u y - v y) <= M)
             ==> abs(cm_sen G u - cm_sen G v)
                 <= K0 * (sqrt(cm_sen (\y. mat 1) (\y. u y - v y)) *
                          (sqrt(cm_sen (\y. mat 1) u) + sqrt(cm_sen (\y. mat 1) v)) +
                          M * cm_sen (\y. mat 1) v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. transp((G:real^K->real^K^K) z) = G z` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  SUBGOAL_THEN `CMR_GCOND (G:real^K->real^K^K) Lam` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CMR_GCOND]; ALL_TAC] THEN
  EXISTS_TAC `&2 * Lam1 + C3 + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC CMR_QB_FACTS THEN
  SUBGOAL_THEN `orthogonal_matrix(mat 1:real^3^3)` ASSUME_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_MATRIX_ID]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K) /\ wan_s2_w12 (v:real^3->real^K) /\
                wan_s2_w12 (\y. u y - v y)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_smap; CMR_S2_W12_SUB]; ALL_TAC] THEN
  (* the two hemispheres *)
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_HEMIS) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `v:real^3->real^K`; `Lam:real`] CMR_SEN_HEMIS) THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `u:real^3->real^K`; `&1`] CMR_SEN_HEMIS) THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `v:real^3->real^K`; `&1`] CMR_SEN_HEMIS) THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `\y. (u:real^3->real^K) y - v y`; `&1`]
                CMR_SEN_HEMIS) THEN
  ASM_REWRITE_TAC[CMR_GCOND_ID; cm_gen; WAN_GDIR_ID] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  (* per hemisphere *)
  SUBGOAL_THEN
   `!Q. orthogonal_matrix Q
        ==> abs(wan_gdir (ball(vec 0,&1)) G (\x. (u:real^3->real^K)(cm_capmap Q x)) -
                wan_gdir (ball(vec 0,&1)) G (\x. (v:real^3->real^K)(cm_capmap Q x)))
            <= Lam1 * sqrt(wan_dir (ball(vec 0,&1))
                             (\x. u(cm_capmap Q x) - v(cm_capmap Q x))) *
                      (sqrt(wan_dir (ball(vec 0,&1)) (\x. u(cm_capmap Q x))) +
                       sqrt(wan_dir (ball(vec 0,&1)) (\x. v(cm_capmap Q x)))) +
               C3 * M * wan_dir (ball(vec 0,&1)) (\x. v(cm_capmap Q x)) /\
            &0 <= wan_dir (ball(vec 0,&1)) (\x. u(cm_capmap Q x) - v(cm_capmap Q x)) /\
            &0 <= wan_dir (ball(vec 0,&1)) (\x. u(cm_capmap Q x)) /\
            &0 <= wan_dir (ball(vec 0,&1)) (\x. v(cm_capmap Q x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `Q:real^3^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `Q:real^3^3`; `vec 0:real^2`;
                   `&1`] CMR_CHART_CMAP) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `v:real^3->real^K`; `Q:real^3^3`; `vec 0:real^2`;
                   `&1`] CMR_CHART_CMAP) THEN
    ASM_REWRITE_TAC[REAL_LT_01; cm_cmap] THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `Lam1:real`;
                     `C3:real`; `ball(vec 0:real^2,&1)`;
                     `\x. (u:real^3->real^K)(cm_capmap Q x)`;
                     `\x. (v:real^3->real^K)(cm_capmap Q x)`; `M:real`] CMR_GDIR_DIFF_W12) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `cm_capmap (Q:real^3^3) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
       [ASM_MESON_TAC[CMR_CAPMAP_FACTS]; ALL_TAC] THEN
      ASM_MESON_TAC[cm_smap];
      MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `orthogonal_matrix(mat 1:real^3^3)`)) THEN
                          MP_TAC(MATCH_MP th (ASSUME `orthogonal_matrix cmr_qb`))) THEN
  ABBREV_TAC `D1 = wan_dir (ball(vec 0:real^2,&1))
                     (\x. (u:real^3->real^K)(cm_capmap (mat 1) x) - (v:real^3->real^K)(cm_capmap (mat 1) x))` THEN
  ABBREV_TAC `D2 = wan_dir (ball(vec 0:real^2,&1))
                     (\x. (u:real^3->real^K)(cm_capmap cmr_qb x) - (v:real^3->real^K)(cm_capmap cmr_qb x))` THEN
  ABBREV_TAC `A1 = wan_dir (ball(vec 0:real^2,&1)) (\x. (u:real^3->real^K)(cm_capmap (mat 1) x))` THEN
  ABBREV_TAC `A2 = wan_dir (ball(vec 0:real^2,&1)) (\x. (u:real^3->real^K)(cm_capmap cmr_qb x))` THEN
  ABBREV_TAC `B1 = wan_dir (ball(vec 0:real^2,&1)) (\x. (v:real^3->real^K)(cm_capmap (mat 1) x))` THEN
  ABBREV_TAC `B2 = wan_dir (ball(vec 0:real^2,&1)) (\x. (v:real^3->real^K)(cm_capmap cmr_qb x))` THEN
  ABBREV_TAC `g1 = wan_gdir (ball(vec 0:real^2,&1)) G (\x. (u:real^3->real^K)(cm_capmap (mat 1) x))` THEN
  ABBREV_TAC `g2 = wan_gdir (ball(vec 0:real^2,&1)) G (\x. (u:real^3->real^K)(cm_capmap cmr_qb x))` THEN
  ABBREV_TAC `h1 = wan_gdir (ball(vec 0:real^2,&1)) G (\x. (v:real^3->real^K)(cm_capmap (mat 1) x))` THEN
  ABBREV_TAC `h2 = wan_gdir (ball(vec 0:real^2,&1)) G (\x. (v:real^3->real^K)(cm_capmap cmr_qb x))` THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Lam1 * (sqrt D1 * sqrt A1 + sqrt D2 * sqrt A2) +
               Lam1 * (sqrt D1 * sqrt B1 + sqrt D2 * sqrt B2) + C3 * M * (B1 + B2)) / &2` THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`abs(g1 - h1) <= Lam1 * sqrt D1 * (sqrt A1 + sqrt B1) + C3 * M * B1`;
      `abs(g2 - h2) <= Lam1 * sqrt D2 * (sqrt A2 + sqrt B2) + C3 * M * B2`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CMR_FGD_ARITH THEN
  MAP_EVERY EXISTS_TAC [`D1 + D2:real`; `A1 + A2:real`] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; CMR_CS2] THEN ASM_REAL_ARITH_TAC);;

(* Real arithmetic for the closeness lemma.                                  *)

let CMR_T_ARITH = prove
 (`!K X Y Z M L s.
     &0 <= K /\ &0 <= X /\ &0 <= Y /\ &0 <= Z /\ &0 <= M /\
     sqrt X <= s /\ M <= s /\ Y <= L /\ Z <= L
     ==> K * (sqrt X * (sqrt Y + sqrt Z) + M * Z) <= s * (K * (&2 * sqrt L + L))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt Y <= sqrt L /\ sqrt Z <= sqrt L` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MONO_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt X /\ &0 <= sqrt Y /\ &0 <= sqrt Z` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt X * (sqrt Y + sqrt Z) <= s * (&2 * sqrt L) /\ M * Z <= s * L`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_ADD] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `K * (sqrt X * (sqrt Y + sqrt Z) + M * Z) <= K * (s * (&2 * sqrt L) + s * L)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let CMR_T3_ARITH = prove
 (`!C M X E B s.
     &0 <= C /\ &0 <= M /\ &0 <= X /\ &0 <= E /\ M <= s /\ sqrt X <= s /\ E <= B
     ==> &2 * C * (M * E + sqrt X * sqrt E) <= s * (&2 * C * (B + sqrt B))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt X /\ &0 <= sqrt E /\ sqrt E <= sqrt B` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `M * E <= s * B /\ sqrt X * sqrt E <= s * sqrt B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `C * (M * E + sqrt X * sqrt E) <= C * (s * B + s * sqrt B)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* For a fixed map u and eta0 > 0 there is eta > 0 such that every map v    *)
(* within eta of u in C^0 and in Dirichlet energy has energy, replacement   *)
(* energies on admissible families, and energies on their caps within eta0. *)

let CMR_UNIF_CLOSE = prove
 (`!S (G:real^K->real^K^K) d e Lam C (u:real^3->real^K) eta0.
     cm_target S G d /\ cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\
     CMR_GCOND G Lam /\ cm_smap S u /\ &0 < eta0
     ==> ?eta. &0 < eta /\
           !v. cm_smap S v /\
               (!y. y IN sphere(vec 0,&1) ==> norm(u y - v y) <= eta) /\
               cm_sen (\y. mat 1) (\y. u y - v y) <= eta
               ==> abs(cm_sen G u - cm_sen G v) <= eta0 /\
                   !n (Q:num->real^3^3) (c:num->real^2) r.
                     cmr_dfam n Q c r
                     ==> abs(cmr_sen_on G u (cmr_fop n Q c r) -
                             cmr_sen_on G v (cmr_fop n Q c r)) <= eta0 /\
                         ((!k. 1 <= k /\ k <= n /\ &0 < r k
                               ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) +
                                   wan_gdir (ball(c k,r k)) G (\x. v(cm_capmap (Q k) x))
                                   <= e)
                          ==> abs(cm_sen G (cmr_repn S G n Q c r u) -
                                  cm_sen G (cmr_repn S G n Q c r v)) <= eta0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K0:real` STRIP_ASSUME_TAC o MATCH_MP CMR_SEN_DIFF) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K1:real` STRIP_ASSUME_TAC o MATCH_MP CMR_FAM_GEN_DIFF) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K2:real` STRIP_ASSUME_TAC o MATCH_MP CMR_REPN_UNIF) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `&0`; `Lam:real`; `u:real^3->real^K`]
                CMR_SEN_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN SIMP_TAC[CMR_GCOND];
      ASM_MESON_TAC[cm_smap]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= Lam` ASSUME_TAC THENL
   [UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN REWRITE_TAC[CMR_GCOND] THEN
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`] o CONJUNCT2 o CONJUNCT2) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `LI = &2 * cm_sen (\y:real^K. mat 1) (u:real^3->real^K) + &2` THEN
  ABBREV_TAC `BB = cm_sen G (u:real^3->real^K) + Lam * LI` THEN
  SUBGOAL_THEN `&0 <= LI /\ &0 <= BB` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["LI"; "BB"] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A = (K0 + K1 + K2) * (&2 * sqrt LI + LI) + &2 * C * (BB + sqrt BB) + &1` THEN
  SUBGOAL_THEN `&0 <= &2 * sqrt LI + LI /\ &0 <= BB + sqrt BB` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &1 <= x + y + &1`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1) ((eta0 / A) pow 2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eta = min (&1) ((eta0 / A) pow 2)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 /\ sqrt eta * A <= eta0 /\ eta <= sqrt eta`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eta0 / A` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `eta <= &1 /\ eta <= (eta0 / A) pow 2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eta0 / A) * A` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((eta0 / A) pow 2)` THEN
        ASM_SIMP_TAC[SQRT_MONO_LE; POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL];
        SUBGOAL_THEN `eta0 / A * A = eta0` SUBST1_TAC THENL
         [UNDISCH_TAC `&1 <= A` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
      SUBGOAL_THEN `sqrt eta pow 2 = eta /\ &0 <= sqrt eta /\ sqrt eta <= &1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_LT_IMP_LE] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt eta * sqrt eta <= sqrt eta * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `sqrt eta pow 2 = eta` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^3->real^K` THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K) /\ wan_s2_w12 (v:real^3->real^K) /\
                wan_s2_w12 (\y. u y - v y)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_smap; CMR_S2_W12_SUB]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `&0`; `Lam:real`; `v:real^3->real^K`]
                CMR_SEN_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LZERO] THEN
    UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN SIMP_TAC[CMR_GCOND];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `&0`; `&1`; `\y. (u:real^3->real^K) y - v y`]
                CMR_SEN_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LZERO; CMR_GCOND_ID] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID; DOT_POS_LE];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `v:real^3->real^K`] CMR_SEN_ID_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `X = cm_sen (\y:real^K. mat 1) (\y. (u:real^3->real^K) y - v y)` THEN
  ABBREV_TAC `Y = cm_sen (\y:real^K. mat 1) (u:real^3->real^K)` THEN
  ABBREV_TAC `Z = cm_sen (\y:real^K. mat 1) (v:real^3->real^K)` THEN
  ABBREV_TAC `W = &2 * sqrt LI + LI` THEN
  SUBGOAL_THEN `sqrt X <= sqrt eta /\ Y <= LI /\ Z <= LI /\
                cm_sen G (u:real^3->real^K) + cm_sen G (v:real^3->real^K) <= BB /\
                &0 <= cm_sen G u + cm_sen G v /\ &0 <= sqrt eta`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_POS_LE; REAL_LT_IMP_LE; REAL_LE_ADD] THEN
    MAP_EVERY EXPAND_TAC ["BB"; "LI"] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `Lam * Z <= Lam * (&2 * Y + &2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. &0 <= K
        ==> K * (sqrt X * (sqrt Y + sqrt Z) + eta * Z) <= sqrt eta * (K * W)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "W" THEN MATCH_MP_TAC CMR_T_ARITH THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * C * (eta * (cm_sen G (u:real^3->real^K) + cm_sen G (v:real^3->real^K)) +
              sqrt X * sqrt(cm_sen G u + cm_sen G v))
    <= sqrt eta * (&2 * C * (BB + sqrt BB))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_T3_ARITH THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt eta * (K0 * W) + sqrt eta * (K2 * W) + sqrt eta * (&2 * C * (BB + sqrt BB))
    <= eta0 /\ sqrt eta * (K1 * W) <= eta0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= W /\ &0 <= sqrt BB` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= K0 * W /\ &0 <= K1 * W /\ &0 <= K2 * W /\ &0 <= C * (BB + sqrt BB)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt eta * A` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "A" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3->real^K`; `v:real^3->real^K`; `eta:real`] o
    check (fun th -> is_forall(concl th) && free_in `K0:real` (concl th))) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(cm_sen G (u:real^3->real^K) - cm_sen G (v:real^3->real^K))
                <= sqrt eta * (K0 * W)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K0 * (sqrt X * (sqrt Y + sqrt Z) + eta * Z)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `sqrt eta * (K2 * W)` REAL_LE_REFL) THEN
    SUBGOAL_THEN `&0 <= sqrt eta * (K2 * W) /\ &0 <= sqrt eta * (&2 * C * (BB + sqrt BB))`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE; REAL_LE_ADD; REAL_POS] THEN
      EXPAND_TAC "W" THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_POS];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `Lam:real`; `C:real`; `n:num`; `Q:num->real^3^3`;
                                  `c:num->real^2`; `r:num->real`; `u:real^3->real^K`;
                                  `v:real^3->real^K`; `eta:real`] o
      check (fun th -> is_forall(concl th) && free_in `K2:real` (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `K2 * (sqrt X * (sqrt Y + sqrt Z) + eta * Z) <= sqrt eta * (K2 * W)`
    MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC
     `&2 * C * (eta * (cm_sen G (u:real^3->real^K) + cm_sen G (v:real^3->real^K)) +
                sqrt X * sqrt(cm_sen G u + cm_sen G v))
      <= sqrt eta * (&2 * C * (BB + sqrt BB))` THEN
    UNDISCH_TAC `abs(cm_sen G (u:real^3->real^K) - cm_sen G (v:real^3->real^K))
                 <= sqrt eta * (K0 * W)` THEN
    UNDISCH_TAC
     `sqrt eta * (K0 * W) + sqrt eta * (K2 * W) + sqrt eta * (&2 * C * (BB + sqrt BB))
      <= eta0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] CMR_SEN_FAM_SUM) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `v:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] CMR_SEN_FAM_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. abs(cm_gen G (ball((c:num->real^2) k,r k))
                                   (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) -
                                 cm_gen G (ball(c k,r k))
                                   (\x. (v:real^3->real^K)(cm_capmap (Q k) x))))` THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC SUM_ABS_NUMSEG; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                                `u:real^3->real^K`; `v:real^3->real^K`; `eta:real`] o
    check (fun th -> is_forall(concl th) && free_in `K1:real` (concl th))) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `K1 * (sqrt X * (sqrt Y + sqrt Z) + eta * Z) <= sqrt eta * (K1 * W)`
  MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `sqrt eta * (K1 * W) <= eta0` THEN
  REAL_ARITH_TAC);;

(* The slices of a sweepout are uniformly continuous in t, uniformly on S^2. *)

let CMR_SWEEP_UNIF_T = prove
 (`!(W:real^3->real->real^K).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t)
        ==> !e. &0 < e
                ==> ?r. &0 < r /\
                        !y s t. y IN sphere(vec 0,&1) /\ s IN real_interval[&0,&1] /\
                                t IN real_interval[&0,&1] /\ abs(s - t) < r
                                ==> norm(W y s - W y t) < e`,
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
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `s:real`; `t:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (y:real^3) (lift t)`;
                                `pastecart (y:real^3) (lift s)`]) THEN
  EXPAND_TAC "KK" THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                  DIST_PASTECART_CANCEL; DIST_LIFT] THEN
  REWRITE_TAC[dist] THEN ASM_REWRITE_TAC[]);;

(* Nearby slices of a sweepout are close in C^0 and in Dirichlet energy.    *)

let CMR_SWEEP_CLOSE = prove
 (`!S (sigma:real^3->real->real^K) t eta.
     cm_sweep S sigma /\ t IN real_interval[&0,&1] /\ &0 < eta
     ==> ?delta. &0 < delta /\
           !s. s IN real_interval[&0,&1] /\ abs(s - t) < delta
               ==> (!y. y IN sphere(vec 0,&1) ==> norm(sigma y t - sigma y s) <= eta) /\
                   cm_sen (\y. mat 1) (\y. sigma y t - sigma y s) <= eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[cm_sweep]) THEN
  DISCH_THEN(MP_TAC o SPEC `eta:real` o MATCH_MP CMR_SWEEP_UNIF_T) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              REWRITE_RULE[cm_sweep]) THEN
  ASM_REWRITE_TAC[REALLIM_WITHINREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `&3 * eta`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_s2_w12 (\y. (sigma:real^3->real->real^K) y t) /\
                wan_s2_w12 (\y. sigma y s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_sweep; cm_smap]; ALL_TAC] THEN
  REWRITE_TAC[cm_sen; WAN_GDIR_ID; GSYM CMR_REXT_SUB] THEN
  MP_TAC(ISPECL [`wan_shell`; `wan_rext (\y. (sigma:real^3->real->real^K) y s)`;
                 `wan_rext (\y. (sigma:real^3->real->real^K) y t)`] CMW_DIR_SUB_SYM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CMT_SHELL_OPEN; wan_s2_w12]; DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `s:real = t` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN SIMP_TAC[WAN_DIR_ZERO; CMT_SHELL_OPEN] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* CM Lemma 3.34, the upper semicontinuity of the improvement                *)
(* e(t) along a sweepout.                                                   *)
(* ========================================================================= *)

(* The G-energy of a half cap of a disjoint family is at most twice the     *)
(* energy on the union of the caps.                                          *)

let CMR_HALF_CAP_BOUND = prove
 (`!S (G:real^K->real^K^K) Lam n Q (c:num->real^2) r (f:real^3->real^K) k.
     CMR_GCOND G Lam /\ cm_smap S f /\ cmr_dfam n Q c r /\ 1 <= k /\ k <= n /\ &0 < r k
     ==> wan_gdir (ball(c k,r k / &2)) G (\x. f(cm_capmap (Q k) x)) <=
         &2 * cmr_sen_on G f (cmr_fop n Q c r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `wan_gdir (ball((c:num->real^2) k,r k)) G
                (\x. (f:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`S:real^K->bool`; `f:real^3->real^K`; `(Q:num->real^3^3) k`;
                     `(c:num->real^2) k`; `(r:num->real) k`] CMR_CHART_CMAP) THEN
      ASM_SIMP_TAC[cm_cmap]];
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `f:real^3->real^K`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `k:num`]
                  CMR_FAM_CAP_BOUND) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; REWRITE_TAC[cm_gen] THEN REAL_ARITH_TAC]]);;

(* CM Lemma 3.34: if e_eps(t) > 0 then e_(eps/2)(s) <= 2 e_eps(t) for s near *)
(* t.                                                                        *)

let CMR_L334 = prove
 (`!S (G:real^K->real^K^K) d e Lam C eps (sigma:real^3->real->real^K) t.
     cm_target S G d /\ cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\
     CMR_GCOND G Lam /\ &0 < eps /\ &4 * eps <= e /\
     cm_sweep S sigma /\ t IN real_interval[&0,&1] /\
     &0 < cmr_e S G eps (\y. sigma y t)
     ==> ?delta. &0 < delta /\
           !s. s IN real_interval[&0,&1] /\ abs(s - t) < delta
               ==> cmr_e S G (eps / &2) (\y. sigma y s) <=
                   &2 * cmr_e S G eps (\y. sigma y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = cmr_e S G eps (\y. (sigma:real^3->real->real^K) y t)` THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> cm_smap S (\y. (sigma:real^3->real->real^K) y s)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `C:real`; `\y. (sigma:real^3->real->real^K) y t`; `min (a / &2) (eps / &2)`]
                CMR_UNIF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `sigma:real^3->real->real^K`; `t:real`; `eta:real`]
                CMR_SWEEP_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\y. (sigma:real^3->real->real^K) y s` o
    check (fun th -> is_forall(concl th) && free_in `eta:real` (concl th))) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fam")) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps / &2`;
                 `\y. (sigma:real^3->real->real^K) y s`] CMR_ESET_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[cmr_e] THEN MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `Q:num->real^3^3`
    (X_CHOOSE_THEN `c:num->real^2` (X_CHOOSE_THEN `r:num->real` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  (* the family on the time-t slice *)
  USE_THEN "fam" (fun th -> ASSUME_TAC(CONJUNCT1(MATCH_MP
    (SPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] th)
    (ASSUME `cmr_dfam n Q (c:num->real^2) r`)))) THEN
  SUBGOAL_THEN `cmr_sen_on G (\y. (sigma:real^3->real->real^K) y t)
                  (cmr_fop n Q (c:num->real^2) r) <= eps`
  ASSUME_TAC THENL
   [UNDISCH_TAC `abs(cmr_sen_on G (\y. (sigma:real^3->real->real^K) y t)
                       (cmr_fop n Q (c:num->real^2) r) -
                     cmr_sen_on G (\y. sigma y s) (cmr_fop n Q c r))
                 <= min (a / &2) (eps / &2)` THEN
    UNDISCH_TAC `cmr_sen_on G (\y. (sigma:real^3->real->real^K) y s)
                   (cmr_fop n Q (c:num->real^2) r) <= eps / &2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cmr_dfam n Q (c:num->real^2) (\j. r j / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r:num->real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "fam" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP
    (SPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `\j. (r:num->real) j / &2`] th)
    (ASSUME `cmr_dfam n Q (c:num->real^2) (\j. r j / &2)`)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (r:num->real) k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `\y. (sigma:real^3->real->real^K) y t`; `k:num`] CMR_HALF_CAP_BOUND) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `\y. (sigma:real^3->real->real^K) y s`; `k:num`] CMR_HALF_CAP_BOUND) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps:real`;
                 `\y. (sigma:real^3->real->real^K) y t`] CMR_ESET_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `cm_sen G (\y. (sigma:real^3->real->real^K) y t) -
                              cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. r j / &2)
                                          (\y. sigma y t))` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  UNDISCH_TAC `abs(cm_sen G (\y. (sigma:real^3->real->real^K) y t) - cm_sen G (\y. sigma y s))
               <= min (a / &2) (eps / &2)` THEN
  UNDISCH_TAC `abs(cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. r j / &2)
                               (\y. (sigma:real^3->real->real^K) y t)) -
                   cm_sen G (cmr_repn S G n Q c (\j. r j / &2) (\y. sigma y s)))
               <= min (a / &2) (eps / &2)` THEN
  UNDISCH_TAC `cm_sen G (\y. (sigma:real^3->real->real^K) y t) -
               cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. r j / &2) (\y. sigma y t))
               <= a` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* CM Lemma 3.39, local part: a family that improves the                     *)
(* slices near t by at least 1/8 of their improvement e_(eps/8).            *)
(* ========================================================================= *)

let CMR_L339_LOCAL = prove
 (`!S (G:real^K->real^K^K) d e Lam C eps (sigma:real^3->real->real^K) t.
     cm_target S G d /\ cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\
     CMR_GCOND G Lam /\ &0 < eps /\ &4 * eps <= e /\
     cm_sweep S sigma /\ t IN real_interval[&0,&1] /\
     &0 < cmr_e S G (eps / &8) (\y. sigma y t)
     ==> ?n Q (c:num->real^2) r delta.
           &0 < delta /\ cmr_dfam n Q c r /\
           !s. s IN real_interval[&0,&1] /\ abs(s - t) < delta
               ==> cmr_sen_on G (\y. sigma y s) (cmr_fop n Q c r) <= eps / &3 /\
                   cmr_e S G (eps / &8) (\y. sigma y s) <=
                   &8 * (cm_sen G (\y. sigma y s) -
                         cm_sen G (cmr_repn S G n Q c (\j. r j / &2) (\y. sigma y s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> cm_smap S (\y. (sigma:real^3->real->real^K) y s)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  ABBREV_TAC `a = cmr_e S G (eps / &4) (\y. (sigma:real^3->real->real^K) y t)` THEN
  SUBGOAL_THEN `cmr_e S G (eps / &8) (\y. (sigma:real^3->real->real^K) y t) <= a`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC CMR_E_MONO THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* a near-optimal family at t *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps / &4`;
                 `\y. (sigma:real^3->real->real^K) y t`; `a / &2`] CMR_E_APPROX) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Q:num->real^3^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:num->real^2` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->real` THEN STRIP_TAC THEN
  (* Lemma 3.34 at t with eps/4 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `C:real`; `eps / &4`; `sigma:real^3->real->real^K`; `t:real`] CMR_L334) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(eps / &4) / &2 = eps / &8`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  (* closeness of nearby slices *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `C:real`; `\y. (sigma:real^3->real->real^K) y t`; `min (a / &8) (eps / &12)`]
                CMR_UNIF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `sigma:real^3->real->real^K`; `t:real`; `eta:real`]
                CMR_SWEEP_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o
    check (fun th -> is_forall(concl th) && free_in `d2:real` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\y. (sigma:real^3->real->real^K) y s` o
    check (fun th -> is_forall(concl th) && free_in `eta:real` (concl th))) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fam")) THEN
  USE_THEN "fam" (fun th -> ASSUME_TAC(CONJUNCT1(MATCH_MP
    (SPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] th)
    (ASSUME `cmr_dfam n Q (c:num->real^2) r`)))) THEN
  SUBGOAL_THEN `cmr_sen_on G (\y. (sigma:real^3->real->real^K) y s)
                  (cmr_fop n Q (c:num->real^2) r) <= eps / &3`
  ASSUME_TAC THENL
   [UNDISCH_TAC `abs(cmr_sen_on G (\y. (sigma:real^3->real->real^K) y t)
                       (cmr_fop n Q (c:num->real^2) r) -
                     cmr_sen_on G (\y. sigma y s) (cmr_fop n Q c r))
                 <= min (a / &8) (eps / &12)` THEN
    UNDISCH_TAC `cmr_sen_on G (\y. (sigma:real^3->real->real^K) y t)
                   (cmr_fop n Q (c:num->real^2) r) <= eps / &4` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cmr_dfam n Q (c:num->real^2) (\j. r j / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r:num->real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "fam" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP
    (SPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `\j. (r:num->real) j / &2`] th)
    (ASSUME `cmr_dfam n Q (c:num->real^2) (\j. r j / &2)`)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (r:num->real) k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `\y. (sigma:real^3->real->real^K) y t`; `k:num`] CMR_HALF_CAP_BOUND) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `\y. (sigma:real^3->real->real^K) y s`; `k:num`] CMR_HALF_CAP_BOUND) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o
    check (fun th -> is_forall(concl th) && free_in `d1:real` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `abs(cm_sen G (\y. (sigma:real^3->real->real^K) y t) - cm_sen G (\y. sigma y s))
               <= min (a / &8) (eps / &12)` THEN
  UNDISCH_TAC `abs(cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. r j / &2)
                               (\y. (sigma:real^3->real->real^K) y t)) -
                   cm_sen G (cmr_repn S G n Q c (\j. r j / &2) (\y. sigma y s)))
               <= min (a / &8) (eps / &12)` THEN
  UNDISCH_TAC `a / &2 < cm_sen G (\y. (sigma:real^3->real->real^K) y t) -
               cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. r j / &2) (\y. sigma y t))` THEN
  UNDISCH_TAC `cmr_e S G (eps / &8) (\y. (sigma:real^3->real->real^K) y s) <= &2 * a` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Sequential replacement under change of data, concatenation                *)
(* of blocks, and blocks of a flattened list of families.                   *)
(* ========================================================================= *)

(* Replacement only depends on the data of the caps 1..m, and caps of       *)
(* nonpositive radius do nothing.                                            *)

let CMR_REPN_CONG = prove
 (`!S (G:real^K->real^K^K) m (Q:num->real^3^3) Q' (c:num->real^2) c' r r' (u:real^3->real^K).
     (!j. 1 <= j /\ j <= m
          ==> Q j = Q' j /\ c j = c' j /\ (r j = r' j \/ (r j <= &0 /\ r' j <= &0)))
     ==> cmr_repn S G m Q c r u = cmr_repn S G m Q' c' r' u`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[cmr_repn] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmr_repn S G m Q c r (u:real^3->real^K) = cmr_repn S G m Q' c' r' u`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= SUC m`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CMR_REP1_NONPOS]);;

let CMR_REPN_ADD = prove
 (`!S (G:real^K->real^K^K) m k (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K).
     cmr_repn S G (m + k) Q c r u =
     cmr_repn S G k (\j. Q(m + j)) (\j. c(m + j)) (\j. r(m + j)) (cmr_repn S G m Q c r u)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; cmr_repn]);;

let CMR_REPN_ZERO_UPTO = prove
 (`!S (G:real^K->real^K^K) m (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K).
     (!j. 1 <= j /\ j <= m ==> r j <= &0) ==> cmr_repn S G m Q c r u = u`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[cmr_repn] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cmr_repn S G m Q c r (u:real^3->real^K) = u` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CMR_REP1_NONPOS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* Flattening N blocks of Mx caps: cap j is cap ((j-1) MOD Mx + 1) of block *)
(* ((j-1) DIV Mx + 1).                                                       *)

let CMR_FLAT_INDEX = prove
 (`!Mx i k. 1 <= Mx /\ 1 <= i /\ 1 <= k /\ k <= Mx
            ==> ((i - 1) * Mx + k - 1) DIV Mx + 1 = i /\
                ((i - 1) * Mx + k - 1) MOD Mx + 1 = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(i - 1) * Mx + k - 1`; `Mx:num`; `i - 1`; `k - 1`] DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let CMR_FLAT_BLOCK_LE = prove
 (`!Mx j k. 1 <= Mx /\ j <= k ==> (j - 1) DIV Mx <= (k - 1) DIV Mx`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC);;

let CMR_FLAT_RANGE = prove
 (`!N Mx j. 1 <= Mx /\ 1 <= j /\ j <= N * Mx
            ==> 1 <= (j - 1) DIV Mx + 1 /\ (j - 1) DIV Mx + 1 <= N /\
                1 <= (j - 1) MOD Mx + 1 /\ (j - 1) MOD Mx + 1 <= Mx /\
                j = (((j - 1) DIV Mx + 1) - 1) * Mx + ((j - 1) MOD Mx + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`j - 1`; `Mx:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[ADD_SUB; ARITH_RULE `1 <= x + 1`] THEN
  SUBGOAL_THEN `(j - 1) DIV Mx < N` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* In a flattened list where only block i has nonzero radii, sequential     *)
(* replacement is replacement on block i.                                   *)

let CMR_REPN_BLOCK = prove
 (`!S (G:real^K->real^K^K) N Mx (QB:num->num->real^3^3) (cB:num->num->real^2)
    (rB:num->num->real) (u:real^3->real^K) i.
     1 <= Mx /\ 1 <= i /\ i <= N
     ==> cmr_repn S G (N * Mx) (\j. QB ((j - 1) DIV Mx + 1) ((j - 1) MOD Mx + 1))
                               (\j. cB ((j - 1) DIV Mx + 1) ((j - 1) MOD Mx + 1))
                               (\j. if (j - 1) DIV Mx + 1 = i
                                    then rB i ((j - 1) MOD Mx + 1) else &0) u =
         cmr_repn S G Mx (QB i) (cB i) (rB i) u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(i - 1) * Mx + Mx = i * Mx` ASSUME_TAC THENL
   [SUBGOAL_THEN `i = (i - 1) + 1` (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `N * Mx = (i - 1) * Mx + (Mx + (N - i) * Mx)` SUBST1_TAC THENL
   [SUBGOAL_THEN `N = (i - 1) + 1 + (N - i)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES]];
    ALL_TAC] THEN
  REWRITE_TAC[CMR_REPN_ADD] THEN
  SUBGOAL_THEN
   `cmr_repn S G ((i - 1) * Mx) (\j. QB ((j - 1) DIV Mx + 1) ((j - 1) MOD Mx + 1))
      (\j. cB ((j - 1) DIV Mx + 1) ((j - 1) MOD Mx + 1))
      (\j. if (j - 1) DIV Mx + 1 = i then rB i ((j - 1) MOD Mx + 1) else &0)
      (u:real^3->real^K) = u`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMR_REPN_ZERO_UPTO THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `(j - 1) DIV Mx < i - 1` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cmr_repn S G Mx (\j. QB ((((i - 1) * Mx + j) - 1) DIV Mx + 1)
                                       ((((i - 1) * Mx + j) - 1) MOD Mx + 1))
                (\j. cB ((((i - 1) * Mx + j) - 1) DIV Mx + 1) ((((i - 1) * Mx + j) - 1) MOD Mx + 1))
                (\j. if (((i - 1) * Mx + j) - 1) DIV Mx + 1 = i
                     then rB i ((((i - 1) * Mx + j) - 1) MOD Mx + 1) else &0)
                (u:real^3->real^K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMR_REPN_ZERO_UPTO THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `i <= (((i - 1) * Mx + Mx + k) - 1) DIV Mx` MP_TAC THENL
     [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CMR_REPN_CONG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`Mx:num`; `i:num`; `k:num`] CMR_FLAT_INDEX) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((i - 1) * Mx + k) - 1 = (i - 1) * Mx + k - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[]);;

(* ========================================================================= *)
(* The tent functions of a grid of mesh 1/N: tent i is 1 on                  *)
(* [(i-1)/N, i/N], 0 outside ((i-1)/N - 1/(4N), i/N + 1/(4N)), continuous,  *)
(* and at most two (consecutive) tents are positive at each time.            *)
(* ========================================================================= *)

let cmr_tent = new_definition
 `cmr_tent N i t =
    max (&0) (min (&1) (min (&4 * (&N * t - &i) + &5) (&4 * (&i - &N * t) + &1)))`;;

let CMR_TENT_FACTS = prove
 (`!N i t. &0 <= cmr_tent N i t /\ cmr_tent N i t <= &1 /\
           (&0 < cmr_tent N i t ==> &i - &5 / &4 < &N * t /\ &N * t < &i + &1 / &4) /\
           (&i - &1 <= &N * t /\ &N * t <= &i ==> cmr_tent N i t = &1)`,
  REWRITE_TAC[cmr_tent] THEN REAL_ARITH_TAC);;

let CMR_TENT_CONT = prove
 (`!N i s. (\t. cmr_tent N i t) real_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_tent] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN CONJ_TAC THEN
  REPEAT((MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD ORELSE MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB ORELSE
          MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL) THEN TRY CONJ_TAC) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID]);;

let CMR_TENT_TWO = prove
 (`!N i i' t. i < i' /\ &0 < cmr_tent N i t /\ &0 < cmr_tent N i' t ==> i' = i + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `i:num`; `t:real`] CMR_TENT_FACTS) THEN
  MP_TAC(SPECL [`N:num`; `i':num`; `t:real`] CMR_TENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&i' < &i + &3 / &2` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(i + 2 <= i')` MP_TAC THENL
   [DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* Every time in [0,1] lies in [(i-1)/N, i/N] for some 1 <= i <= N.          *)

let CMR_GRID_CELL = prove
 (`!N t. 1 <= N /\ t IN real_interval[&0,&1]
         ==> ?i. 1 <= i /\ i <= N /\ &i - &1 <= &N * t /\ &N * t <= &i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &N * t /\ &N * t <= &N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\i. &N * t <= &i` num_WOP) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `?i. &N * t <= &i` (fun th -> REWRITE_TAC[th]) THENL
   [EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `i:num = 0` THENL
   [EXISTS_TAC `1` THEN UNDISCH_TAC `&N * t <= &i` THEN ASM_REWRITE_TAC[LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(i:num) <= N` ASSUME_TAC THENL
   [ASM_CASES_TAC `(N:num) < i` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(i = 0) ==> 1 <= i`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (ASM_ARITH_TAC ORELSE ASM_REAL_ARITH_TAC));;

let CMR_TENT_POS = prove
 (`!N i t. &i - &5 / &4 < &N * t /\ &N * t < &i + &1 / &4 ==> &0 < cmr_tent N i t`,
  REWRITE_TAC[cmr_tent] THEN REAL_ARITH_TAC);;

(* The active blocks at a time t in [0,1]: a first one i0 <= N, and every    *)
(* active block is i0 or i0 + 1.                                            *)

let CMR_FLAT_ACTIVE = prove
 (`!N t. 1 <= N /\ t IN real_interval[&0,&1] /\ (?i. 1 <= i /\ &0 < cmr_tent N i t)
         ==> ?i0. 1 <= i0 /\ i0 <= N /\ &0 < cmr_tent N i0 t /\
                  !i. 1 <= i /\ &0 < cmr_tent N i t ==> i = i0 \/ i = i0 + 1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPEC `\i. 1 <= i /\ &0 < cmr_tent N i t` num_WOP) THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i0:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k. 1 <= k /\ &0 < cmr_tent N k t ==> i0 <= k` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      free_in `m:num` (concl th) = false)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `(N:num) < i0` THENL
     [ALL_TAC; UNDISCH_TAC `~((N:num) < i0)` THEN ARITH_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_TENT_POS THEN
    MP_TAC(SPECL [`N:num`; `i0:num`; `t:real`] CMR_TENT_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&N + &1 <= &i0 /\ &N * t <= &N` MP_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `(N:num) < i0` THEN ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        UNDISCH_TAC `t IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP (SPEC `i:num` (ASSUME `!k. 1 <= k /\ &0 < cmr_tent N k t ==> i0 <= k`))
    (CONJ (ASSUME `1 <= i`) (ASSUME `&0 < cmr_tent N i t`))) THEN
  REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  DISJ2_TAC THEN MATCH_MP_TAC CMR_TENT_TWO THEN
  MAP_EVERY EXISTS_TAC [`N:num`; `t:real`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* A flattened list of N blocks of caps (block i is the family               *)
(* (nB i, QB i, cB i, rB i), padded to Mx caps), its blocks, its subfamilies *)
(* and their energies.                                                       *)
(* ========================================================================= *)

let cmr_blk = new_definition `cmr_blk Mx j = (j - 1) DIV Mx + 1`;;

let cmr_loc = new_definition `cmr_loc Mx j = (j - 1) MOD Mx + 1`;;

let cmr_flatQ = new_definition
 `cmr_flatQ N Mx (nB:num->num) (QB:num->num->real^3^3) j =
    if 1 <= j /\ j <= N * Mx /\ cmr_loc Mx j <= nB(cmr_blk Mx j)
    then QB (cmr_blk Mx j) (cmr_loc Mx j) else mat 1`;;

let cmr_flatc = new_definition
 `cmr_flatc N Mx (nB:num->num) (cB:num->num->real^2) j =
    if 1 <= j /\ j <= N * Mx /\ cmr_loc Mx j <= nB(cmr_blk Mx j)
    then cB (cmr_blk Mx j) (cmr_loc Mx j) else vec 0`;;

let cmr_flatr = new_definition
 `cmr_flatr N Mx (nB:num->num) (rB:num->num->real) j =
    if 1 <= j /\ j <= N * Mx /\ cmr_loc Mx j <= nB(cmr_blk Mx j)
    then max (&0) (rB (cmr_blk Mx j) (cmr_loc Mx j)) else &0`;;

let CMR_FLATR_POS = prove
 (`!N Mx nB rB j. &0 <= cmr_flatr N Mx nB rB j`,
  REWRITE_TAC[cmr_flatr] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let CMR_FLATQ_ORTHO = prove
 (`!N Mx nB (QB:num->num->real^3^3) (cB:num->num->real^2) rB j.
     1 <= Mx /\ (!i. 1 <= i /\ i <= N ==> cmr_dfam (nB i) (QB i) (cB i) (rB i))
     ==> orthogonal_matrix(cmr_flatQ N Mx nB QB j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_flatQ] THEN COND_CASES_TAC THEN
  REWRITE_TAC[ORTHOGONAL_MATRIX_ID] THEN FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`N:num`; `Mx:num`; `j:num`] CMR_FLAT_RANGE) THEN
  ASM_REWRITE_TAC[GSYM cmr_blk; GSYM cmr_loc] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cmr_blk Mx j`) THEN ASM_REWRITE_TAC[cmr_dfam] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

let CMR_REPN_SPLIT_AT = prove
 (`!S (G:real^K->real^K^K) m n (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K).
     m <= n
     ==> cmr_repn S G n Q c r u =
         cmr_repn S G (n - m) (\j. Q(m + j)) (\j. c(m + j)) (\j. r(m + j))
           (cmr_repn S G m Q c r u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
  REWRITE_TAC[CMR_REPN_ADD; ADD_SUB2]);;

(* Replacement on one block of the flattened list (radii halved).           *)

let CMR_FLAT_BLOCK_REPN = prove
 (`!S (G:real^K->real^K^K) N Mx nB (QB:num->num->real^3^3) (cB:num->num->real^2) rB
    (u:real^3->real^K) i.
     1 <= i /\ i <= N /\ nB i < Mx
     ==> cmr_repn S G (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB)
           (\j. if cmr_blk Mx j = i then cmr_flatr N Mx nB rB j / &2 else &0) u =
         cmr_repn S G (nB i) (QB i) (cB i) (\k. rB i k / &2) u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= Mx` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Qp = \i k. if k <= nB i then (QB:num->num->real^3^3) i k else mat 1` THEN
  ABBREV_TAC `cp = \i k. if k <= nB i then (cB:num->num->real^2) i k else vec 0` THEN
  ABBREV_TAC `rp = \i k. if k <= nB i then max (&0) ((rB:num->num->real) i k) / &2 else &0` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cmr_repn S G (N * Mx) (\j. Qp ((j - 1) DIV Mx + 1) ((j - 1) MOD Mx + 1))
                (\j. cp ((j - 1) DIV Mx + 1) ((j - 1) MOD Mx + 1))
                (\j. if (j - 1) DIV Mx + 1 = i then rp i ((j - 1) MOD Mx + 1) else &0)
                (u:real^3->real^K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMR_REPN_CONG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["Qp"; "cp"; "rp"] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[cmr_flatQ; cmr_blk; cmr_loc]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[cmr_flatc; cmr_blk; cmr_loc]; ALL_TAC] THEN
    DISJ1_TAC THEN REWRITE_TAC[cmr_flatr; cmr_blk; cmr_loc] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `N:num`; `Mx:num`;
                 `Qp:num->num->real^3^3`; `cp:num->num->real^2`; `rp:num->num->real`;
                 `u:real^3->real^K`; `i:num`] CMR_REPN_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `nB(i:num):num`; `Mx:num`;
                 `(Qp:num->num->real^3^3) i`; `(cp:num->num->real^2) i`;
                 `(rp:num->num->real) i`; `u:real^3->real^K`] CMR_REPN_SPLIT_AT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cmr_repn S G (nB(i:num)) ((Qp:num->num->real^3^3) i) ((cp:num->num->real^2) i)
                (rp i) (u:real^3->real^K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMR_REPN_ZERO_UPTO THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    EXPAND_TAC "rp" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `1 <= k ==> ~(n + k <= n)`]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CMR_REPN_CONG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MAP_EVERY EXPAND_TAC ["Qp"; "cp"; "rp"] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* A subfamily of the flattened list carried by one block: its caps lie in  *)
(* the caps of that block, and it is disjoint.                               *)

let CMR_FLAT_SUB_CAP = prove
 (`!N Mx nB (QB:num->num->real^3^3) (cB:num->num->real^2) rB R' i j.
     1 <= Mx /\ (!j. &0 < R' j ==> cmr_blk Mx j = i /\ R' j <= cmr_flatr N Mx nB rB j) /\
     &0 < R' j
     ==> 1 <= j /\ j <= N * Mx /\ 1 <= cmr_loc Mx j /\ cmr_loc Mx j <= nB i /\
         cmr_blk Mx j = i /\ 1 <= i /\ i <= N /\
         cmr_flatQ N Mx nB QB j = QB i (cmr_loc Mx j) /\
         cmr_flatc N Mx nB cB j = cB i (cmr_loc Mx j) /\
         &0 < rB i (cmr_loc Mx j) /\ R' j <= rB i (cmr_loc Mx j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cmr_flatr N Mx nB rB j` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cmr_flatr] THEN
  COND_CASES_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(SPECL [`N:num`; `Mx:num`; `j:num`] CMR_FLAT_RANGE) THEN
  ASM_REWRITE_TAC[GSYM cmr_blk; GSYM cmr_loc] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_blk Mx j = i` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[cmr_flatQ; cmr_flatc] THEN
  UNDISCH_TAC `R' (j:num) <= cmr_flatr N Mx nB rB j` THEN
  ASM_REWRITE_TAC[cmr_flatr] THEN REAL_ARITH_TAC);;

let CMR_FLAT_SUB_FOP = prove
 (`!N Mx nB (QB:num->num->real^3^3) (cB:num->num->real^2) rB R' i.
     1 <= Mx /\ (!j. &0 < R' j ==> cmr_blk Mx j = i /\ R' j <= cmr_flatr N Mx nB rB j)
     ==> cmr_fop (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB) R' SUBSET
         cmr_fop (nB i) (QB i) (cB i) (rB i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; cmr_fop; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `&0 < (R':num->real) j` ASSUME_TAC THENL
   [UNDISCH_TAC `x IN ball(cmr_flatc N Mx nB (cB:num->num->real^2) j,R' j)` THEN
    REWRITE_TAC[IN_BALL] THEN MP_TAC(ISPECL [`cmr_flatc N Mx nB (cB:num->num->real^2) j`;
                                            `x:real^2`] DIST_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `Mx:num`; `nB:num->num`; `QB:num->num->real^3^3`;
                `cB:num->num->real^2`; `rB:num->num->real`; `R':num->real`; `i:num`; `j:num`]
               CMR_FLAT_SUB_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `cmr_loc Mx j` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `x:real^2` THEN UNDISCH_TAC `y = cm_capmap (cmr_flatQ N Mx nB (QB:num->num->real^3^3) j) x` THEN
  UNDISCH_TAC `x IN ball(cmr_flatc N Mx nB (cB:num->num->real^2) j,R' j)` THEN
  ASM_REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let CMR_FLAT_SUB_DFAM = prove
 (`!N Mx nB (QB:num->num->real^3^3) (cB:num->num->real^2) rB R' i.
     1 <= Mx /\ (!i. 1 <= i /\ i <= N ==> cmr_dfam (nB i) (QB i) (cB i) (rB i)) /\
     (!j. &0 < R' j ==> cmr_blk Mx j = i /\ R' j <= cmr_flatr N Mx nB rB j)
     ==> cmr_dfam (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB) R'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_dfam] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMR_FLATQ_ORTHO THEN
    MAP_EVERY EXISTS_TAC [`cB:num->num->real^2`; `rB:num->num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `l:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `Mx:num`; `nB:num->num`; `QB:num->num->real^3^3`;
                `cB:num->num->real^2`; `rB:num->num->real`; `R':num->real`; `i:num`; `j:num`]
               CMR_FLAT_SUB_CAP) THEN
  MP_TAC(SPECL [`N:num`; `Mx:num`; `nB:num->num`; `QB:num->num->real^3^3`;
                `cB:num->num->real^2`; `rB:num->num->real`; `R':num->real`; `i:num`; `l:num`]
               CMR_FLAT_SUB_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmr_loc Mx j < cmr_loc Mx l` ASSUME_TAC THENL
   [MP_TAC(SPECL [`N:num`; `Mx:num`; `j:num`] CMR_FLAT_RANGE) THEN
    MP_TAC(SPECL [`N:num`; `Mx:num`; `l:num`] CMR_FLAT_RANGE) THEN
    ASM_REWRITE_TAC[GSYM cmr_blk; GSYM cmr_loc] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `!i. 1 <= i /\ i <= N
                   ==> cmr_dfam (nB i) ((QB:num->num->real^3^3) i) ((cB:num->num->real^2) i)
                         ((rB:num->num->real) i)` THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[cmr_dfam] THEN
  DISCH_THEN(MP_TAC o SPECL [`cmr_loc Mx j`; `cmr_loc Mx l`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET s' /\ (t:real^3->bool) SUBSET t'
                         ==> DISJOINT s' t' ==> DISJOINT s t`) THEN
  CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_CBALL THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* CM Lemma 3.39, the flattened families along a sweepout.                   *)
(* ========================================================================= *)

let CMR_FOP_ZERO = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r. (!j. r j <= &0) ==> cmr_fop n Q c r = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_fop; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[BALL_EMPTY; IMAGE_CLAUSES; NOT_IN_EMPTY]);;

let CMR_DFAM_ZERO = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r.
     (!j. 1 <= j /\ j <= n ==> orthogonal_matrix(Q j)) /\ (!j. r j <= &0)
     ==> cmr_dfam n Q c r`,
  REWRITE_TAC[cmr_dfam] THEN MESON_TAC[REAL_NOT_LE]);;

let CMR_FOP_SEN_MONO = prove
 (`!(G:real^K->real^K^K) Lam (u:real^3->real^K) n1 Q1 (c1:num->real^2) r1 n2 Q2
    (c2:num->real^2) r2.
     CMR_GCOND G Lam /\ wan_s2_w12 u /\
     (!j. 1 <= j /\ j <= n1 ==> orthogonal_matrix(Q1 j)) /\
     (!j. 1 <= j /\ j <= n2 ==> orthogonal_matrix(Q2 j)) /\
     cmr_fop n1 Q1 c1 r1 SUBSET cmr_fop n2 Q2 c2 r2
     ==> cmr_sen_on G u (cmr_fop n1 Q1 c1 r1) <= cmr_sen_on G u (cmr_fop n2 Q2 c2 r2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
  MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_REWRITE_TAC[]);;

(* The two blocks active at a time t of the grid.                           *)

let CMR_FLAT_AT = prove
 (`!S (G:real^K->real^K^K) e Lam eps Estar N Mx nB (QB:num->num->real^3^3)
    (cB:num->num->real^2) rB (sigma:real^3->real->real^K) t.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_sweep S sigma /\ 1 <= N /\
     (!i. 1 <= i /\ i <= N ==> nB i < Mx) /\
     (!i. 1 <= i /\ i <= N ==> cmr_dfam (nB i) (QB i) (cB i) (rB i)) /\
     (!i s. 1 <= i /\ i <= N /\ s IN real_interval[&0,&1] /\ &0 < cmr_tent N i s
            ==> cmr_sen_on G (\y. sigma y s) (cmr_fop (nB i) (QB i) (cB i) (rB i)) <= eps / &3) /\
     (!i s. 1 <= i /\ i <= N /\ s IN real_interval[&0,&1] /\ &i - &1 <= &N * s /\
            &N * s <= &i /\ Estar <= cm_sen G (\y. sigma y s)
            ==> cmr_e S G (eps / &8) (\y. sigma y s) <=
                &8 * (cm_sen G (\y. sigma y s) -
                      cm_sen G (cmr_repn S G (nB i) (QB i) (cB i) (\k. rB i k / &2)
                                  (\y. sigma y s)))) /\
     &0 <= eps /\ t IN real_interval[&0,&1]
     ==> ?R1 R2.
           (!j. (R1 j <= &0 /\ cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j = R2 j) \/
                (R2 j <= &0 /\ cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j = R1 j)) /\
           (!j k. &0 < R1 j /\ &0 < R2 k ==> j < k) /\
           cmr_dfam (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB) R1 /\
           cmr_dfam (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB) R2 /\
           cmr_sen_on G (\y. sigma y t)
             (cmr_fop (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB) R1) <= eps / &3 /\
           cmr_sen_on G (\y. sigma y t)
             (cmr_fop (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB) R2) <= eps / &3 /\
           (Estar <= cm_sen G (\y. sigma y t)
            ==> cmr_e S G (eps / &8) (\y. sigma y t) <=
                &8 * (cm_sen G (\y. sigma y t) -
                      cm_sen G (cmr_repn S G (N * Mx) (cmr_flatQ N Mx nB QB)
                                  (cmr_flatc N Mx nB cB) (\j. R1 j / &2) (\y. sigma y t))) \/
                cmr_e S G (eps / &8) (\y. sigma y t) <=
                &8 * (cm_sen G (\y. sigma y t) -
                      cm_sen G (cmr_repn S G (N * Mx) (cmr_flatQ N Mx nB QB)
                                  (cmr_flatc N Mx nB cB) (\j. R2 j / &2) (\y. sigma y t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= Mx` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      free_in `Mx:num` (concl th) && not(free_in `cmr_dfam` (concl th)))) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cm_smap S (\y. (sigma:real^3->real->real^K) y t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. orthogonal_matrix(cmr_flatQ N Mx nB (QB:num->num->real^3^3) j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMR_FLATQ_ORTHO THEN
    MAP_EVERY EXISTS_TAC [`cB:num->num->real^2`; `rB:num->num->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmr_sen_on G (\y. (sigma:real^3->real->real^K) y t) {} = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (sigma:real^3->real->real^K) y t`; `Lam:real`]
                  CMR_SEN_ON_BASICS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. 1 <= cmr_blk Mx j` ASSUME_TAC THENL
   [REWRITE_TAC[cmr_blk] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. &0 <= cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j /\
        cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j <= cmr_flatr N Mx nB rB j`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPECL [`N:num`; `cmr_blk Mx j`; `t:real`] CMR_TENT_FACTS) THEN
    MP_TAC(SPECL [`N:num`; `Mx:num`; `nB:num->num`; `rB:num->num->real`; `j:num`]
                 CMR_FLATR_POS) THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the grid cell of t *)
  MP_TAC(SPECL [`N:num`; `t:real`] CMR_GRID_CELL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ic:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cmr_tent N ic t = &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`N:num`; `ic:num`; `t:real`] CMR_TENT_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `t:real`] CMR_FLAT_ACTIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ic:num` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!j. &0 < cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j
        ==> cmr_blk Mx j = i0 \/ cmr_blk Mx j = i0 + 1`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`N:num`; `cmr_blk Mx j`; `t:real`] CMR_TENT_FACTS) THEN
    MP_TAC(SPECL [`N:num`; `Mx:num`; `nB:num->num`; `rB:num->num->real`; `j:num`]
                 CMR_FLATR_POS) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `&0 < cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `\j. if cmr_blk Mx j = i0
                  then cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j else &0` THEN
  EXISTS_TAC `\j. if cmr_blk Mx j = i0
                  then &0 else cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!j. &0 < (if cmr_blk Mx j = i0
               then cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j else &0)
         ==> cmr_blk Mx j = i0 /\
             (if cmr_blk Mx j = i0
              then cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j else &0)
             <= cmr_flatr N Mx nB rB j) /\
    (!j. &0 < (if cmr_blk Mx j = i0
               then &0 else cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j)
         ==> cmr_blk Mx j = i0 + 1 /\
             (if cmr_blk Mx j = i0
              then &0 else cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j)
             <= cmr_flatr N Mx nB rB j)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LT_REFL] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= N * Mx ==> orthogonal_matrix(cmr_flatQ N Mx nB (QB:num->num->real^3^3) j)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= N
        ==> !k. 1 <= k /\ k <= nB i ==> orthogonal_matrix((QB:num->num->real^3^3) i k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!i. 1 <= i /\ i <= N
                     ==> cmr_dfam (nB i) ((QB:num->num->real^3^3) i) ((cB:num->num->real^2) i)
                           ((rB:num->num->real) i)` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[cmr_dfam] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* split *)
    X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL];
    (* order *)
    MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `cmr_blk Mx j = i0 /\ cmr_blk Mx k = i0 + 1` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM NOT_LE] THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`Mx:num`; `k:num`; `j:num`] CMR_FLAT_BLOCK_LE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cmr_blk Mx j = i0` THEN UNDISCH_TAC `cmr_blk Mx k = i0 + 1` THEN
    REWRITE_TAC[cmr_blk] THEN ARITH_TAC;
    (* dfam R1 *)
    MATCH_MP_TAC CMR_FLAT_SUB_DFAM THEN
    MAP_EVERY EXISTS_TAC [`rB:num->num->real`; `i0:num`] THEN ASM_REWRITE_TAC[];
    (* dfam R2 *)
    MATCH_MP_TAC CMR_FLAT_SUB_DFAM THEN
    MAP_EVERY EXISTS_TAC [`rB:num->num->real`; `i0 + 1`] THEN ASM_REWRITE_TAC[];
    (* energy R1 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (\y. (sigma:real^3->real->real^K) y t)
                  (cmr_fop (nB(i0:num)) ((QB:num->num->real^3^3) i0) ((cB:num->num->real^2) i0)
                     ((rB:num->num->real) i0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_FOP_SEN_MONO THEN EXISTS_TAC `Lam:real` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_MESON_TAC[cm_smap]; ASM_REWRITE_TAC[];
        UNDISCH_TAC `!i. 1 <= i /\ i <= N
                         ==> !k. 1 <= k /\ k <= nB i
                                 ==> orthogonal_matrix((QB:num->num->real^3^3) i k)` THEN
        DISCH_THEN(MP_TAC o SPEC `i0:num`) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CMR_FLAT_SUB_FOP THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `eps / &3` (concl th))) THEN ASM_REWRITE_TAC[]];
    (* energy R2 *)
    ASM_CASES_TAC
     `?k. &0 < (if cmr_blk Mx k = i0
                then &0 else cmr_tent N (cmr_blk Mx k) t * cmr_flatr N Mx nB rB k)` THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `k:num`) THEN
      MP_TAC(SPECL [`N:num`; `Mx:num`; `nB:num->num`; `QB:num->num->real^3^3`;
                    `cB:num->num->real^2`; `rB:num->num->real`;
                    `\j. if cmr_blk Mx j = i0
                         then &0 else cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j`;
                    `i0 + 1`; `k:num`] CMR_FLAT_SUB_CAP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < cmr_tent N (i0 + 1) t` ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < (if cmr_blk Mx k = i0
                           then &0 else cmr_tent N (cmr_blk Mx k) t * cmr_flatr N Mx nB rB k)` THEN
        ASM_REWRITE_TAC[ARITH_RULE `~(i0 + 1 = i0)`] THEN
        MP_TAC(SPECL [`N:num`; `i0 + 1`; `t:real`] CMR_TENT_FACTS) THEN
        STRIP_TAC THEN ASM_CASES_TAC `cmr_tent N (i0 + 1) t = &0` THEN
        ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmr_sen_on G (\y. (sigma:real^3->real->real^K) y t)
                    (cmr_fop (nB(i0 + 1)) ((QB:num->num->real^3^3) (i0 + 1))
                       ((cB:num->num->real^2) (i0 + 1)) ((rB:num->num->real) (i0 + 1)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CMR_FOP_SEN_MONO THEN EXISTS_TAC `Lam:real` THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_MESON_TAC[cm_smap]; ASM_REWRITE_TAC[];
          UNDISCH_TAC `!i. 1 <= i /\ i <= N
                           ==> !k. 1 <= k /\ k <= nB i
                                   ==> orthogonal_matrix((QB:num->num->real^3^3) i k)` THEN
          DISCH_THEN(MP_TAC o SPEC `i0 + 1`) THEN ASM_REWRITE_TAC[ARITH_RULE `1 <= i0 + 1`];
          MATCH_MP_TAC CMR_FLAT_SUB_FOP THEN ASM_REWRITE_TAC[]];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          free_in `eps / &3` (concl th))) THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= i0 + 1`]];
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; REAL_NOT_LT]) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP CMR_FOP_ZERO th]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* decrease *)
    DISCH_TAC THEN
    SUBGOAL_THEN `ic = i0 \/ ic = i0 + 1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC)] THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN
       `cmr_repn S G (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB)
          (\j. (if cmr_blk Mx j = i0
                then cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j else &0) / &2)
          (\y. (sigma:real^3->real->real^K) y t) =
        cmr_repn S G (nB i0) ((QB:num->num->real^3^3) i0) ((cB:num->num->real^2) i0)
          (\k. (rB:num->num->real) i0 k / &2) (\y. sigma y t)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `cmr_repn S G (N * Mx) (cmr_flatQ N Mx nB (QB:num->num->real^3^3))
                      (cmr_flatc N Mx nB (cB:num->num->real^2))
                      (\j. if cmr_blk Mx j = i0 then cmr_flatr N Mx nB rB j / &2 else &0)
                      (\y. (sigma:real^3->real->real^K) y t)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CMR_REPN_CONG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
          REWRITE_TAC[] THEN DISJ1_TAC THEN COND_CASES_TAC THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ic:num = i0` THEN
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC CMR_FLAT_BLOCK_REPN THEN ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `Estar:real` (concl th))) THEN
      UNDISCH_TAC `ic:num = i0` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN
      SUBGOAL_THEN
       `cmr_repn S G (N * Mx) (cmr_flatQ N Mx nB QB) (cmr_flatc N Mx nB cB)
          (\j. (if cmr_blk Mx j = i0
                then &0 else cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j) / &2)
          (\y. (sigma:real^3->real->real^K) y t) =
        cmr_repn S G (nB(i0 + 1)) ((QB:num->num->real^3^3) (i0 + 1))
          ((cB:num->num->real^2) (i0 + 1))
          (\k. (rB:num->num->real) (i0 + 1) k / &2) (\y. sigma y t)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `cmr_repn S G (N * Mx) (cmr_flatQ N Mx nB (QB:num->num->real^3^3))
                      (cmr_flatc N Mx nB (cB:num->num->real^2))
                      (\j. if cmr_blk Mx j = i0 + 1 then cmr_flatr N Mx nB rB j / &2 else &0)
                      (\y. (sigma:real^3->real->real^K) y t)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CMR_REPN_CONG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
          REWRITE_TAC[] THEN DISJ1_TAC THEN
          ASM_CASES_TAC `cmr_blk Mx j = i0` THEN
          ASM_REWRITE_TAC[ARITH_RULE `~(i0 = i0 + 1)`] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_CASES_TAC `cmr_blk Mx j = i0 + 1` THEN ASM_REWRITE_TAC[] THENL
           [UNDISCH_TAC `ic:num = i0 + 1` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
            ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `~(&0 < cmr_tent N (cmr_blk Mx j) t * cmr_flatr N Mx nB rB j)` MP_TAC THENL
           [ASM_MESON_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `cmr_flatr N Mx nB rB`)) (concl th) &&
            not (can (find_term (fun t -> t = `i0:num`)) (concl th)))) THEN
          REAL_ARITH_TAC;
          SUBGOAL_THEN `i0 + 1 <= N` ASSUME_TAC THENL
           [UNDISCH_TAC `ic:num = i0 + 1` THEN UNDISCH_TAC `ic:num <= N` THEN ARITH_TAC;
            ALL_TAC] THEN
          MATCH_MP_TAC CMR_FLAT_BLOCK_REPN THEN ASM_SIMP_TAC[ARITH_RULE `1 <= i0 + 1`]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `Estar:real` (concl th))) THEN
      UNDISCH_TAC `ic:num = i0 + 1` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* CM Lemma 3.39.                                                            *)
(* ========================================================================= *)

(* The energy of the slices of a sweepout is continuous in t.               *)

let CMR_SWEEP_SEN_CONT = prove
 (`!S (G:real^K->real^K^K) d e Lam C (sigma:real^3->real->real^K) t ep.
     cm_target S G d /\ cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\
     CMR_GCOND G Lam /\ cm_sweep S sigma /\ t IN real_interval[&0,&1] /\ &0 < ep
     ==> ?delta. &0 < delta /\
           !s. s IN real_interval[&0,&1] /\ abs(s - t) < delta
               ==> abs(cm_sen G (\y. sigma y t) - cm_sen G (\y. sigma y s)) <= ep`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> cm_smap S (\y. (sigma:real^3->real->real^K) y s)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `C:real`; `\y. (sigma:real^3->real->real^K) y t`; `ep:real`] CMR_UNIF_CLOSE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `sigma:real^3->real->real^K`; `t:real`; `eta:real`]
                CMR_SWEEP_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\y. (sigma:real^3->real->real^K) y s` o
    check (fun th -> is_forall(concl th) && free_in `eta:real` (concl th))) THEN
  ASM_SIMP_TAC[]);;

(* The times of energy below Estar, together with the complement of [0,1],  *)
(* form an open set.                                                         *)

let CMR_SEN_LOW_OPEN = prove
 (`!S (G:real^K->real^K^K) d e Lam C (sigma:real^3->real->real^K) Estar.
     cm_target S G d /\ cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\
     CMR_GCOND G Lam /\ cm_sweep S sigma
     ==> real_open ((:real) DIFF
                    {t | t IN real_interval[&0,&1] /\ Estar <= cm_sen G (\y. sigma y t)})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_open; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x IN real_interval[&0,&1]` THENL
   [ALL_TAC;
    UNDISCH_TAC `~(x IN real_interval[&0,&1])` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_TAC THEN EXISTS_TAC `max (--x) (x - &1)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real` THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `cm_sen G (\y. (sigma:real^3->real->real^K) y x) < Estar` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_NOT_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `C:real`; `sigma:real^3->real->real^K`; `x:real`;
                 `(Estar - cm_sen G (\y. (sigma:real^3->real->real^K) y x)) / &2`]
                CMR_SWEEP_SEN_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y IN real_interval[&0,&1]` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Where a tent is positive, the time is within 3/(4N) of the centre of its *)
(* cell.                                                                      *)

let CMR_TENT_NEAR = prove
 (`!N i s d0. 1 <= N /\ inv(&N) < d0 /\ &0 < cmr_tent N i s
              ==> s IN real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `i:num`; `s:real`] CMR_TENT_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s - (&i - &1 / &2) / &N = (&N * s - (&i - &1 / &2)) * inv(&N)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `abs(s - (&i - &1 / &2) / &N) < d0` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 * inv(&N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]);;

(* CM Lemma 3.39: finitely many disjoint families with continuous radius    *)
(* scalings, flattened into one list of caps, such that at each time the    *)
(* positive radii form two ordered disjoint subfamilies of energy at most   *)
(* eps/3, and when the slice has energy at least Estar one of them improves *)
(* it by at least e_(eps/8)/8.                                               *)

let CMR_L339 = prove
 (`!S (G:real^K->real^K^K) d e Lam C eps Estar (sigma:real^3->real->real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\
     CMR_GCOND G Lam /\ &0 < eps /\ &4 * eps <= e /\ cm_sweep S sigma /\
     (!t. t IN real_interval[&0,&1] /\ Estar <= cm_sen G (\y. sigma y t)
          ==> &0 < cmr_e S G (eps / &8) (\y. sigma y t))
     ==> ?M (QQ:num->real^3^3) (cc:num->real^2) RR.
           (!j. orthogonal_matrix (QQ j)) /\
           (!j. RR j real_continuous_on real_interval[&0,&1] /\
                !t. t IN real_interval[&0,&1] ==> &0 <= RR j t) /\
           (!j t. M < j ==> RR j t = &0) /\
           !t. t IN real_interval[&0,&1]
               ==> ?R1 R2.
                     (!j. (R1 j <= &0 /\ RR j t = R2 j) \/ (R2 j <= &0 /\ RR j t = R1 j)) /\
                     (!j k. &0 < R1 j /\ &0 < R2 k ==> j < k) /\
                     cmr_dfam M QQ cc R1 /\ cmr_dfam M QQ cc R2 /\
                     cmr_sen_on G (\y. sigma y t) (cmr_fop M QQ cc R1) <= eps / &3 /\
                     cmr_sen_on G (\y. sigma y t) (cmr_fop M QQ cc R2) <= eps / &3 /\
                     (Estar <= cm_sen G (\y. sigma y t)
                      ==> cmr_e S G (eps / &8) (\y. sigma y t) <=
                          &8 * (cm_sen G (\y. sigma y t) -
                                cm_sen G (cmr_repn S G M QQ cc (\j. R1 j / &2)
                                            (\y. sigma y t))) \/
                          cmr_e S G (eps / &8) (\y. sigma y t) <=
                          &8 * (cm_sen G (\y. sigma y t) -
                                cm_sen G (cmr_repn S G M QQ cc (\j. R2 j / &2)
                                            (\y. sigma y t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `IH = {t | t IN real_interval[&0,&1] /\
                        Estar <= cm_sen G (\y. (sigma:real^3->real->real^K) y t)}` THEN
  (* the local families *)
  SUBGOAL_THEN
   `!t. ?n Q (c:num->real^2) r delta.
          t IN IH
          ==> &0 < delta /\ cmr_dfam n Q c r /\
              !s. s IN real_interval[&0,&1] /\ abs(s - t) < delta
                  ==> cmr_sen_on G (\y. (sigma:real^3->real->real^K) y s) (cmr_fop n Q c r)
                      <= eps / &3 /\
                      cmr_e S G (eps / &8) (\y. sigma y s) <=
                      &8 * (cm_sen G (\y. sigma y s) -
                            cm_sen G (cmr_repn S G n Q c (\j. r j / &2) (\y. sigma y s)))`
  MP_TAC THENL
   [X_GEN_TAC `t:real` THEN ASM_CASES_TAC `(t:real) IN IH` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                   `C:real`; `eps:real`; `sigma:real^3->real->real^K`; `t:real`]
                  CMR_L339_LOCAL) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(t:real) IN IH` THEN EXPAND_TAC "IH" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `nf:real->num` (X_CHOOSE_THEN `Qf:real->num->real^3^3`
      (X_CHOOSE_THEN `cf:real->num->real^2` (X_CHOOSE_THEN `rf:real->num->real`
        (X_CHOOSE_THEN `df:real->real` (LABEL_TAC "loc"))))))] THEN
  (* a Lebesgue number of the cover of [0,1] by the J_t and the low times *)
  MP_TAC(ISPECL [`real_euclidean_metric`; `real_interval[&0,&1]`;
                 `((:real) DIFF IH) INSERT
                  {real_interval(t - df t,t + df t) | t IN IH}`] LEBESGUE_NUMBER) THEN
  REWRITE_TAC[MTOPOLOGY_REAL_EUCLIDEAN_METRIC; MBALL_REAL_INTERVAL;
              COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC; GSYM REAL_OPEN_IN;
                REAL_OPEN_REAL_INTERVAL] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "IH" THEN MATCH_MP_TAC CMR_SEN_LOW_OPEN THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `e:real`; `Lam:real`; `C:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; UNIONS_INSERT; IN_UNION; IN_DIFF; IN_UNIV; UNIONS_GSPEC;
                IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:real) IN IH` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    USE_THEN "loc" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(x:real) IN IH`) o
                    SPEC `x:real`) THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leb")))] THEN
  (* the grid *)
  MP_TAC(SPEC `d0:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= N ==> (&i - &1 / &2) / &N IN real_interval[&0,&1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0 < &N /\ &1 <= &i /\ &i <= &N` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `act = \i:num. ?t. t IN IH /\
            real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0) SUBSET
            real_interval(t - (df:real->real) t,t + df t)` THEN
  ABBREV_TAC
   `TT = \i:num. @t. t IN IH /\
            real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0) SUBSET
            real_interval(t - (df:real->real) t,t + df t)` THEN
  SUBGOAL_THEN
   `!i. (act:num->bool) i
        ==> (TT:num->real) i IN IH /\
            real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0) SUBSET
            real_interval(TT i - (df:real->real)(TT i),TT i + df(TT i))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN MAP_EVERY EXPAND_TAC ["act"; "TT"] THEN
    REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i s. 1 <= i /\ i <= N /\ ~((act:num->bool) i) /\
          s IN real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0)
          ==> ~(s IN IH)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(&i - &1 / &2) / &N IN real_interval[&0,&1]` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "leb" (MP_TAC o C MATCH_MP
      (ASSUME `(&i - &1 / &2) / &N IN real_interval[&0,&1]`) o SPEC `(&i - &1 / &2) / &N`) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `u IN ((:real) DIFF IH) INSERT {real_interval(t - (df:real->real) t,t + df t) | t IN IH}` THEN
    REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN STRIP_TAC THENL
     [UNDISCH_TAC `real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0) SUBSET u` THEN
      ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `~((act:num->bool) i)` THEN EXPAND_TAC "act" THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the block data *)
  ABBREV_TAC `nB = \i. if (act:num->bool) i then (nf:real->num)((TT:num->real) i) else 0` THEN
  ABBREV_TAC `Mx = nsum(1..N) nB + 1` THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= N ==> (nB:num->num) i < Mx` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Mx" THEN
    MATCH_MP_TAC(ARITH_RULE `x <= s ==> x < s + 1`) THEN
    MP_TAC(ISPECL [`nB:num->num`; `nsum(1..N) nB`; `1..N`] NSUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; LE_REFL; IN_NUMSEG] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Mx` ASSUME_TAC THENL
   [EXPAND_TAC "Mx" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (act:num->bool) i ==> ((nB:num->num) i = (nf:real->num)((TT:num->real) i))`
  ASSUME_TAC THENL [EXPAND_TAC "nB" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. ~((act:num->bool) i) ==> (nB:num->num) i = 0` ASSUME_TAC THENL
   [EXPAND_TAC "nB" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= N
        ==> cmr_dfam ((nB:num->num) i) ((Qf:real->num->real^3^3) ((TT:num->real) i))
              ((cf:real->num->real^2) (TT i)) ((rf:real->num->real) (TT i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `(act:num->bool) i` THENL
     [SUBGOAL_THEN `(TT:num->real) i IN IH` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(TT:num->real) i IN IH`) o
                      SPEC `(TT:num->real) i`) THEN
      SIMP_TAC[];
      ASM_SIMP_TAC[] THEN REWRITE_TAC[cmr_dfam] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i s. 1 <= i /\ i <= N /\ s IN real_interval[&0,&1] /\ &0 < cmr_tent N i s
          ==> cmr_sen_on G (\y. (sigma:real^3->real->real^K) y s)
                (cmr_fop ((nB:num->num) i) ((Qf:real->num->real^3^3) ((TT:num->real) i))
                   ((cf:real->num->real^2) (TT i)) ((rf:real->num->real) (TT i))) <= eps / &3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `(act:num->bool) i` THENL
     [SUBGOAL_THEN `(TT:num->real) i IN IH /\
                    abs(s - (TT:num->real) i) < (df:real->real) (TT i)` STRIP_ASSUME_TAC THENL
       [MP_TAC(SPECL [`N:num`; `i:num`; `s:real`; `d0:real`] CMR_TENT_NEAR) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(act:num->bool) i`) o
          check (fun th -> is_forall(concl th) && free_in `TT:num->real` (concl th) &&
                           free_in `df:real->real` (concl th))) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0) SUBSET
                     real_interval((TT:num->real) i - (df:real->real) (TT i),TT i + df (TT i))` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(TT:num->real) i IN IH`) o
                      SPEC `(TT:num->real) i`) THEN
      DISCH_THEN(MP_TAC o SPEC `s:real` o last o CONJUNCTS) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[CMR_FAM_SETS0] THEN
      MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (sigma:real^3->real->real^K) y s`; `Lam:real`]
                    CMR_SEN_ON_BASICS) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[cm_sweep; cm_smap]; ALL_TAC] THEN
      SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i s. 1 <= i /\ i <= N /\ s IN real_interval[&0,&1] /\ &i - &1 <= &N * s /\
          &N * s <= &i /\ Estar <= cm_sen G (\y. (sigma:real^3->real->real^K) y s)
          ==> cmr_e S G (eps / &8) (\y. sigma y s) <=
              &8 * (cm_sen G (\y. sigma y s) -
                    cm_sen G (cmr_repn S G ((nB:num->num) i)
                                ((Qf:real->num->real^3^3) ((TT:num->real) i))
                                ((cf:real->num->real^2) (TT i))
                                (\k. (rf:real->num->real) (TT i) k / &2) (\y. sigma y s)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(s:real) IN IH` ASSUME_TAC THENL
     [EXPAND_TAC "IH" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `s IN real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CMR_TENT_NEAR THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`N:num`; `i:num`; `s:real`] CMR_TENT_FACTS) THEN ASM_SIMP_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(act:num->bool) i` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(act:num->bool) i`) o
      check (fun th -> is_forall(concl th) && free_in `TT:num->real` (concl th) &&
                       free_in `df:real->real` (concl th))) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(TT:num->real) i IN IH`) o
                    SPEC `(TT:num->real) i`) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `real_interval((&i - &1 / &2) / &N - d0,(&i - &1 / &2) / &N + d0) SUBSET
                   real_interval((TT:num->real) i - (df:real->real) (TT i),TT i + df (TT i))` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the flattened data *)
  MAP_EVERY EXISTS_TAC
   [`(N:num) * Mx`;
    `cmr_flatQ N Mx nB (\i. (Qf:real->num->real^3^3) ((TT:num->real) i))`;
    `cmr_flatc N Mx nB (\i. (cf:real->num->real^2) ((TT:num->real) i))`;
    `\j t. cmr_tent N (cmr_blk Mx j) t *
           cmr_flatr N Mx nB (\i. (rf:real->num->real) ((TT:num->real) i)) j`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMR_FLATQ_ORTHO THEN
    MAP_EVERY EXISTS_TAC [`\i. (cf:real->num->real^2) ((TT:num->real) i)`;
                          `\i. (rf:real->num->real) ((TT:num->real) i)`] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN REWRITE_TAC[CMR_TENT_CONT];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[CMR_TENT_FACTS; CMR_FLATR_POS]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_flatr] THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMR_FLAT_AT THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ========================================================================= *)
(* The flattened families of CM Lemma 3.39 satisfy the                       *)
(* hypotheses of the replacement homotopy cmr_famok (pc_cmr_cont): every    *)
(* intermediate map has energy at most 4 eps/3 on the next cap.             *)
(* ========================================================================= *)

let CMR_POS_SCALE = prove
 (`!s r. &0 <= s /\ &0 < s * r ==> &0 < s /\ &0 < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [ASM_CASES_TAC `s = &0` THENL
     [UNDISCH_TAC `&0 < s * r` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
      ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_MUL_EQ]]);;

let CMR_DFAM_TAIL = prove
 (`!M m (Q:num->real^3^3) (c:num->real^2) r.
     (!j. orthogonal_matrix(Q j)) /\ cmr_dfam M Q c r /\ (!j. M < j ==> r j <= &0)
     ==> cmr_dfam m Q c r`,
  REWRITE_TAC[cmr_dfam] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th -> is_forall(concl th) &&
    free_in `M:num` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* A family scaled by s in [0,1] (any prefix of it) has its caps inside the *)
(* caps of the family.                                                        *)

let CMR_FOP_SCALE_SUB = prove
 (`!M m (Q:num->real^3^3) (c:num->real^2) r s.
     &0 <= s /\ s <= &1 /\ (!j. M < j ==> r j <= &0)
     ==> cmr_fop m Q c (\j. s * r j) SUBSET cmr_fop M Q c r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; cmr_fop; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `&0 < s * (r:num->real) k` ASSUME_TAC THENL
   [UNDISCH_TAC `x IN ball((c:num->real^2) k,s * r k)` THEN REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`(c:num->real^2) k`; `x:real^2`] DIST_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:real`; `(r:num->real) k`] CMR_POS_SCALE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x IN ball((c:num->real^2) k,s * r k)` THEN REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `s * (r:num->real) k <= r k` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REAL_ARITH_TAC]]);;

let CMR_SCALE_NONPOS = prove
 (`!s x. &0 <= s /\ x <= &0 ==> s * x <= &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= s * --x ==> s * x <= &0`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* The flattened families of CM Lemma 3.39 give a replacement homotopy.      *)

let CMR_FAMOK_FROM_SPLIT = prove
 (`!S (G:real^K->real^K^K) e Lam eps M (QQ:num->real^3^3) (cc:num->real^2) RR
    (sigma:real^3->real->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_sweep S sigma /\ &0 <= eps /\
     &8 * eps <= &3 * e /\
     (!j. orthogonal_matrix (QQ j)) /\
     (!j. RR j real_continuous_on real_interval[&0,&1] /\
          !t. t IN real_interval[&0,&1] ==> &0 <= RR j t) /\
     (!j t. M < j ==> RR j t = &0) /\
     (!t. t IN real_interval[&0,&1]
          ==> ?R1 R2.
                (!j. (R1 j <= &0 /\ RR j t = R2 j) \/ (R2 j <= &0 /\ RR j t = R1 j)) /\
                (!j k. &0 < R1 j /\ &0 < R2 k ==> j < k) /\
                cmr_dfam M QQ cc R1 /\ cmr_dfam M QQ cc R2 /\
                cmr_sen_on G (\y. sigma y t) (cmr_fop M QQ cc R1) <= eps / &3 /\
                cmr_sen_on G (\y. sigma y t) (cmr_fop M QQ cc R2) <= eps / &3)
     ==> cmr_famok S G e QQ cc RR sigma`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[cmr_famok] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `m:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    free_in `eps:real` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:num->real` (X_CHOOSE_THEN `R2:num->real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 <= s /\ s <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `cm_smap S (\y. (sigma:real^3->real->real^K) y t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  ABBREV_TAC `u = \y. (sigma:real^3->real->real^K) y t` THEN
  SUBGOAL_THEN `!j. M < j ==> (R1:num->real) j <= &0 /\ (R2:num->real) j <= &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `t:real`] o check (fun th -> is_forall(concl th) &&
      free_in `M:num` (concl th) && not(free_in `R1:num->real` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      free_in `R1:num->real` (concl th) && free_in `RR:num->real->real` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_dfam m QQ (cc:num->real^2) (\j. s * R1 j) /\ cmr_dfam m QQ cc (\j. s * R2 j) /\
    cmr_fop m QQ cc (\j. s * R1 j) SUBSET cmr_fop M QQ cc R1 /\
    cmr_fop m QQ cc (\j. s * R2 j) SUBSET cmr_fop M QQ cc R2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CMR_FOP_SCALE_SUB THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC CMR_DFAM_SHRINK THENL
     [EXISTS_TAC `R1:num->real`; EXISTS_TAC `R2:num->real`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CMR_DFAM_TAIL THEN EXISTS_TAC `M:num` THEN ASM_SIMP_TAC[];
       X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
       MP_TAC(SPECL [`s:real`; `(R1:num->real) k`] CMR_POS_SCALE) THEN
       MP_TAC(SPECL [`s:real`; `(R2:num->real) k`] CMR_POS_SCALE) THEN
       ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
       GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);
    ALL_TAC] THEN
  (* the scaled radii split as the radii do *)
  SUBGOAL_THEN
   `cmr_repn S G m QQ (cc:num->real^2) (\j. s * (RR:num->real->real) j t) (u:real^3->real^K) =
    cmr_repn S G m QQ cc (\j. s * R2 j) (cmr_repn S G m QQ cc (\j. s * R1 j) u)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `QQ:num->real^3^3`;
                   `cc:num->real^2`; `\j. s * (RR:num->real->real) j t`;
                   `\j. s * (R1:num->real) j`; `\j. s * (R2:num->real) j`;
                   `u:real^3->real^K`] CMR_REPN_SPLIT) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        free_in `R1:num->real` (concl th) && free_in `RR:num->real->real` (concl th))) THEN
      ASM_SIMP_TAC[CMR_SCALE_NONPOS];
      MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_POS_SCALE]];
    ALL_TAC] THEN
  (* energies on the scaled families and the cap *)
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (u:real^3->real^K) (cmr_fop m QQ (cc:num->real^2) (\j. s * R1 j)) <= eps / &3 /\
    cmr_sen_on G u (cmr_fop m QQ cc (\j. s * R2 j)) <= eps / &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop M QQ (cc:num->real^2) R1)`;
      EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop M QQ (cc:num->real^2) R2)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_FOP_SEN_MONO THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= m /\ &0 < s * R1 k
        ==> wan_gdir (ball((cc:num->real^2) k,s * R1 k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((QQ:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `m:num`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `\j. s * (R1:num->real) j`; `k:num`]
                  CMR_FAM_CAP_BOUND) THEN
    ASM_REWRITE_TAC[cm_gen] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v = cmr_repn S G m QQ (cc:num->real^2) (\j. s * R1 j) (u:real^3->real^K)` THEN
  SUBGOAL_THEN `cm_smap S (v:real^3->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `m:num`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `\j. s * (R1:num->real) j`;
                   `u:real^3->real^K`] CMR_REPN_DEC_SUM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (v:real^3->real^K) (cmr_fop m QQ (cc:num->real^2) (\j. s * R2 j))
    <= &2 * eps / &3`
  ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop m QQ (cc:num->real^2) (\j. s * R2 j)) +
                cmr_sen_on G u (cmr_fop m QQ cc (\j. s * R1 j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_REPN_FOP_BOUND THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= m /\ &0 < s * R2 k
        ==> wan_gdir (ball((cc:num->real^2) k,s * R2 k)) G
              (\x. (v:real^3->real^K)(cm_capmap ((QQ:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `v:real^3->real^K`; `m:num`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `\j. s * (R2:num->real) j`; `k:num`]
                  CMR_FAM_CAP_BOUND) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    REWRITE_TAC[cm_gen] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the next cap as a one-cap family *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `(QQ:num->real^3^3) (SUC m)`;
                 `(cc:num->real^2) (SUC m)`; `s * (RR:num->real->real) (SUC m) t`;
                 `u:real^3->real^K`] CMR_REPN_ONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `(RR:num->real->real) (SUC m) t`] CMR_POS_SCALE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SUC m <= M` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < (RR:num->real->real) (SUC m) t` THEN ASM_SIMP_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (u:real^3->real^K)
      (cmr_fop 1 (\k. (QQ:num->real^3^3) (SUC m)) (\k. (cc:num->real^2) (SUC m))
         (\k. s * (RR:num->real->real) (SUC m) t)) <= eps / &3`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!R':num->real. RR (SUC m) t = R' (SUC m) /\ cmr_dfam M QQ (cc:num->real^2) R'
        ==> cmr_sen_on G (u:real^3->real^K)
              (cmr_fop 1 (\k. (QQ:num->real^3^3) (SUC m)) (\k. (cc:num->real^2) (SUC m))
                 (\k. s * (RR:num->real->real) (SUC m) t)) <=
            cmr_sen_on G u (cmr_fop M QQ cc R')`
    ASSUME_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_FOP_SEN_MONO THEN
      EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; cmr_fop; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC m`] THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `x IN ball((cc:num->real^2) (SUC m),s * R' (SUC m))` THEN
      REWRITE_TAC[IN_BALL] THEN
      SUBGOAL_THEN `s * R' (SUC m) <= R' (SUC m)` MP_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(RR:num->real->real) (SUC m) t = (R':num->real) (SUC m)` THEN
        UNDISCH_TAC `&0 < (RR:num->real->real) (SUC m) t` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `SUC m` o check (fun th -> is_forall(concl th) &&
      free_in `R1:num->real` (concl th) && free_in `RR:num->real->real` (concl th))) THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop M QQ (cc:num->real^2) R2)`;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop M QQ (cc:num->real^2) R1)`] THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      free_in `M:num` (concl th) && free_in `s:real` (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (v:real^3->real^K)
      (cmr_fop 1 (\k. (QQ:num->real^3^3) (SUC m)) (\k. (cc:num->real^2) (SUC m))
         (\k. s * (RR:num->real->real) (SUC m) t)) <= &2 * eps / &3`
  ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (u:real^3->real^K)
                  (cmr_fop 1 (\k. (QQ:num->real^3^3) (SUC m)) (\k. (cc:num->real^2) (SUC m))
                     (\k. s * (RR:num->real->real) (SUC m) t)) +
                cmr_sen_on G u (cmr_fop m QQ cc (\j. s * R1 j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_REPN_FOP_BOUND THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (cmr_repn S G m QQ (cc:num->real^2) (\j. s * R2 j) (v:real^3->real^K))
      (cmr_fop 1 (\k. (QQ:num->real^3^3) (SUC m)) (\k. cc (SUC m))
         (\k. s * (RR:num->real->real) (SUC m) t)) <= &4 * eps / &3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (v:real^3->real^K)
                  (cmr_fop 1 (\k. (QQ:num->real^3^3) (SUC m)) (\k. (cc:num->real^2) (SUC m))
                     (\k. s * (RR:num->real->real) (SUC m) t)) +
                cmr_sen_on G v (cmr_fop m QQ cc (\j. s * R2 j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_REPN_FOP_BOUND THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* back to the chart *)
  SUBGOAL_THEN
   `wan_s2_w12 (cmr_repn S G m QQ (cc:num->real^2) (\j. s * R2 j) (v:real^3->real^K))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `m:num`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `\j. s * (R2:num->real) j`;
                   `v:real^3->real^K`] CMR_REPN_DEC_SUM) THEN
    ASM_SIMP_TAC[cm_smap];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`;
                 `cmr_repn S G m QQ (cc:num->real^2) (\j. s * R2 j) (v:real^3->real^K)`;
                 `(QQ:num->real^3^3) (SUC m)`; `Lam:real`;
                 `ball((cc:num->real^2) (SUC m),s * (RR:num->real->real) (SUC m) t)`]
                CMR_CAP_EN) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH `a = b / &2 ==> b = &2 * a`)) THEN
  UNDISCH_TAC
   `cmr_sen_on G (cmr_repn S G m QQ (cc:num->real^2) (\j. s * R2 j) (v:real^3->real^K))
      (cmr_fop 1 (\k. (QQ:num->real^3^3) (SUC m)) (\k. cc (SUC m))
         (\k. s * (RR:num->real->real) (SUC m) t)) <= &4 * eps / &3` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

