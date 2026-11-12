(* ========================================================================= *)
(* Unit pc_pde_menergy: the energy estimate for tr_k Hess_h on a compact     *)
(* manifold in chart-wise norms (PDE_MLIN_ENERGY) and uniqueness             *)
(* (PDE_MLIN_UNIQUE), by transplants of cut-off chart representatives to     *)
(* tori and the torus energy estimate.                                       *)
(* ========================================================================= *)

needs "src/pc_pde_mtor.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The exact transplant identity                                             *)
(*   int_cube |D^l T g|^2 = lam^(2|l|) lam^(-N) int_(R^N) |D^l g|^2          *)
(* for g supported in ball(0,lam/4), T = pdm_transplant lam, and its         *)
(* consequences for sums over index lists.                                   *)
(* ========================================================================= *)

let PDE_ME_SUPPORT_CUBE = prove
 (`!lam (x:real^N). &0 < lam /\ ~(x IN interval[vec 0,vec 1])
                    ==> lam / &4 < norm(lam % x + --(lam % inv(&2) % vec 1))`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_INTERVAL; NOT_FORALL_THM; NOT_IMP; VEC_COMPONENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `abs((lam % (x:real^N) + --(lam % inv(&2) % vec 1))$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT;
               VEC_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `lam * x + --(lam * inv(&2) * &1) = lam * (x - inv(&2))`] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  REWRITE_TAC[REAL_ARITH `lam / &4 < lam * y <=> lam * inv(&4) < lam * y`] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC);;

let PDE_ME_TRANSPLANT_TERM = prove
 (`!lam (g:real^N->real^K) l.
     &0 < lam /\ smooth_map_on (:real^N) g /\ (!z. lam / &4 < norm z ==> g z = vec 0)
     ==> drop(integral (interval[vec 0,vec 1])
                (\x. lift(norm(iterated_partial l (pdm_transplant lam g) x) pow 2))) =
         lam pow (2 * LENGTH l) * inv(lam pow dimindex(:N)) *
         drop(integral (:real^N) (\z. lift(norm(iterated_partial l g z) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `h = \z:real^N. lift(norm(iterated_partial l (g:real^N->real^K) z) pow 2)` THEN
  SUBGOAL_THEN `!z:real^N. lam / &4 < norm z ==> (h:real^N->real^1) z = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_EQ; GSYM LIFT_NUM] THEN
    REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; ARITH_EQ] THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `(:real^N) DIFF cball(vec 0,lam / &4)` THEN
    ASM_SIMP_TAC[GSYM closed; CLOSED_CBALL; IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^1) integrable_on (:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC PDM_SQNORM_PARTIAL_INTEGRABLE THEN
    EXISTS_TAC `cball(vec 0:real^N,lam / &4)` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (interval[vec 0,vec 1])
      (\x. lift(norm(iterated_partial l (pdm_transplant lam (g:real^N->real^K)) x) pow 2)) =
    integral (interval[vec 0,vec 1])
      (\x:real^N. lam pow (2 * LENGTH l) %
                  (h:real^N->real^1) (lam % x + --(lam % inv(&2) % vec 1)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`lam:real`; `g:real^N->real^K`; `l:num list`; `x:real^N`]
                  PDM_TRANSPLANT_PARTIAL) THEN
    ASM_SIMP_TAC[PDE_MT_CUBE_IN_BOX] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`; NORM_MUL; REAL_ABS_POW;
                 REAL_POW_MUL; LIFT_CMUL; REAL_POW_POW] THEN
    REWRITE_TAC[VECTOR_ARITH `lam % (x - c) = lam % x + --(lam % c):real^N`;
                ARITH_RULE `LENGTH(l:num list) * 2 = 2 * LENGTH l`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (interval[vec 0,vec 1])
      (\x:real^N. lam pow (2 * LENGTH(l:num list)) %
                  (h:real^N->real^1) (lam % x + --(lam % inv(&2) % vec 1))) =
    integral (:real^N)
      (\x. lam pow (2 * LENGTH l) % h (lam % x + --(lam % inv(&2) % vec 1)))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(h:real^N->real^1) (lam % x + --(lam % inv(&2) % vec 1)) = vec 0`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC PDE_ME_SUPPORT_CUBE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^1`; `lam:real`; `--(lam % inv(&2) % vec 1):real^N`]
                PDM_INTEGRABLE_AFFINE_UNIV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^1`; `lam:real`; `--(lam % inv(&2) % vec 1):real^N`]
                PDM_INTEGRAL_AFFINE_UNIV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; DROP_CMUL] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`]);;

let PDE_ME_UNIV_SQNORM_POS = prove
 (`!lam (g:real^N->real^K) l.
     smooth_map_on (:real^N) g /\ (!z. lam / &4 < norm z ==> g z = vec 0)
     ==> &0 <= drop(integral (:real^N) (\z. lift(norm(iterated_partial l g z) pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC PDM_SQNORM_PARTIAL_INTEGRABLE THEN
  EXISTS_TAC `cball(vec 0:real^N,lam / &4)` THEN
  ASM_SIMP_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE]);;

let PDE_ME_TRANSPLANT_HS2_LE = prove
 (`!lam (g:real^N->real^K) s.
     &1 <= lam /\ smooth_map_on (:real^N) g /\ (!z. lam / &4 < norm z ==> g z = vec 0)
     ==> pde_hs2 s (pdm_transplant lam g) <=
         lam pow (2 * s) *
         sum (pde_index_lists s (:N))
           (\l. drop(integral (:real^N) (\z. lift(norm(iterated_partial l g z) pow 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hs2; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lam:real`; `g:real^N->real^K`; `l:num list`] PDE_ME_TRANSPLANT_TERM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `g:real^N->real^K`; `l:num list`] PDE_ME_UNIV_SQNORM_POS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = drop(integral (:real^N)
                    (\z. lift(norm(iterated_partial l (g:real^N->real^K) z) pow 2)))` THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam pow (2 * LENGTH(l:num list)) * &1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let PDE_ME_CHART_LE_TRANSPLANT = prove
 (`!lam (g:real^N->real^K) s.
     &1 <= lam /\ smooth_map_on (:real^N) g /\ (!z. lam / &4 < norm z ==> g z = vec 0)
     ==> sum (pde_index_lists s (:N))
           (\l. drop(integral (:real^N) (\z. lift(norm(iterated_partial l g z) pow 2))))
         <= lam pow dimindex(:N) * pde_hs2 s (pdm_transplant lam g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hs2; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lam:real`; `g:real^N->real^K`; `l:num list`] PDE_ME_TRANSPLANT_TERM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `g:real^N->real^K`; `l:num list`] PDE_ME_UNIV_SQNORM_POS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = drop(integral (:real^N)
                    (\z. lift(norm(iterated_partial l (g:real^N->real^K) z) pow 2)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < lam pow dimindex(:N) /\ &1 <= lam pow (2 * LENGTH(l:num list))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * y * z * r:real = (x * z) * y * r`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Chart norms of pde_upto families with a uniformly bounded support are     *)
(* continuous in time (parametric integrals over a box,                      *)
(* NS_PARAM_INTEGRAL_SMOOTH).                                                *)
(* ========================================================================= *)

let PDE_ME_OUTSIDE_BOX = prove
 (`!R (z:real^N). ~(z IN interval[--(abs R + &1) % vec 1,(abs R + &1) % vec 1])
                  ==> R < norm z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INTERVAL; NOT_FORALL_THM; NOT_IMP; VECTOR_MUL_COMPONENT;
              VECTOR_NEG_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs((z:real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN ASM_REAL_ARITH_TAC);;

let PDE_ME_CHART_NORM_CONT = prove
 (`!a b b' (G:real->real^N->real^K) R l.
     pde_upto a b (:real^N) G /\ b' < b /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     (!t z. a <= t /\ t < b /\ R < norm z ==> G t z = vec 0)
     ==> (\r. drop(integral (:real^N) (\z. lift(norm(iterated_partial l (G r) z) pow 2))))
         real_continuous_on real_interval[a,b']`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FG:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `H = \w:real^(1,N)finite_sum.
                    lift(norm(iterated_partial (MAP (\k. 1 + k) l)
                                (FG:real^(1,N)finite_sum->real^K) w) pow 2)` THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift(a - e),lift b) PCROSS (:real^N))
                  (H:real^(1,N)finite_sum->real^1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift(a - e),lift b)`;
                 `interval(lift(a - e),lift b) PCROSS (:real^N)`;
                 `--(abs R + &1) % vec 1:real^N`; `(abs R + &1) % vec 1:real^N`;
                 `H:real^(1,N)finite_sum->real^1`] NS_PARAM_INTEGRAL_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV];
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\r. drop(integral (interval[--(abs R + &1) % vec 1,(abs R + &1) % vec 1])
                      (\z:real^N. (H:real^(1,N)finite_sum->real^1)
                                  (pastecart (lift r) z)))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
    SUBGOAL_THEN `(G:real->real^N->real^K) r =
                  (\y. (FG:real^(1,N)finite_sum->real^K) (pastecart (lift r) y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [EXPAND_TAC "H" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_ST_SLICE_ITERATED THEN
      EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (:real^N)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV;
                   IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[LIFT_EQ; GSYM LIFT_NUM] THEN
    REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; ARITH_EQ] THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `(:real^N) DIFF cball(vec 0,R)` THEN
    SIMP_TAC[GSYM closed; CLOSED_CBALL; IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE] THEN
    ASM_SIMP_TAC[PDE_ME_OUTSIDE_BOX] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(FG:real^(1,N)finite_sum->real^K) (pastecart (lift r) y) = G r y`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval(lift(a - e),lift b)` THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Jets of sums and bilinear products, and the H^s bound of the commutator   *)
(* pde_mt_comm on the torus by the H^(s+1) norm, uniformly in time for       *)
(* admissible coefficients.                                                  *)
(* ========================================================================= *)

let PDE_ME_JETN_ADD = prove
 (`!m (f:real^N->real^K) g x.
     smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g
     ==> pde_jetn m (\x. f x + g x) x <= pde_jetn m f x + pde_jetn m g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn; GSYM SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[GSYM(MATCH_MP SUM_ADD (SPEC_ALL PDE_INDEX_LISTS_FINITE))] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `(:real^N)`; `f:real^N->real^K`; `g:real^N->real^K`]
                PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[NORM_TRIANGLE]);;

let PDE_ME_JETN_VSUM = prove
 (`!m (f:A->real^N->real^K) S x.
     FINITE S /\ (!a. a IN S ==> smooth_map_on (:real^N) (f a))
     ==> pde_jetn m (\x. vsum S (\a. f a x)) x <= sum S (\a. pde_jetn m (f a) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:num list`; `(:real^N)`; `f:A->real^N->real^K`; `S:A->bool`]
                PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let PDE_ME_JETN_BILINEAR = prove
 (`!(bb:real^P->real^Q->real^K) M A m (f:real^N->real^P) g x.
     bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M /\ &0 <= A /\
     smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g /\
     (!l' y. LENGTH l' <= m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l'
             ==> norm(iterated_partial l' f y) <= A)
     ==> pde_jetn m (\x. bb (f x) (g x)) x <=
         &(CARD(pde_index_lists m (:N))) * (&2 pow m * M * A) * pde_jetn m g x`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [pde_jetn] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists m (:N))
                (\l:num list. &2 pow m * M * A * pde_jetn m (g:real^N->real^Q) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `M:real`; `A:real`] PDE_LEIBNIZ_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`l:num list`; `f:real^N->real^P`; `g:real^N->real^Q`;
                               `x:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[PDE_JETN_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN REAL_ARITH_TAC]);;

let PDE_ME_ENTRY_BILINEAR = prove
 (`!i j. bilinear (\(m:real^(N,N)finite_prod) (v:real^K). (matrify m:real^N^N)$i$j % v) /\
         (!m (v:real^K). norm((matrify m:real^N^N)$i$j % v) <= &1 * norm m * norm v)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
                MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[NORM_MUL; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; PDE_MATRIFY_ENTRY_LE]]);;

let PDE_ME_MATVEC_BILINEAR = prove
 (`bilinear (\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v) /\
   (!m v. norm((matrify m:real^K^K) ** v) <= &1 * norm m * norm v)`,
  REWRITE_TAC[INST_TYPE [`:K`,`:N`] LRG_BILINEAR_MATRIFY_MUL; REAL_MUL_LID;
              PDE_MATRIFY_MUL_NORM]);;

let PDE_ME_DROPMUL_BILINEAR = prove
 (`bilinear (\(c:real^1) (v:real^K). drop c % v) /\
   (!c v. norm(drop c % v:real^K) <= &1 * norm c * norm v)`,
  REWRITE_TAC[BILINEAR_DROP_MUL; NORM_MUL; REAL_MUL_LID; NORM_1; REAL_LE_REFL]);;

let PDE_ME_PARTIAL_JETS = prove
 (`!(p:real^N->real^1) A m i j.
     (!l y. LENGTH l <= m + 2 /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
            ==> norm(iterated_partial l p y) <= A) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (!l y. LENGTH l <= m /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
                ==> norm(iterated_partial l (partial_derivative i p) y) <= A) /\
         (!l y. LENGTH l <= m /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
                ==> norm(iterated_partial l (partial_derivative i (partial_derivative j p)) y)
                    <= A)`,
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `iterated_partial l (partial_derivative i (p:real^N->real^1)) =
                  iterated_partial (APPEND l [i]) p` SUBST1_TAC THENL
     [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC];
    SUBGOAL_THEN `iterated_partial l (partial_derivative i (partial_derivative j
                    (p:real^N->real^1))) = iterated_partial (APPEND l [i; j]) p`
    SUBST1_TAC THENL
     [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; ALL_APPEND; ALL; LENGTH] THEN ASM_ARITH_TAC);;

(* Jets of a product drop(q) w with q of bounded jets. *)

let PDE_ME_JETN_DROPMUL = prove
 (`!(q:real^N->real^1) (w:real^N->real^K) Aq m x.
     smooth_map_on (:real^N) q /\ smooth_map_on (:real^N) w /\ &0 <= Aq /\
     (!l y. LENGTH l <= m /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
            ==> norm(iterated_partial l q y) <= Aq)
     ==> pde_jetn m (\x. drop(q x) % w x) x <=
         (&(CARD(pde_index_lists m (:N))) * &2 pow m) * Aq * pde_jetn m w x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(c:real^1) (v:real^K). drop c % v`; `&1`; `Aq:real`; `m:num`;
                 `q:real^N->real^1`; `w:real^N->real^K`; `x:real^N`] PDE_ME_JETN_BILINEAR) THEN
  ASM_REWRITE_TAC[PDE_ME_DROPMUL_BILINEAR; REAL_POS] THEN REAL_ARITH_TAC);;

let PDE_ME_COMM_JETN = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) (u:real^N->real^K)
    M Ap m x.
     smooth_map_on (:real^N) (\x. (vectorize:real^N^N->real^(N,N)finite_prod) (A x)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> smooth_map_on (:real^N)
                (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (B x i))) /\
     smooth_map_on (:real^N) p /\ smooth_map_on (:real^N) u /\ &0 <= M /\ &0 <= Ap /\
     (!l y. LENGTH l <= m /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
            ==> norm(iterated_partial l (\x. (vectorize:real^N^N->real^(N,N)finite_prod) (A x))
                       y) <= M /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> norm(iterated_partial l
                               (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (B x i)) y)
                         <= M)) /\
     (!l y. LENGTH l <= m + 2 /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
            ==> norm(iterated_partial l p y) <= Ap)
     ==> pde_jetn m (pde_mt_comm A B p u) x <=
         (&(CARD(pde_index_lists m (:N))) * &2 pow m) pow 2 * Ap * M *
         (&3 * &(dimindex(:N)) pow 2 + &(dimindex(:N))) * pde_jetn (m + 1) u x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Q = &(CARD(pde_index_lists m (:N))) * &2 pow m` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on (:real^N) (partial_derivative i (p:real^N->real^1)) /\
        smooth_map_on (:real^N) (partial_derivative i (u:real^N->real^K)) /\
        !j. smooth_map_on (:real^N) (partial_derivative i (partial_derivative j p))`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. 1 <= i /\ i <= dimindex(:N)
         ==> !l y. LENGTH l <= m /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
                   ==> norm(iterated_partial l (partial_derivative i (p:real^N->real^1)) y)
                       <= Ap) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> !l y. LENGTH l <= m /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
                     ==> norm(iterated_partial l
                                (partial_derivative i (partial_derivative j p)) y) <= Ap)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`p:real^N->real^1`; `Ap:real`; `m:num`; `i:num`; `i:num`]
                    PDE_ME_PARTIAL_JETS);
      MP_TAC(ISPECL [`p:real^N->real^1`; `Ap:real`; `m:num`; `i:num`; `j:num`]
                    PDE_ME_PARTIAL_JETS)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the X_ij terms *)
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on (:real^N)
                (\x. drop(partial_derivative i (p:real^N->real^1) x) %
                     partial_derivative j (u:real^N->real^K) x +
                     drop(partial_derivative j p x) % partial_derivative i u x +
                     drop(partial_derivative i (partial_derivative j p) x) % u x) /\
              pde_jetn m
                (\x. drop(partial_derivative i (p:real^N->real^1) x) %
                     partial_derivative j (u:real^N->real^K) x +
                     drop(partial_derivative j p x) % partial_derivative i u x +
                     drop(partial_derivative i (partial_derivative j p) x) % u x) x
              <= &3 * Q * Ap * pde_jetn (m + 1) u x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^N)
        (\x. drop(partial_derivative i (p:real^N->real^1) x) %
             partial_derivative j (u:real^N->real^K) x) /\
      smooth_map_on (:real^N)
        (\x. drop(partial_derivative j (p:real^N->real^1) x) %
             partial_derivative i (u:real^N->real^K) x) /\
      smooth_map_on (:real^N)
        (\x. drop(partial_derivative i (partial_derivative j (p:real^N->real^1)) x) %
             (u:real^N->real^K) x)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
             TRY CONJ_TAC) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PDE_ME_JETN_ADD o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PDE_ME_JETN_ADD o rand o lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= c /\ d <= &2 * c ==> b <= d ==> a + b <= &3 * c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Q * Ap * pde_jetn m (partial_derivative j (u:real^N->real^K)) x` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Q" THEN MATCH_MP_TAC PDE_ME_JETN_DROPMUL THEN ASM_SIMP_TAC[ETA_AX];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM ADD1] THEN MATCH_MP_TAC PDE_JETN_PARTIAL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= c ==> a + b <= &2 * c`) THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `Q * Ap * pde_jetn m (partial_derivative i (u:real^N->real^K)) x`;
      EXISTS_TAC `Q * Ap * pde_jetn m (u:real^N->real^K) x`] THEN
    (CONJ_TAC THENL
      [EXPAND_TAC "Q" THEN MATCH_MP_TAC PDE_ME_JETN_DROPMUL THEN ASM_SIMP_TAC[ETA_AX];
       MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]) THENL
     [REWRITE_TAC[GSYM ADD1] THEN MATCH_MP_TAC PDE_JETN_PARTIAL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC];
    ALL_TAC] THEN
  (* the terms of the first sum *)
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on (:real^N)
                (\x. (A:real^N->real^N^N) x$i$j %
                     (drop(partial_derivative i (p:real^N->real^1) x) %
                      partial_derivative j (u:real^N->real^K) x +
                      drop(partial_derivative j p x) % partial_derivative i u x +
                      drop(partial_derivative i (partial_derivative j p) x) % u x)) /\
              pde_jetn m
                (\x. (A:real^N->real^N^N) x$i$j %
                     (drop(partial_derivative i (p:real^N->real^1) x) %
                      partial_derivative j (u:real^N->real^K) x +
                      drop(partial_derivative j p x) % partial_derivative i u x +
                      drop(partial_derivative i (partial_derivative j p) x) % u x)) x
              <= Q * M * (&3 * Q * Ap * pde_jetn (m + 1) u x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`\(m:real^(N,N)finite_prod) (v:real^K). (matrify m:real^N^N)$i$j % v`;
                   `&1`; `M:real`; `m:num`;
                   `\x. (vectorize:real^N^N->real^(N,N)finite_prod) ((A:real^N->real^N^N) x)`;
                   `\x. drop(partial_derivative i (p:real^N->real^1) x) %
                        partial_derivative j (u:real^N->real^K) x +
                        drop(partial_derivative j p x) % partial_derivative i u x +
                        drop(partial_derivative i (partial_derivative j p) x) % u x`;
                   `x:real^N`] PDE_ME_JETN_BILINEAR) THEN
    REWRITE_TAC[PDE_ME_ENTRY_BILINEAR; MATRIFY_VECTORIZE; REAL_POS] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "bil") THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^N)`;
                     `\(m:real^(N,N)finite_prod) (v:real^K). (matrify m:real^N^N)$i$j % v`;
                     `\x. (vectorize:real^N^N->real^(N,N)finite_prod) ((A:real^N->real^N^N) x)`;
                     `\x. drop(partial_derivative i (p:real^N->real^1) x) %
                          partial_derivative j (u:real^N->real^K) x +
                          drop(partial_derivative j p x) % partial_derivative i u x +
                          drop(partial_derivative i (partial_derivative j p) x) % u x`]
                    SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[PDE_ME_ENTRY_BILINEAR; MATRIFY_VECTORIZE; OPEN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Q * M * pde_jetn m
                  (\x. drop(partial_derivative i (p:real^N->real^1) x) %
                       partial_derivative j (u:real^N->real^K) x +
                       drop(partial_derivative j p x) % partial_derivative i u x +
                       drop(partial_derivative i (partial_derivative j p) x) % u x) x` THEN
    CONJ_TAC THENL
     [USE_THEN "bil" MP_TAC THEN EXPAND_TAC "Q" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the terms of the second sum *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> smooth_map_on (:real^N)
              (\x. drop(partial_derivative i (p:real^N->real^1) x) %
                   ((B:real^N->num->real^K^K) x i ** (u:real^N->real^K) x)) /\
            pde_jetn m
              (\x. drop(partial_derivative i (p:real^N->real^1) x) %
                   ((B:real^N->num->real^K^K) x i ** (u:real^N->real^K) x)) x
            <= Q * Ap * (Q * M * pde_jetn (m + 1) u x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^N)
        (\x. (B:real^N->num->real^K^K) x i ** (u:real^N->real^K) x)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(:real^N)`;
                     `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                     `\x. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((B:real^N->num->real^K^K) x i)`;
                     `u:real^N->real^K`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[PDE_ME_MATVEC_BILINEAR; MATRIFY_VECTORIZE; OPEN_UNIV; ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Q * Ap * pde_jetn m
                  (\x. (B:real^N->num->real^K^K) x i ** (u:real^N->real^K) x) x` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC PDE_ME_JETN_DROPMUL THEN ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `&1`; `M:real`; `m:num`;
                   `\x. (vectorize:real^K^K->real^(K,K)finite_prod)
                          ((B:real^N->num->real^K^K) x i)`;
                   `u:real^N->real^K`; `x:real^N`] PDE_ME_JETN_BILINEAR) THEN
    REWRITE_TAC[PDE_ME_MATVEC_BILINEAR; MATRIFY_VECTORIZE; REAL_POS] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Q * M * pde_jetn m (u:real^N->real^K) x` THEN CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC];
    ALL_TAC] THEN
  (* assembly *)
  SUBGOAL_THEN
   `pde_mt_comm A B p u =
    (\z. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. (A:real^N->real^N^N) z$i$j %
                       (drop(partial_derivative i (p:real^N->real^1) z) %
                        partial_derivative j (u:real^N->real^K) z +
                        drop(partial_derivative j p z) % partial_derivative i u z +
                        drop(partial_derivative i (partial_derivative j p) z) % u z))) +
         vsum(1..dimindex(:N))
           (\i. drop(partial_derivative i p z) %
                ((B:real^N->num->real^K^K) z i ** u z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_mt_comm]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> smooth_map_on (:real^N)
              (\z. vsum(1..dimindex(:N))
                     (\j. (A:real^N->real^N^N) z$i$j %
                          (drop(partial_derivative i (p:real^N->real^1) z) %
                           partial_derivative j (u:real^N->real^K) z +
                           drop(partial_derivative j p z) % partial_derivative i u z +
                           drop(partial_derivative i (partial_derivative j p) z) % u z))) /\
            pde_jetn m
              (\z. vsum(1..dimindex(:N))
                     (\j. (A:real^N->real^N^N) z$i$j %
                          (drop(partial_derivative i (p:real^N->real^1) z) %
                           partial_derivative j (u:real^N->real^K) z +
                           drop(partial_derivative j p z) % partial_derivative i u z +
                           drop(partial_derivative i (partial_derivative j p) z) % u z))) x
            <= &(dimindex(:N)) * (Q * M * (&3 * Q * Ap * pde_jetn (m + 1) u x))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      ASM_SIMP_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_NUMSEG; ETA_AX];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PDE_ME_JETN_VSUM o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                  (\j:num. Q * M * (&3 * Q * Ap * pde_jetn (m + 1) (u:real^N->real^K) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[ETA_AX];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&(dimindex(:N)) * (&(dimindex(:N)) * (Q * M * (&3 * Q * Ap * pde_jetn (m + 1) u x))) +
    &(dimindex(:N)) * (Q * Ap * (Q * M * pde_jetn (m + 1) (u:real^N->real^K) x))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) PDE_ME_JETN_ADD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      ASM_SIMP_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_NUMSEG; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= d ==> x <= a + b ==> x <= c + d`) THEN
    CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PDE_ME_JETN_VSUM o lhand o snd) THEN
    (ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; ETA_AX]; ALL_TAC]) THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `sum(1..dimindex(:N))
                    (\i:num. &(dimindex(:N)) *
                             (Q * M * (&3 * Q * Ap * pde_jetn (m + 1) (u:real^N->real^K) x)))`;
      EXISTS_TAC `sum(1..dimindex(:N))
                    (\i:num. Q * Ap * (Q * M * pde_jetn (m + 1) (u:real^N->real^K) x))`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[ETA_AX];
       REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* Squares of jets and the H^s norm. *)

let PDE_ME_TERM_LE_JETN = prove
 (`!m (w:real^N->real^K) l x.
     l IN pde_index_lists m (:N) ==> norm(iterated_partial l w x) <= pde_jetn m w x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MP_TAC(ISPECL [`\l:num list. norm(iterated_partial l (w:real^N->real^K) x)`;
                 `pde_index_lists m (:N)`; `l:num list`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> s = t - x ==> x <= t`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN SIMP_TAC[FINITE_DELETE; PDE_INDEX_LISTS_FINITE; NORM_POS_LE]);;

let PDE_ME_JETN_SQ = prove
 (`!m (w:real^N->real^K) x.
     pde_jetn m w x pow 2 <=
     &(CARD(pde_index_lists m (:N))) *
     sum (pde_index_lists m (:N)) (\l. norm(iterated_partial l w x) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MATCH_MP_TAC PDM_SUM_SQUARE_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE]);;

let PDE_ME_SQSUM_SMOOTH = prove
 (`!m (w:real^N->real^K).
     smooth_map_on (:real^N) w
     ==> smooth_map_on (:real^N)
           (\x. lift(sum (pde_index_lists m (:N)) (\l. norm(iterated_partial l w x) pow 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
  ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]);;

let PDE_ME_HS2_SQSUM = prove
 (`!m (w:real^N->real^K).
     smooth_map_on (:real^N) w
     ==> pde_hs2 m w =
         pde_cint (\x. sum (pde_index_lists m (:N)) (\l. norm(iterated_partial l w x) pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_HS2_CINT] THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`\(l:num list) (x:real^N). norm(iterated_partial l (w:real^N->real^K) x) pow 2`;
                 `pde_index_lists m (:N)`] PDE_CINT_SUM) THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
  ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]);;

(* Smoothness of the commutator. *)

let PDE_ME_COMM_SMOOTH = prove
 (`!U (A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) (u:real^N->real^K).
     open U /\ smooth_map_on U (\x. (vectorize:real^N^N->real^(N,N)finite_prod) (A x)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> smooth_map_on U (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (B x i))) /\
     smooth_map_on U p /\ smooth_map_on U u
     ==> smooth_map_on U (pde_mt_comm A B p u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pde_mt_comm A B p u = (\z. pde_mt_comm (A:real^N->real^N^N)
                  (B:real^N->num->real^K^K) (p:real^N->real^1) (u:real^N->real^K) z)`
  SUBST1_TAC THENL [REWRITE_TAC[ETA_AX]; REWRITE_TAC[pde_mt_comm]] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on U (partial_derivative i (p:real^N->real^1)) /\
        smooth_map_on U (partial_derivative i (u:real^N->real^K)) /\
        !j. smooth_map_on U (partial_derivative i (partial_derivative j p))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\(m:real^(N,N)finite_prod) (v:real^K). (matrify m:real^N^N)$i$j % v`;
                   `\x. (vectorize:real^N^N->real^(N,N)finite_prod) ((A:real^N->real^N^N) x)`;
                   `\x. drop(partial_derivative i (p:real^N->real^1) x) %
                        partial_derivative j (u:real^N->real^K) x +
                        drop(partial_derivative j p x) % partial_derivative i u x +
                        drop(partial_derivative i (partial_derivative j p) x) % u x`]
                  SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    REWRITE_TAC[PDE_ME_ENTRY_BILINEAR; MATRIFY_VECTORIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\x. (vectorize:real^K^K->real^(K,K)finite_prod)
                          ((B:real^N->num->real^K^K) x i)`;
                   `u:real^N->real^K`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[PDE_ME_MATVEC_BILINEAR; MATRIFY_VECTORIZE; ETA_AX]]);;

(* The torus bound: H^s of the commutator by H^(s+1). *)

let PDE_ME_COMM_TORUS_BOUND = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc
    (p:real^N->real^1) T1 s.
     pde_tcoeff tmax lam aa bb cc /\ &0 <= T1 /\ T1 < tmax /\
     smooth_map_on (:real^N) p /\ pde_zper p
     ==> ?C. &0 <= C /\
             !t (u:real^N->real^K).
               &0 <= t /\ t <= T1 /\ smooth_map_on (:real^N) u
               ==> pde_hs2 s (pde_mt_comm (aa t) (bb t) p u) <= C * pde_hs2 (s + 1) u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam:real`; `aa:real->real^N->real^N^N`;
                 `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`;
                 `T1:real`; `s:num`] PDE_TCOEFF_FCOEFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  MP_TAC(ISPECL [`p:real^N->real^1`; `s + 2`] PDE_ZPER_JET_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ap:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[pde_fcoeff; pde_fbnd] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = (&(CARD(pde_index_lists s (:N))) * &2 pow s) pow 2 * Ap * M *
                  (&3 * &(dimindex(:N)) pow 2 + &(dimindex(:N)))` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_ADD; REAL_LE_MUL; REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists s (:N))) * K pow 2 *
              &(CARD(pde_index_lists (s + 1) (:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `u:real^N->real^K`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pde_fcoeff; pde_fbnd] THEN STRIP_TAC THEN
  ABBREV_TAC `w = pde_mt_comm ((aa:real->real^N->real^N^N) t)
                    ((bb:real->real^N->num->real^K^K) t) p (u:real^N->real^K)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (w:real^N->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC PDE_ME_COMM_SMOOTH THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. pde_jetn s (w:real^N->real^K) x <= K * pde_jetn (s + 1) (u:real^N->real^K) x`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "w" THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC PDE_ME_COMM_JETN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [PDE_HS2_CINT] THEN
  MP_TAC(ISPECL [`s + 1`; `u:real^N->real^K`] PDE_ME_HS2_SQSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists s (:N))
                (\l:num list. pde_cint (\x. K pow 2 * &(CARD(pde_index_lists (s + 1) (:N))) *
                   sum (pde_index_lists (s + 1) (:N))
                     (\l. norm(iterated_partial l (u:real^N->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_CINT_LE THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
      ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      ASM_SIMP_TAC[OPEN_UNIV; PDE_ME_SQSUM_SMOOTH];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(K * pde_jetn (s + 1) (u:real^N->real^K) x) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn s (w:real^N->real^K) x` THEN
        ASM_SIMP_TAC[PDE_ME_TERM_LE_JETN];
        REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; PDE_ME_JETN_SQ]]];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`K pow 2 * &(CARD(pde_index_lists (s + 1) (:N)))`;
                 `\x. sum (pde_index_lists (s + 1) (:N))
                        (\l. norm(iterated_partial l (u:real^N->real^K) x) pow 2)`]
                PDE_CINT_CMUL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[PDE_ME_SQSUM_SMOOTH]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]);;

(* ========================================================================= *)
(* The commutator under the dilation and under transplants.  If the torus    *)
(* coefficients agree with lam^-2 A, lam^-1 B near the support of the        *)
(* cutoff, the transplant of the chart commutator [L,psi] W is the torus     *)
(* commutator of the transplants of psi and of a smooth F equal to W near    *)
(* the support.                                                              *)
(* ========================================================================= *)

let PDE_ME_COMM_DILATE = prove
 (`!lam (AT:real^N->real^N^N) (BT:real^N->num->real^K^K) (pT:real^N->real^1)
    (wT:real^N->real^K) (A:real^N->real^N^N) (B:real^N->num->real^K^K) z.
     smooth_map_on (:real^N) pT /\ smooth_map_on (:real^N) wT /\
     AT (inv lam % z + inv(&2) % vec 1) = inv(lam pow 2) %% A z /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> BT (inv lam % z + inv(&2) % vec 1) i = inv lam %% B z i)
     ==> pde_mt_comm AT BT pT wT (inv lam % z + inv(&2) % vec 1) =
         pde_mt_comm A B (\z. pT(inv lam % z + inv(&2) % vec 1))
                         (\z. wT(inv lam % z + inv(&2) % vec 1)) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mt_comm] THEN
  MP_TAC(GEN `l:num list`
    (ISPECL [`l:num list`; `pT:real^N->real^1`; `inv lam`; `inv(&2) % vec 1:real^N`]
            PDM_ITERATED_PARTIAL_AFFINE)) THEN
  MP_TAC(GEN `l:num list`
    (ISPECL [`l:num list`; `wT:real^N->real^K`; `inv lam`; `inv(&2) % vec 1:real^N`]
            PDM_ITERATED_PARTIAL_AFFINE)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(!i. partial_derivative i (\z. (pT:real^N->real^1) (inv lam % z + inv(&2) % vec 1)) z =
         inv lam % partial_derivative i pT (inv lam % z + inv(&2) % vec 1)) /\
    (!i j. partial_derivative i (partial_derivative j
             (\z. (pT:real^N->real^1) (inv lam % z + inv(&2) % vec 1))) z =
           inv(lam pow 2) %
           partial_derivative i (partial_derivative j pT) (inv lam % z + inv(&2) % vec 1)) /\
    (!i. partial_derivative i (\z. (wT:real^N->real^K) (inv lam % z + inv(&2) % vec 1)) z =
         inv lam % partial_derivative i wT (inv lam % z + inv(&2) % vec 1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`[i:num]`; `z:real^N`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`[i:num; j:num]`; `z:real^N`]);
      FIRST_ASSUM(MP_TAC o SPECL [`[i:num]`; `z:real^N`] o
                  check (fun th -> can (find_term ((=) `wT:real^N->real^K`)) (concl th)))] THEN
    REWRITE_TAC[iterated_partial; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1; REAL_POW_INV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(VECTOR_ARITH `s1:real^K = s1' /\ s2 = s2' ==> s1 + s2 = s1' + s2'`) THEN
  CONJ_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT; DROP_CMUL; VECTOR_MUL_ASSOC;
                VECTOR_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN
    BINOP_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[MATRIX_VECTOR_LMUL; DROP_CMUL; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let PDE_ME_COMM_LOCAL = prove
 (`!S (A:real^N->real^N^N) (B:real^N->num->real^K^K) (p1:real^N->real^1) p2
    (w1:real^N->real^K) w2 z.
     open S /\ z IN S /\ (!y. y IN S ==> p1 y = p2 y) /\ (!y. y IN S ==> w1 y = w2 y)
     ==> pde_mt_comm A B p1 w1 z = pde_mt_comm A B p2 w2 z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!l. iterated_partial l (p1:real^N->real^1) z = iterated_partial l p2 z) /\
    (!l. iterated_partial l (w1:real^N->real^K) z = iterated_partial l w2 z)`
  MP_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th ->
    MP_TAC(GEN `i:num` (SPEC `[i:num]` th)) THEN
    MP_TAC(GEN `i:num` (GEN `j:num` (SPEC `[i:num; j:num]` th))) THEN
    MP_TAC(SPEC `[]:num list` th))) THEN
  REWRITE_TAC[iterated_partial] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[pde_mt_comm]);;

let PDE_ME_COMM_COEFF_AT = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) A' B' (p:real^N->real^1) w z.
     A z = A' z /\ (!i. 1 <= i /\ i <= dimindex(:N) ==> B z i = B' z i)
     ==> pde_mt_comm A B p w z = pde_mt_comm A' B' p w z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mt_comm] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]);;

let PDE_ME_COMM_ZPER = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) (w:real^N->real^K).
     pde_zper A /\ (!i. pde_zper (\x. B x i)) /\
     smooth_map_on (:real^N) p /\ pde_zper p /\ smooth_map_on (:real^N) w /\ pde_zper w
     ==> pde_zper (pde_mt_comm A B p w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_zper] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l. iterated_partial l (p:real^N->real^1) (x + basis k) = iterated_partial l p x /\
        iterated_partial l (w:real^N->real^K) (x + basis k) = iterated_partial l w x`
  MP_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`l:num list`; `p:real^N->real^1`] PDE_ZPER_ITERATED_PARTIAL);
      MP_TAC(ISPECL [`l:num list`; `w:real^N->real^K`] PDE_ZPER_ITERATED_PARTIAL)] THEN
    ASM_REWRITE_TAC[pde_zper] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(GEN `i:num` (SPEC `[i:num]` th)) THEN
    MP_TAC(GEN `i:num` (GEN `j:num` (SPEC `[i:num; j:num]` th))) THEN
    MP_TAC(SPEC `[]:num list` th)) THEN
  REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN ASM_SIMP_TAC[pde_mt_comm]);;

let PDE_ME_TRANSPLANT_COMM = prove
 (`!lam (AT:real^N->real^N^N) (BT:real^N->num->real^K^K) (A:real^N->real^N^N)
    (B:real^N->num->real^K^K) V U0 O (psi:real^N->real) Lp (W:real^N->real^K) FF.
     &0 < lam /\
     (!z. z IN V
          ==> AT (inv lam % z + inv(&2) % vec 1) = inv(lam pow 2) %% A z /\
              (!i. 1 <= i /\ i <= dimindex(:N)
                   ==> BT (inv lam % z + inv(&2) % vec 1) i = inv lam %% B z i)) /\
     pde_zper AT /\ (!i. pde_zper (\x. BT x i)) /\
     open U0 /\ open O /\ Lp SUBSET O /\ O SUBSET U0 /\ compact Lp /\ Lp SUBSET V /\
     Lp SUBSET ball(vec 0,lam / &4) /\
     smooth_map_on (:real^N) (\z. lift(psi z)) /\ (!z. ~(z IN Lp) ==> psi z = &0) /\
     smooth_map_on (:real^N) FF /\ (!z. lam / &4 < norm z ==> FF z = vec 0) /\
     (!z. z IN O ==> W z = FF z)
     ==> !x. pdm_transplant lam
               (\z. if z IN U0 then pde_mt_comm A B (\z. lift(psi z)) W z else vec 0) x =
             pde_mt_comm AT BT (pdm_transplant lam (\z. lift(psi z)))
                         (pdm_transplant lam FF) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "agr")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open((:real^N) DIFF Lp)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. ~(z IN Lp) ==> lift((psi:real^N->real) z) = vec 0` ASSUME_TAC
  THENL [ASM_SIMP_TAC[LIFT_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(A1:real^N->real^N^N) (B1:real^N->num->real^K^K) (w:real^N->real^K) z.
      ~(z IN Lp) ==> pde_mt_comm A1 B1 (\z. lift((psi:real^N->real) z)) w z = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN
    EXISTS_TAC `(:real^N) DIFF Lp` THEN ASM_SIMP_TAC[IN_DIFF; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. lam / &4 < norm z ==> ~(z IN Lp)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `(Lp:real^N->bool) SUBSET ball(vec 0,lam / &4)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (pdm_transplant lam (\z. lift((psi:real^N->real) z))) /\
    pde_zper (pdm_transplant lam (\z. lift((psi:real^N->real) z))) /\
    smooth_map_on (:real^N) (pdm_transplant lam (FF:real^N->real^K)) /\
    pde_zper (pdm_transplant lam (FF:real^N->real^K))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PDM_TRANSPLANT_ZPER] THEN CONJ_TAC THEN
    MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* reduction to the unit cube *)
  SUBGOAL_THEN
   `!y. y IN interval[vec 0,vec 1]
        ==> pdm_transplant lam
              (\z. if z IN U0 then pde_mt_comm (A:real^N->real^N^N) (B:real^N->num->real^K^K)
                                     (\z. lift((psi:real^N->real) z)) (W:real^N->real^K) z
                   else vec 0) y =
            pde_mt_comm (AT:real^N->real^N^N) (BT:real^N->num->real^K^K)
              (pdm_transplant lam (\z. lift(psi z))) (pdm_transplant lam FF) y`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:real^N` THEN MP_TAC(ISPEC `x:real^N` PDE_MT_FRAC_DECOMP) THEN
    ABBREV_TAC `y:real^N = pdm_frac x` THEN ABBREV_TAC `m:real^N = pdm_floorv x` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `(a:real^K) = a' /\ b = b' ==> a' = b' ==> a = b`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `x:real^N`)) THEN
    CONJ_TAC THEN MATCH_MP_TAC PDE_ZPER_INTEGER THEN ASM_REWRITE_TAC[PDM_TRANSPLANT_ZPER] THEN
    MATCH_MP_TAC PDE_ME_COMM_ZPER THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lam:real`; `y:real^N`] PDE_MT_DILATE_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lam:real` PDE_MT_DILATE_OPEN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `y IN interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[PDE_MT_CUBE_IN_BOX]; ALL_TAC] THEN
  ABBREV_TAC `z0:real^N = lam % (y - inv(&2) % vec 1)` THEN
  (* the left side *)
  MP_TAC(ISPECL [`lam:real`;
                 `\z. if z IN U0 then pde_mt_comm (A:real^N->real^N^N)
                                        (B:real^N->num->real^K^K)
                                        (\z. lift((psi:real^N->real) z)) (W:real^N->real^K) z
                      else vec 0`; `y:real^N`] PDM_TRANSPLANT_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  (* the right side: dilation with the torus coefficients, then locality *)
  SUBGOAL_THEN `y:real^N = inv lam % z0 + inv(&2) % vec 1` SUBST1_TAC THENL
   [EXPAND_TAC "z0" THEN ASM_SIMP_TAC[PDE_MT_DILATE_INV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `AT:real^N->real^N^N`; `BT:real^N->num->real^K^K`;
                 `pdm_transplant lam (\z. lift((psi:real^N->real) z))`;
                 `pdm_transplant lam (FF:real^N->real^K)`;
                 `\z:real^N. lam pow 2 %% (AT:real^N->real^N^N) (inv lam % z + inv(&2) % vec 1)`;
                 `\(z:real^N) (i:num). lam %%
                    (BT:real^N->num->real^K^K) (inv lam % z + inv(&2) % vec 1) i`;
                 `z0:real^N`] PDE_ME_COMM_DILATE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_POW_NZ; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
    DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `Z = IMAGE (\x:real^N. lam % x + --(lam % inv(&2) % vec 1))
                        (interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1))` THEN
  SUBGOAL_THEN `(z0:real^N) IN Z` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`Z:real^N->bool`;
    `\z:real^N. lam pow 2 %% (AT:real^N->real^N^N) (inv lam % z + inv(&2) % vec 1)`;
    `\(z:real^N) (i:num). lam %% (BT:real^N->num->real^K^K) (inv lam % z + inv(&2) % vec 1) i`;
    `\z. pdm_transplant lam (\z. lift((psi:real^N->real) z)) (inv lam % z + inv(&2) % vec 1)`;
    `\z. lift((psi:real^N->real) z)`;
    `\z. pdm_transplant lam (FF:real^N->real^K) (inv lam % z + inv(&2) % vec 1)`;
    `FF:real^N->real^K`; `z0:real^N`] PDE_ME_COMM_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    (SUBGOAL_THEN
      `inv lam % z + inv(&2) % vec 1 IN
       interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    MP_TAC(ISPECL [`lam:real`; `z:real^N`] PDE_MT_DILATE_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) PDM_TRANSPLANT_EQ (lhand w))) THEN
    (ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);
    DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `(z0:real^N) IN Lp` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[COND_ID]] THEN
  SUBGOAL_THEN `(z0:real^N) IN U0 /\ z0 IN O /\ z0 IN V` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "agr" (MP_TAC o SPEC `z0:real^N`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
    `\z:real^N. lam pow 2 %% (AT:real^N->real^N^N) (inv lam % z + inv(&2) % vec 1)`;
    `\(z:real^N) (i:num). lam %% (BT:real^N->num->real^K^K) (inv lam % z + inv(&2) % vec 1) i`;
    `\z. lift((psi:real^N->real) z)`; `FF:real^N->real^K`; `z0:real^N`]
   PDE_ME_COMM_COEFF_AT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_RINV; REAL_POW_NZ; REAL_LT_IMP_NZ;
                 MATRIX_CMUL_LID];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC PDE_ME_COMM_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Chart norms with a cutoff (pde_me_cnorm, one term of pde_mnorm2), their   *)
(* expression by zero extensions, continuity in time, differences of H^s     *)
(* norms, time shifts of real integrals, and auxiliary cutoffs equal to 1    *)
(* near a chart piece.                                                       *)
(* ========================================================================= *)

let pde_me_cnorm = new_definition
 `pde_me_cnorm (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
               (phi:A->real) (s:num) (v:A->real^N^N) =
    sum (pde_index_lists s (:N))
      (\l. drop(integral (IMAGE (SND c) (FST c))
             (\y. lift(norm(iterated_partial l
                    (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                         (phi (chart_inv c z) %% metric_local atlas c v z)) y) pow 2))))`;;

let PDE_ME_MNORM2_CNORM = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) n0 cs psi s v.
     pde_mnorm2 atlas n0 cs psi s v =
     sum {i | i < n0} (\i. pde_me_cnorm atlas (cs i) (psi i) s v)`,
  REWRITE_TAC[pde_mnorm2; pde_me_cnorm]);;

(* The chart representative of a cutoff, extended by zero. *)

let PDE_ME_CUTOFF_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) k.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact k /\ k SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) k)
     ==> smooth_map_on (:real^N)
           (\z. lift(if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0)) /\
         (!z. ~(z IN k)
              ==> (if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z:real^N. z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\ ~(z IN k)
               ==> (phi:A->real) (chart_inv c z) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o ONCE_REWRITE_RULE
      [TAUT `(~p ==> q) <=> (~q ==> p)`]) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^N) = y` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift(if z IN IMAGE (SND c) (FST c) then (phi:A->real)(chart_inv c z) else &0)) =
      (\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
           then ((\x. lift(phi x)) o chart_inv c) z else vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[LIFT_NUM];
      ALL_TAC] THEN
    MATCH_MP_TAC PDM_ZERO_EXT_SMOOTH THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[mfd_smooth]) THEN ASM_SIMP_TAC[ETA_AX];
      ASM_SIMP_TAC[o_THM; LIFT_NUM]];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* Chart norms as integrals over R^N of zero extensions. *)

let PDE_ME_CNORM_ZEROEXT = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) k (v:A->real^N^N) s.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact k /\ k SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) k) /\ pde_tensor_smooth atlas v
     ==> pde_me_cnorm atlas c phi s v =
         sum (pde_index_lists s (:N))
           (\l. drop(integral (:real^N)
                  (\y. lift(norm(iterated_partial l
                     (\z. if z IN IMAGE (SND c) (FST c)
                          then (if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0) %
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                                 (metric_local atlas c v z)
                          else vec 0) y) pow 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_me_cnorm] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `v:A->real^N^N`;
                 `k:real^N->bool`] PDM_CHART_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `k:real^N->bool`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((phi:A->real) (chart_inv (c:(A->bool)#(A->real^N)) z) %%
                       metric_local atlas c (v:A->real^N^N) z)`; `l:num list`]
                PDM_ZERO_EXT_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTORIZE_CMUL]);;

(* H^s norms of differences, transplants of differences. *)

let PDE_ME_HS2_SUB = prove
 (`!s (f:real^N->real^K) g.
     smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g
     ==> pde_hs2 s (\x. f x - g x) <= &2 * pde_hs2 s f + &2 * pde_hs2 s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_HS2_CINT; GSYM SUM_LMUL] THEN
  REWRITE_TAC[GSYM(MATCH_MP SUM_ADD (SPEC_ALL PDE_INDEX_LISTS_FINITE))] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (\x. lift(norm(iterated_partial l (f:real^N->real^K) x) pow 2)) /\
    smooth_map_on (:real^N) (\x. lift(norm(iterated_partial l (g:real^N->real^K) x) pow 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM PDE_CINT_CMUL; GSYM PDE_CINT_ADD; SMOOTH_MAP_ON_CMUL_OPEN; OPEN_UNIV;
               LIFT_CMUL; SMOOTH_MAP_ON_ADD_OPEN; LIFT_ADD] THEN
  MATCH_MP_TAC PDE_CINT_LE THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_SUB_OPEN];
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CMUL_OPEN];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:num list`; `(:real^N)`; `f:real^N->real^K`; `g:real^N->real^K`]
                  TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(norm(iterated_partial l (f:real^N->real^K) x) +
                 norm(iterated_partial l (g:real^N->real^K) x)) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN NORM_ARITH_TAC;
      MP_TAC(SPEC `norm(iterated_partial l (f:real^N->real^K) x) -
                   norm(iterated_partial l (g:real^N->real^K) x)` REAL_LE_SQUARE) THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]]);;

let PDE_ME_TRANSPLANT_SUB = prove
 (`!lam (g1:real^N->real^K) g2.
     pdm_transplant lam (\z. g1 z - g2 z) =
     (\x. pdm_transplant lam g1 x - pdm_transplant lam g2 x)`,
  REWRITE_TAC[FUN_EQ_THM; pdm_transplant; pdm_periodize]);;

(* Shifts of real integrals. *)

let PDE_ME_RINT_SHIFT = prove
 (`!(g:real->real) a t.
     a <= t /\ g real_continuous_on real_interval[a,t]
     ==> real_integral (real_interval[&0,t - a]) (\r. g(r + a)) =
         real_integral (real_interval[a,t]) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g has_real_integral real_integral (real_interval[a,t]) g)
                  (real_interval[a,t])` MP_TAC THENL
   [REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `a:real`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_AFFINITY)) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ; REAL_ABS_NUM; REAL_INV_1; REAL_MUL_LID] THEN
  SUBGOAL_THEN `IMAGE (\x. x - a) (real_interval[a,t]) = real_interval[&0,t - a]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN X_GEN_TAC `y:real` THEN
    EQ_TAC THENL [STRIP_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    EXISTS_TAC `y + a:real` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE));;

(* Cutoffs on M equal to 1 near a chart piece. *)

let PDE_ME_THETA_EXISTS = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) k.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ c IN atlas /\
     compact k /\ k SUBSET IMAGE (SND c) (FST c)
     ==> ?theta:A->real kt O.
           mfd_smooth atlas (\x. lift(theta x)) /\
           compact kt /\ kt SUBSET IMAGE (SND c) (FST c) /\
           (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv c) kt) /\
           open O /\ k SUBSET O /\ O SUBSET IMAGE (SND c) (FST c) /\
           (!z. z IN O ==> theta(chart_inv c z) = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(FST (c:(A->bool)#(A->real^N)),SND c) IN atlas` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `k:real^N->bool`] MFDC_CHART_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `{x:A | x IN FST(c:(A->bool)#(A->real^N)) /\ SND c x IN k}`;
                 `FST(c:(A->bool)#(A->real^N))`] MFD_SMOOTH_CUTOFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `V:A->bool`
    (X_CHOOSE_THEN `L:A->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `\x:A. if x IN topspace top then chi x else &0` THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) L` THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER V)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* smoothness *)
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(chi x))` THEN
    REWRITE_TAC[mfd_smooth] THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(MATCH_MP th (ASSUME
      `(c':(A->bool)#(A->real^N)) IN (atlas:((A->bool)#(A->real^N))->bool)`))) THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(\x. lift((chi:A->real) x)) o chart_inv (c':(A->bool)#(A->real^N))` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c':(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c':(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c':(A->bool)#(A->real^N)) z IN topspace top`
      (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    (* compactness of the image of L *)
    MATCH_MP_TAC PDM_CHART_IMAGE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    (* support *)
    X_GEN_TAC `x:A` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN L` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_DIFF]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) x` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM SET_TAC[]];
    (* openness *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `V:A->bool`] MFDR_RESTRICT_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[];
    (* k inside *)
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) z` THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `V:A->bool`)) (concl th) &&
      not (can (find_term ((=) `chi:A->real`)) (concl th)))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    SET_TAC[];
    (* theta = 1 on O *)
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Continuity in time of chart norms of pde_tfam_from families with a        *)
(* cutoff.                                                                   *)
(* ========================================================================= *)

let PDE_ME_CUT_UPTO = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) kp a b (v:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) kp) /\ pde_tfam_from atlas a b v
     ==> pde_upto a b (:real^N)
           (\t z. if z IN IMAGE (SND c) (FST c)
                  then (if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0) %
                       (vectorize:real^N^N->real^(N,N)finite_prod)
                         (metric_local atlas c (v t) z)
                  else vec 0) /\
         (!t z. ~(z IN kp)
                ==> (if z IN IMAGE (SND c) (FST c)
                     then (if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0) %
                          (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas c (v t) z)
                     else vec 0) = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `kp:real^N->bool`]
                PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vanish")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                   `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (c:(A->bool)#(A->real^N))
                               ((v:real->A->real^N^N) t) y)`;
                   `\z. if z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)
                        then (phi:A->real)(chart_inv c z) else &0`;
                   `kp:real^N->bool`] PDM_UPTO_CUTOFF_EXT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PDM_TFAM_FROM_UPTO]) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "vanish" (MP_TAC o SPEC `z:real^N`) THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

let PDE_ME_CNORM_CONT = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) kp a b b' (v:real->A->real^N^N) s.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) kp) /\
     pde_tfam_from atlas a b v /\ b' < b
     ==> (\r. pde_me_cnorm atlas c phi s (v r)) real_continuous_on real_interval[a,b']`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `kp:real^N->bool` COMPACT_IMP_BOUNDED) THEN
  ASM_REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `kp:real^N->bool`;
                 `a:real`; `b:real`; `v:real->A->real^N^N`] PDE_ME_CUT_UPTO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\r. sum (pde_index_lists s (:N))
          (\l. drop(integral (:real^N)
                 (\y. lift(norm(iterated_partial l
                    (\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                         then (if z IN IMAGE (SND c) (FST c)
                               then (phi:A->real)(chart_inv c z) else &0) %
                              (vectorize:real^N^N->real^(N,N)finite_prod)
                                (metric_local atlas c ((v:real->A->real^N^N) r) z)
                         else vec 0) y) pow 2))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_ME_CNORM_ZEROEXT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `kp:real^N->bool`] THEN
    ASM_REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `b':real`;
                 `\t z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                        then (if z IN IMAGE (SND c) (FST c)
                              then (phi:A->real)(chart_inv c z) else &0) %
                             (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c ((v:real->A->real^N^N) t) z)
                        else vec 0`;
                 `R:real`; `l:num list`] PDE_ME_CHART_NORM_CONT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[REAL_NOT_LE]);;

(* ========================================================================= *)
(* The energy inequality in one chart.  For a solution v with zero initial   *)
(* data, the chart norm of psi v at order s+1 is bounded by the time         *)
(* integral of the chart norms of psi f (order s) and of theta v (order      *)
(* s+1), theta = 1 near the support of psi: the transplant of psi v solves   *)
(* the torus equation with forcing the transplant of                         *)
(* psi f - [L,psi] v (PDE_MT_TRANS_TSOL), the torus energy estimate          *)
(* (PDE_TORUS_ENERGY), the transplanted commutator (PDE_ME_TRANSPLANT_COMM)  *)
(* and its torus bound (PDE_ME_COMM_TORUS_BOUND).                            *)
(* ========================================================================= *)

(* Zero initial data in charts. *)

let PDE_ME_CHART_ZERO = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (w:A->real^N^N) z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     (!x. x IN topspace top ==> w x = mat 0) /\ z IN IMAGE (SND c) (FST c)
     ==> metric_local atlas c w z = mat 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN `(w:A->real^N^N) (chart_inv (c:(A->bool)#(A->real^N)) z) = mat 0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO]]);;

(* The static data of one chart: dilation, torus coefficients, constants. *)

let PDE_ME_CE_STATIC = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (psi:A->real) kp kt a b b'
    (k:real->A->real^N^N) h s.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b' /\ b' < b /\
     mfd_smooth atlas (\x. lift(psi x)) /\ compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(psi x = &0) ==> x IN IMAGE (chart_inv c) kp) /\
     compact kt /\ kt SUBSET IMAGE (SND c) (FST c)
     ==> ?lam b'' (aaT:real->real^N->real^N^N)
          (bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) ccT lamT V C1 C2.
           &1 <= lam /\ b' < b'' /\ b'' < b /\
           kp UNION kt SUBSET ball(vec 0,lam / &4) /\
           pde_tcoeff (b'' - a) lamT aaT bbT ccT /\
           open V /\ kp UNION kt SUBSET V /\ V SUBSET IMAGE (SND c) (FST c) /\
           (!t z. a <= t /\ t < b'' /\ z IN V
                  ==> aaT (t - a) (inv lam % z + inv(&2) % vec 1) =
                      inv(lam pow 2) %% pde_mlaa atlas c k t z /\
                      (!i. 1 <= i /\ i <= dimindex(:N)
                           ==> bbT (t - a) (inv lam % z + inv(&2) % vec 1) i =
                               inv lam %% pde_mlbt atlas c k h t z i) /\
                      ccT (t - a) (inv lam % z + inv(&2) % vec 1) = pde_mlct atlas c k h t z) /\
           &0 <= C1 /\
           (!f u. pde_upto (&0) (b'' - a) (:real^N) f /\ (!t. pde_zper (f t)) /\
                  pde_tsol (b'' - a) aaT bbT ccT f (\y. vec 0) u
                  ==> !t. &0 <= t /\ t <= b' - a
                          ==> pde_hs2 (s + 1) (u t) <=
                              C1 * real_integral (real_interval[&0,t])
                                                 (\r. pde_hs2 s (f r))) /\
           &0 <= C2 /\
           (!t (w:real^N->real^(N,N)finite_prod).
              &0 <= t /\ t <= b' - a /\ smooth_map_on (:real^N) w
              ==> pde_hs2 s
                    (pde_mt_comm (aaT t) (bbT t)
                       (pdm_transplant lam
                          (\z. lift(if z IN IMAGE (SND c) (FST c)
                                    then psi(chart_inv c z) else &0))) w)
                  <= C2 * pde_hs2 (s + 1) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `kp UNION kt:real^N->bool` COMPACT_IMP_BOUNDED) THEN
  ASM_SIMP_TAC[COMPACT_UNION; BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `lam = &4 * (abs R + &1)` THEN
  SUBGOAL_THEN `&1 <= lam /\ kp UNION kt SUBSET ball(vec 0:real^N,lam / &4)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `b'' = (b' + b) / &2` THEN
  SUBGOAL_THEN `b' < b'' /\ b'' < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b''" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b'':real`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                 `c:(A->bool)#(A->real^N)`; `kp UNION kt:real^N->bool`; `lam:real`]
                PDE_MT_TORUS_COEFF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `aaT:real->real^N->real^N^N` (X_CHOOSE_THEN
    `bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod` (X_CHOOSE_THEN
    `ccT:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod` (X_CHOOSE_THEN `lamT:real`
    (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`b'' - a:real`; `lamT:real`; `aaT:real->real^N->real^N^N`;
                 `bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `b' - a:real`; `s:num`] PDE_TORUS_ENERGY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`]
                PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b'' - a:real`; `lamT:real`; `aaT:real->real^N->real^N^N`;
                 `bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `pdm_transplant lam
                    (\z. lift(if z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)
                              then (psi:A->real)(chart_inv c z) else &0))`;
                 `b' - a:real`; `s:num`] PDE_ME_COMM_TORUS_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PDM_TRANSPLANT_ZPER] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((z:real^N) IN kp)` (fun th -> ASM_SIMP_TAC[th; LIFT_NUM]) THEN
    DISCH_TAC THEN UNDISCH_TAC `kp UNION kt SUBSET ball(vec 0:real^N,lam / &4)` THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC
   [`lam:real`; `b'':real`; `aaT:real->real^N->real^N^N`;
    `bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
    `ccT:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
    `lamT:real`; `V:real^N->bool`; `max C0 (&0)`; `C2:real`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
   (REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:real->real^N->real^(N,N)finite_prod`;
                                  `u:real->real^N->real^(N,N)finite_prod`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x * i <= y * i ==> p <= x * i ==> p <= y * i`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN EXISTS_TAC `b'' - a:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN
      EXISTS_TAC `b'' - a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]));;

(* Shifting and restricting pde_upto families. *)

let PDE_ME_UPTO_SHIFT_SUB = prove
 (`!a b b'' (U:real^N->bool) (g:real->real^N->real^K).
     open U /\ pde_upto a b U g /\ b'' <= b
     ==> pde_upto (&0) (b'' - a) U (\r z. g (r + a) z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN
  EXISTS_TAC `b - a:real` THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`; `g:real->real^N->real^K`; `a:real`]
                PDE_MT_UPTO_SHIFT) THEN
  ASM_SIMP_TAC[REAL_SUB_REFL; ETA_AX]);;

(* The transplanted forcing is pde_upto and periodic. *)

let PDE_ME_GG_UPTO = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (psi:A->real) kp (theta:A->real) kt O a b b''
    (k:real->A->real^N^N) h (v:real->A->real^N^N) (f:real->A->real^N^N) lam.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b'' /\ b'' < b /\
     mfd_smooth atlas (\x. lift(psi x)) /\ compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(psi x = &0) ==> x IN IMAGE (chart_inv c) kp) /\
     mfd_smooth atlas (\x. lift(theta x)) /\ compact kt /\ kt SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv c) kt) /\
     open O /\ kp SUBSET O /\ O SUBSET IMAGE (SND c) (FST c) /\
     (!z. z IN O ==> theta(chart_inv c z) = &1) /\
     &0 < lam /\ kp SUBSET ball(vec 0,lam / &4) /\
     pde_tfam_from atlas a b v /\ pde_tfam_from atlas a b f
     ==> pde_upto (&0) (b'' - a) (:real^N)
           (\r. pdm_transplant lam
              (\z. if z IN IMAGE (SND c) (FST c)
                   then (if z IN IMAGE (SND c) (FST c) then psi(chart_inv c z) else &0) %
                        (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas c (f (r + a)) z) -
                        pde_mt_comm (pde_mlaa atlas c k (r + a)) (pde_mlbt atlas c k h (r + a))
                          (\z. lift(if z IN IMAGE (SND c) (FST c)
                                    then psi(chart_inv c z) else &0))
                          (\z. vectorize(metric_local atlas c (v (r + a)) z)) z
                   else vec 0)) /\
         (!r. pde_zper
               (pdm_transplant lam
                 (\z. if z IN IMAGE (SND c) (FST c)
                      then (if z IN IMAGE (SND c) (FST c) then psi(chart_inv c z) else &0) %
                           (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas c (f (r + a)) z) -
                           pde_mt_comm (pde_mlaa atlas c k (r + a))
                             (pde_mlbt atlas c k h (r + a))
                             (\z. lift(if z IN IMAGE (SND c) (FST c)
                                       then psi(chart_inv c z) else &0))
                             (\z. vectorize(metric_local atlas c (v (r + a)) z)) z
                      else vec 0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[PDM_TRANSPLANT_ZPER] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`]
                PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "psiz")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `theta:A->real`; `kt:real^N->bool`]
                PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "thetaz")) THEN
  (* the shifted chart families *)
  SUBGOAL_THEN
   `!(w:real->A->real^N^N).
      pde_tfam_from atlas a b w
      ==> pde_upto (&0) (b'' - a) (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
            (\r z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (metric_local atlas (c:(A->bool)#(A->real^N)) (w (r + a)) z))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN
    EXISTS_TAC `b - a:real` THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`;
                   `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (c:(A->bool)#(A->real^N))
                               ((w:real->A->real^N^N) t) z)`; `a:real`] PDE_MT_UPTO_SHIFT) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PDM_TFAM_FROM_UPTO]) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                PDE_MT_CHART_COEFF_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  (* the commutator family on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) *)
  SUBGOAL_THEN
   `pde_upto (&0) (b'' - a) (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
      (\r z. pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (r + a))
               (pde_mlbt atlas c k (h:A->real^N^N) (r + a))
               (\z. lift(if z IN (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) then (psi:A->real)(chart_inv c z) else &0))
               (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas c ((v:real->A->real^N^N) (r + a)) z)) z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&0`; `b'' - a:real`; `(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`;
                   `\r. pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (r + a)`;
                   `\r. pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)
                          (h:A->real^N^N) (r + a)`;
                   `\z. lift(if z IN (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) then (psi:A->real)(chart_inv
                          (c:(A->bool)#(A->real^N)) z) else &0)`;
                   `\r z. (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (c:(A->bool)#(A->real^N))
                               ((v:real->A->real^N^N) (r + a)) z)`] PDE_MT_COMM_UPTO) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:real`; `b:real`; `b'':real`;
                     `(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`;
                     `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                 (k:real->A->real^N^N) t z)`] PDE_ME_UPTO_SHIFT_SUB) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`a:real`; `b:real`; `b'':real`;
                     `(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`;
                     `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                       ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                              (pde_mlbt atlas (c:(A->bool)#(A->real^N))
                                 (k:real->A->real^N^N) (h:A->real^N^N) t z i)`]
                    PDE_ME_UPTO_SHIFT_SUB) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  (* vanishing off kp *)
  SUBGOAL_THEN
   `!r z. ~(z IN kp)
          ==> pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (r + a))
               (pde_mlbt atlas c k (h:A->real^N^N) (r + a))
               (\z. lift(if z IN (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) then (psi:A->real)(chart_inv c z) else &0))
               (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas c ((v:real->A->real^N^N) (r + a)) z)) z = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN
    EXISTS_TAC `(:real^N) DIFF kp` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; LIFT_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&0`; `b'' - a:real`; `lam:real`;
                 `\r z. if z IN (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                        then (if z IN (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) then (psi:A->real)(chart_inv
                                (c:(A->bool)#(A->real^N)) z) else &0) %
                             (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c ((f:real->A->real^N^N) (r + a)) z) -
                             pde_mt_comm (pde_mlaa atlas c (k:real->A->real^N^N) (r + a))
                               (pde_mlbt atlas c k (h:A->real^N^N) (r + a))
                               (\z. lift(if z IN (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) then psi(chart_inv c z) else &0))
                               (\z. vectorize(metric_local atlas c
                                      ((v:real->A->real^N^N) (r + a)) z)) z
                        else vec 0`;
                 `kp:real^N->bool`] PDM_TRANSPLANT_UPTO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO; COND_ID]] THEN
  MATCH_MP_TAC PDM_UPTO_CONG THEN
  EXISTS_TAC
   `\r z. &1 % (if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                then (if z IN IMAGE (SND c) (FST c) then (psi:A->real)(chart_inv c z)
                      else &0) %
                     (vectorize:real^N^N->real^(N,N)finite_prod)
                       (metric_local atlas c ((f:real->A->real^N^N) (r + a)) z)
                else vec 0) +
          --(&1) % (if z IN IMAGE (SND c) (FST c)
                    then (if z IN IMAGE (SND c) (FST c) then (theta:A->real)(chart_inv c z)
                          else &0) %
                         pde_mt_comm (pde_mlaa atlas c (k:real->A->real^N^N) (r + a))
                           (pde_mlbt atlas c k (h:A->real^N^N) (r + a))
                           (\z. lift(if z IN IMAGE (SND c) (FST c)
                                     then psi(chart_inv c z) else &0))
                           (\z. vectorize(metric_local atlas c ((v:real->A->real^N^N) (r + a)) z))
                           z
                    else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_LIN2 THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`&0`; `b'' - a:real`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `\r z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (metric_local atlas (c:(A->bool)#(A->real^N))
                                 ((f:real->A->real^N^N) (r + a)) z)`;
                     `\z. if z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)
                          then (psi:A->real)(chart_inv c z) else &0`;
                     `kp:real^N->bool`] PDM_UPTO_CUTOFF_EXT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`&0`; `b'' - a:real`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `\r z. pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                           (k:real->A->real^N^N) (r + a))
                              (pde_mlbt atlas c k (h:A->real^N^N) (r + a))
                              (\z. lift(if z IN IMAGE (SND c) (FST c)
                                        then (psi:A->real)(chart_inv c z) else &0))
                              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                     (metric_local atlas c ((v:real->A->real^N^N) (r + a)) z))
                              z`;
                     `\z. if z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)
                          then (theta:A->real)(chart_inv c z) else &0`;
                     `kt:real^N->bool`] PDM_UPTO_CUTOFF_EXT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `z:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  ASM_CASES_TAC `(z:real^N) IN kp` THENL
   [SUBGOAL_THEN `(theta:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) = &1`
    (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[VECTOR_MUL_RZERO] THEN VECTOR_ARITH_TAC]);;

(* The dynamic part: the inequality for one solution. *)

let PDE_ME_CE_DYNAMIC = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (psi:A->real) kp (theta:A->real) kt O a b b'
    (k:real->A->real^N^N) h s lam b'' (aaT:real->real^N->real^N^N)
    (bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) ccT lamT V C1 C2 f v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b' /\ b' < b /\
     mfd_smooth atlas (\x. lift(psi x)) /\ compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(psi x = &0) ==> x IN IMAGE (chart_inv c) kp) /\
     mfd_smooth atlas (\x. lift(theta x)) /\ compact kt /\ kt SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv c) kt) /\
     open O /\ kp SUBSET O /\ O SUBSET IMAGE (SND c) (FST c) /\
     (!z. z IN O ==> theta(chart_inv c z) = &1) /\
     &1 <= lam /\ b' < b'' /\ b'' < b /\
     kp UNION kt SUBSET ball(vec 0,lam / &4) /\
     pde_tcoeff (b'' - a) lamT aaT bbT ccT /\
     open V /\ kp UNION kt SUBSET V /\ V SUBSET IMAGE (SND c) (FST c) /\
     (!t z. a <= t /\ t < b'' /\ z IN V
            ==> aaT (t - a) (inv lam % z + inv(&2) % vec 1) =
                inv(lam pow 2) %% pde_mlaa atlas c k t z /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> bbT (t - a) (inv lam % z + inv(&2) % vec 1) i =
                         inv lam %% pde_mlbt atlas c k h t z i) /\
                ccT (t - a) (inv lam % z + inv(&2) % vec 1) = pde_mlct atlas c k h t z) /\
     &0 <= C1 /\
     (!f u. pde_upto (&0) (b'' - a) (:real^N) f /\ (!t. pde_zper (f t)) /\
            pde_tsol (b'' - a) aaT bbT ccT f (\y. vec 0) u
            ==> !t. &0 <= t /\ t <= b' - a
                    ==> pde_hs2 (s + 1) (u t) <=
                        C1 * real_integral (real_interval[&0,t]) (\r. pde_hs2 s (f r))) /\
     &0 <= C2 /\
     (!t (w:real^N->real^(N,N)finite_prod).
        &0 <= t /\ t <= b' - a /\ smooth_map_on (:real^N) w
        ==> pde_hs2 s
              (pde_mt_comm (aaT t) (bbT t)
                 (pdm_transplant lam
                    (\z. lift(if z IN IMAGE (SND c) (FST c)
                              then psi(chart_inv c z) else &0))) w)
            <= C2 * pde_hs2 (s + 1) w) /\
     pde_tfam_from atlas a b f /\ pde_mlin_sol (top,atlas) a b k h f (\x. mat 0) v
     ==> !t. a <= t /\ t <= b'
             ==> pde_me_cnorm atlas c psi (s + 1) (v t) <=
                 lam pow dimindex(:N) * C1 * (&2 * max (lam pow (2 * s))
                                                       (C2 * lam pow (2 * (s + 1)))) *
                 real_integral (real_interval[a,t])
                   (\r. pde_me_cnorm atlas c psi s (f r) +
                        pde_me_cnorm atlas c theta (s + 1) (v r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`]
                PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "psiz")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `theta:A->real`; `kt:real^N->bool`]
                PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "thetaz")) THEN
  SUBGOAL_THEN
   `pde_upto a b (IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))))
      (\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas c ((v:real->A->real^N^N) t) z)) /\
    pde_upto a b (IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))))
      (\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas c ((f:real->A->real^N^N) t) z))`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PDM_TFAM_FROM_UPTO; pde_mlin_sol]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the transplanted solution and forcing *)
  ABBREV_TAC
   `u = \r. pdm_transplant lam
              (\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                   then (if z IN IMAGE (SND c) (FST c) then (psi:A->real)(chart_inv c z)
                         else &0) %
                        (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas c ((v:real->A->real^N^N) (r + a)) z)
                   else vec 0)` THEN
  ABBREV_TAC
   `GG = \r. pdm_transplant lam
              (\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                   then (if z IN IMAGE (SND c) (FST c) then (psi:A->real)(chart_inv c z)
                         else &0) %
                        (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas c ((f:real->A->real^N^N) (r + a)) z) -
                        pde_mt_comm (pde_mlaa atlas c (k:real->A->real^N^N) (r + a))
                          (pde_mlbt atlas c k (h:A->real^N^N) (r + a))
                          (\z. lift(if z IN IMAGE (SND c) (FST c)
                                    then psi(chart_inv c z) else &0))
                          (\z. vectorize(metric_local atlas c (v (r + a)) z)) z
                   else vec 0)` THEN
  SUBGOAL_THEN
   `&0 < lam /\ kp SUBSET (V:real^N->bool) /\ kp SUBSET ball(vec 0:real^N,lam / &4) /\
    kt SUBSET (V:real^N->bool) /\ kt SUBSET ball(vec 0:real^N,lam / &4)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_upto a b'' (IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))))
      (\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas c ((v:real->A->real^N^N) t) z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. a < t /\ t < b'' /\ z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
          ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas c ((v:real->A->real^N^N) (drop s)) z))
               has_vector_derivative
               pde_lop0 (pde_mlaa atlas c (k:real->A->real^N^N) t)
                        (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t)
                 (\z. vectorize(metric_local atlas c (v t) z)) z +
               vectorize(metric_local atlas c ((f:real->A->real^N^N) t) z)) (at (lift t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                   `f:real->A->real^N^N`; `\x:A. mat 0:real^N^N`; `v:real->A->real^N^N`;
                   `c:(A->bool)#(A->real^N)`; `t':real`; `z:real^N`] PDE_ML_SOL_CHART_LOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[PDE_LOP_LOP0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!r. (u:real->real^N->real^(N,N)finite_prod) r =
         pdm_transplant lam
           (\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                then (if z IN IMAGE (SND c) (FST c) then (psi:A->real)(chart_inv c z)
                      else &0) %
                     (vectorize:real^N^N->real^(N,N)finite_prod)
                       (metric_local atlas c ((v:real->A->real^N^N) (r + a)) z)
                else vec 0)) /\
    (!r. (GG:real->real^N->real^(N,N)finite_prod) r =
         pdm_transplant lam
           (\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                then (if z IN IMAGE (SND c) (FST c) then (psi:A->real)(chart_inv c z)
                      else &0) %
                     (vectorize:real^N^N->real^(N,N)finite_prod)
                       (metric_local atlas c ((f:real->A->real^N^N) (r + a)) z) -
                     pde_mt_comm (pde_mlaa atlas c (k:real->A->real^N^N) (r + a))
                       (pde_mlbt atlas c k (h:A->real^N^N) (r + a))
                       (\z. lift(if z IN IMAGE (SND c) (FST c)
                                 then psi(chart_inv c z) else &0))
                       (\z. vectorize(metric_local atlas c (v (r + a)) z)) z
                else vec 0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THENL [EXPAND_TAC "u"; EXPAND_TAC "GG"] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_tsol (b'' - a) aaT bbT ccT
                  (GG:real->real^N->real^(N,N)finite_prod) (u (&0)) u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_MT_TRANS_TSOL THEN
    MAP_EVERY EXISTS_TAC
     [`lam:real`; `lamT:real`; `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)`;
      `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N)`;
      `pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N)`;
      `V:real^N->bool`; `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`;
      `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t) z)`;
      `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas (c:(A->bool)#(A->real^N)) ((f:real->A->real^N^N) t) z)`;
      `\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
           then (psi:A->real)(chart_inv c z) else &0`;
      `kp:real^N->bool`] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* zero initial data *)
  SUBGOAL_THEN `(u:real->real^N->real^(N,N)finite_prod) (&0) = (\y. vec 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    SUBGOAL_THEN
     `(\z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
           then (if z IN IMAGE (SND c) (FST c) then (psi:A->real)(chart_inv c z) else &0) %
                (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas c ((v:real->A->real^N^N) a) z)
           else vec 0) = (\z:real^N. vec 0:real^(N,N)finite_prod)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`; `(v:real->A->real^N^N) a`; `z:real^N`]
                    PDE_ME_CHART_ZERO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h
                       (f:real->A->real^N^N) (\x. mat 0) (v:real->A->real^N^N)` THEN
        SIMP_TAC[pde_mlin_sol];
        SIMP_TAC[VECTORIZE_0; VECTOR_MUL_RZERO]];
      REWRITE_TAC[FUN_EQ_THM; pdm_transplant; pdm_periodize]];
    ALL_TAC] THEN
  (* regularity of the forcing *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`;
                 `theta:A->real`; `kt:real^N->bool`; `O:real^N->bool`; `a:real`; `b:real`;
                 `b'':real`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                 `v:real->A->real^N^N`; `f:real->A->real^N^N`; `lam:real`] PDE_ME_GG_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h
                   (f:real->A->real^N^N) (\x. mat 0) (v:real->A->real^N^N)` THEN
    SIMP_TAC[pde_mlin_sol];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `!r. pde_zper ((GG:real->real^N->real^(N,N)finite_prod) r)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PDM_TRANSPLANT_ZPER]; ALL_TAC] THEN
  (* the torus energy estimate *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`GG:real->real^N->real^(N,N)finite_prod`;
                                `u:real->real^N->real^(N,N)finite_prod`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th) &&
    is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t - a:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `a <= t /\ t < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the tensor slices *)
  SUBGOAL_THEN
   `!r. a <= r /\ r < b
        ==> pde_tensor_smooth atlas ((v:real->A->real^N^N) r) /\
            pde_tensor_smooth atlas ((f:real->A->real^N^N) r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h
                   (f:real->A->real^N^N) (\x. mat 0) (v:real->A->real^N^N)` THEN
    SIMP_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  (* cut-off chart pieces are smooth on R^N with support in the piece *)
  SUBGOAL_THEN
   `!(phi:A->real) kq (w:A->real^N^N).
      mfd_smooth atlas (\x. lift(phi x)) /\ compact kq /\
      kq SUBSET IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))) /\
      (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) kq) /\ pde_tensor_smooth atlas w
      ==> smooth_map_on (:real^N)
            (\z. if z IN IMAGE (SND c) (FST c)
                 then (if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0) %
                      (vectorize:real^N^N->real^(N,N)finite_prod) (metric_local atlas c w z)
                 else vec 0) /\
          (!z. ~(z IN kq)
               ==> (if z IN IMAGE (SND c) (FST c)
                    then (if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0) %
                         (vectorize:real^N^N->real^(N,N)finite_prod) (metric_local atlas c w z)
                    else vec 0) = vec 0)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `phi:A->real`; `w:A->real^N^N`;
                   `kq:real^N->bool`] PDM_CHART_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `kq:real^N->bool`;
                     `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((phi:A->real) (chart_inv (c:(A->bool)#(A->real^N)) z) %%
                           metric_local atlas c (w:A->real^N^N) z)`] PDM_ZERO_EXT_SMOOTH) THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[VECTORIZE_CMUL];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "%%")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[VECTORIZE_CMUL]];
    ALL_TAC] THEN
  (* the left side: chart norm by the torus norm of the transplant *)
  SUBGOAL_THEN
   `pde_me_cnorm atlas c psi (s + 1) ((v:real->A->real^N^N) t) <=
    lam pow dimindex(:N) * pde_hs2 (s + 1) ((u:real->real^N->real^(N,N)finite_prod) (t - a))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`;
                   `(v:real->A->real^N^N) t`; `s + 1`] PDE_ME_CNORM_ZEROEXT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_ADD] THEN MATCH_MP_TAC PDE_ME_CHART_LE_TRANSPLANT THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`psi:A->real`; `kp:real^N->bool`;
                                  `(v:real->A->real^N^N) t`] o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "kq")) (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `kp SUBSET ball(vec 0:real^N,lam / &4)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  (* the bound for the transplanted forcing *)
  SUBGOAL_THEN
   `!r. &0 <= r /\ r <= b' - a
        ==> pde_hs2 s ((GG:real->real^N->real^(N,N)finite_prod) r) <=
            (&2 * max (lam pow (2 * s)) (C2 * lam pow (2 * (s + 1)))) *
            (pde_me_cnorm atlas c psi s ((f:real->A->real^N^N) (r + a)) +
             pde_me_cnorm atlas c theta (s + 1) ((v:real->A->real^N^N) (r + a)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= r + a /\ r + a < b /\ r + a < b''` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (* the two pieces P1 (forcing) and F (theta v) *)
    FIRST_ASSUM(MP_TAC o SPECL [`psi:A->real`; `kp:real^N->bool`;
                                `(f:real->A->real^N^N) (r + a)`] o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "kq")) (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`theta:A->real`; `kt:real^N->bool`;
                                `(v:real->A->real^N^N) (r + a)`] o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "kq")) (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
    ABBREV_TAC
     `P1 = \z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
               then (if z IN IMAGE (SND c) (FST c) then (psi:A->real)(chart_inv c z)
                     else &0) %
                    (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas c ((f:real->A->real^N^N) (r + a)) z)
               else vec 0` THEN
    ABBREV_TAC
     `FF = \z. if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
               then (if z IN IMAGE (SND c) (FST c) then (theta:A->real)(chart_inv c z)
                     else &0) %
                    (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas c ((v:real->A->real^N^N) (r + a)) z)
               else vec 0` THEN
    (* the transplanted commutator *)
    MP_TAC(ISPECL
     [`lam:real`; `(aaT:real->real^N->real^N^N) r`;
      `(bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) r`;
      `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (r + a)`;
      `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) (r + a)`;
      `V:real^N->bool`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `O:real^N->bool`;
      `\z. if z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)
           then (psi:A->real)(chart_inv c z) else &0`;
      `kp:real^N->bool`;
      `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) (r + a)) z)`;
      `FF:real^N->real^(N,N)finite_prod`] PDE_ME_TRANSPLANT_COMM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`r + a:real`; `z:real^N`] o check (fun th ->
          can (find_term (fun t -> is_var t && fst(dest_var t) = "aaT")) (concl th) &&
          is_forall (concl th))) THEN
        ASM_REWRITE_TAC[REAL_ARITH `(r + a) - a:real = r`] THEN SIMP_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[pde_tcoeff]) THEN ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[pde_tcoeff]) THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN EXPAND_TAC "FF" THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `kt SUBSET ball(vec 0:real^N,lam / &4)` THEN
        REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LT_ANTISYM];
        X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "FF" THEN
        SUBGOAL_THEN `(z:real^N) IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`
          (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[VECTOR_MUL_LID]];
      DISCH_THEN(LABEL_TAC "tcomm" o REWRITE_RULE[])] THEN
    (* GG r splits *)
    SUBGOAL_THEN
     `(GG:real->real^N->real^(N,N)finite_prod) r =
      (\x. pdm_transplant lam (P1:real^N->real^(N,N)finite_prod) x -
           pde_mt_comm ((aaT:real->real^N->real^N^N) r)
             ((bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) r)
             (pdm_transplant lam
                (\z. lift(if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                          then (psi:A->real)(chart_inv c z) else &0)))
             (pdm_transplant lam (FF:real^N->real^(N,N)finite_prod)) x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REMOVE_THEN "tcomm" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[GSYM PDE_ME_TRANSPLANT_SUB] THEN AP_TERM_TAC THEN
      EXPAND_TAC "P1" THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[VECTOR_SUB_RZERO];
      ALL_TAC] THEN
    (* smoothness and support of the pieces *)
    SUBGOAL_THEN
     `smooth_map_on (:real^N) (P1:real^N->real^(N,N)finite_prod) /\
      (!z. lam / &4 < norm z ==> P1 z = vec 0) /\
      smooth_map_on (:real^N) (FF:real^N->real^(N,N)finite_prod) /\
      (!z. lam / &4 < norm z ==> FF z = vec 0)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "P1" THEN EXPAND_TAC "FF" THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
       [UNDISCH_TAC `kp SUBSET ball(vec 0:real^N,lam / &4)`;
        UNDISCH_TAC `kt SUBSET ball(vec 0:real^N,lam / &4)`] THEN
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LT_ANTISYM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^N)
        (pdm_transplant lam
           (\z. lift(if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                     then (psi:A->real)(chart_inv c z) else &0)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `~((z:real^N) IN kp)` (fun th -> ASM_SIMP_TAC[th; LIFT_NUM]) THEN
      UNDISCH_TAC `kp SUBSET ball(vec 0:real^N,lam / &4)` THEN
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LT_ANTISYM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^N) (pdm_transplant lam (P1:real^N->real^(N,N)finite_prod)) /\
      smooth_map_on (:real^N) (pdm_transplant lam (FF:real^N->real^(N,N)finite_prod))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^N)
        (pde_mt_comm ((aaT:real->real^N->real^N^N) r)
          ((bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) r)
          (pdm_transplant lam
             (\z. lift(if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                       then (psi:A->real)(chart_inv c z) else &0)))
          (pdm_transplant lam (FF:real^N->real^(N,N)finite_prod)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PDE_ME_COMM_SMOOTH THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
      UNDISCH_TAC `pde_tcoeff (b'' - a) lamT (aaT:real->real^N->real^N^N)
                     (bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) ccT` THEN
      REWRITE_TAC[pde_tcoeff] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`b'' - a:real`;
                       `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                                ((aaT:real->real^N->real^N^N) t y)`; `r:real`]
                      PDE_UPTO_SLICE_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
        REPEAT STRIP_TAC THEN
        MP_TAC(ISPECL [`b'' - a:real`;
                       `\t y. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                         ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                                ((bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod)
                                   t y i)`; `r:real`] PDE_UPTO_SLICE_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]];
      ALL_TAC] THEN
    (* the two norms *)
    SUBGOAL_THEN
     `pde_hs2 s (pdm_transplant lam (P1:real^N->real^(N,N)finite_prod)) <=
      lam pow (2 * s) * pde_me_cnorm atlas c psi s ((f:real->A->real^N^N) (r + a)) /\
      &0 <= pde_me_cnorm atlas c psi s ((f:real->A->real^N^N) (r + a))`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`;
                     `(f:real->A->real^N^N) (r + a)`; `s:num`] PDE_ME_CNORM_ZEROEXT) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PDE_ME_TRANSPLANT_HS2_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ME_UNIV_SQNORM_POS THEN
        EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pde_hs2 (s + 1) (pdm_transplant lam (FF:real^N->real^(N,N)finite_prod)) <=
      lam pow (2 * (s + 1)) *
      pde_me_cnorm atlas c theta (s + 1) ((v:real->A->real^N^N) (r + a)) /\
      &0 <= pde_me_cnorm atlas c theta (s + 1) ((v:real->A->real^N^N) (r + a))`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`; `theta:A->real`; `kt:real^N->bool`;
                     `(v:real->A->real^N^N) (r + a)`; `s + 1`] PDE_ME_CNORM_ZEROEXT) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PDE_ME_TRANSPLANT_HS2_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ME_UNIV_SQNORM_POS THEN
        EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pde_hs2 s
        (pde_mt_comm ((aaT:real->real^N->real^N^N) r)
          ((bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) r)
          (pdm_transplant lam
             (\z. lift(if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                       then (psi:A->real)(chart_inv c z) else &0)))
          (pdm_transplant lam (FF:real^N->real^(N,N)finite_prod))) <=
      C2 * pde_hs2 (s + 1) (pdm_transplant lam FF)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> is_var t && fst(dest_var t) = "w")) (concl th) &&
        can (find_term (fun t -> is_var t && fst(dest_var t) = "C2")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&2 * pde_hs2 s (pdm_transplant lam (P1:real^N->real^(N,N)finite_prod)) +
      &2 * pde_hs2 s
        (pde_mt_comm ((aaT:real->real^N->real^N^N) r)
          ((bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) r)
          (pdm_transplant lam
             (\z. lift(if z IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
                       then (psi:A->real)(chart_inv c z) else &0)))
          (pdm_transplant lam (FF:real^N->real^(N,N)finite_prod)))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC PDE_ME_HS2_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    ABBREV_TAC `MM = max (lam pow (2 * s)) (C2 * lam pow (2 * (s + 1)))` THEN
    SUBGOAL_THEN `lam pow (2 * s) <= MM /\ C2 * lam pow (2 * (s + 1)) <= MM`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "MM" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&2 * (lam pow (2 * s) * pde_me_cnorm atlas c psi s ((f:real->A->real^N^N) (r + a))) +
      &2 * (C2 * (lam pow (2 * (s + 1)) *
                  pde_me_cnorm atlas c theta (s + 1) ((v:real->A->real^N^N) (r + a))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `x <= x' /\ y <= y' ==> &2 * x + &2 * y <= &2 * x' + &2 * y'`) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `C2 * pde_hs2 (s + 1) (pdm_transplant lam (FF:real^N->real^(N,N)finite_prod))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(REAL_ARITH
       `p <= MM * A /\ q <= MM * B ==> &2 * p + &2 * q <= (&2 * MM) * (A + B)`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* continuity of the right-hand integrand *)
  ABBREV_TAC `g = \r. pde_me_cnorm atlas (c:(A->bool)#(A->real^N)) psi s ((f:real->A->real^N^N) r) +
                      pde_me_cnorm atlas c theta (s + 1) ((v:real->A->real^N^N) r)` THEN
  SUBGOAL_THEN `(g:real->real) real_continuous_on real_interval[a,t]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[a,b']` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "g" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC PDE_ME_CNORM_CONT THENL
       [MAP_EVERY EXISTS_TAC [`top:A topology`; `kp:real^N->bool`; `b:real`];
        MAP_EVERY EXISTS_TAC [`top:A topology`; `kt:real^N->bool`; `b:real`]] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h
                     (f:real->A->real^N^N) (\x. mat 0) (v:real->A->real^N^N)` THEN
      SIMP_TAC[pde_mlin_sol];
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\r. (g:real->real) (r + a)) real_continuous_on real_interval[&0,t - a]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\r. (g:real->real) (r + a)) = g o (\r. r + a)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
      SUBGOAL_THEN `IMAGE (\r. r + a) (real_interval[&0,t - a]) = real_interval[a,t]`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN X_GEN_TAC `y:real` THEN
      EQ_TAC THENL [STRIP_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      EXISTS_TAC `y - a:real` THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the integral comparison *)
  SUBGOAL_THEN
   `real_integral (real_interval[&0,t - a])
      (\r. pde_hs2 s ((GG:real->real^N->real^(N,N)finite_prod) r)) <=
    (&2 * max (lam pow (2 * s)) (C2 * lam pow (2 * (s + 1)))) *
    real_integral (real_interval[a,t]) g`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,t - a])
                  (\r. (&2 * max (lam pow (2 * s)) (C2 * lam pow (2 * (s + 1)))) *
                       (g:real->real) (r + a))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN EXISTS_TAC `b'' - a:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        EXPAND_TAC "g" THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`\r. (g:real->real) (r + a)`;
                     `&2 * max (lam pow (2 * s)) (C2 * lam pow (2 * (s + 1)))`;
                     `real_interval[&0,t - a]`] REAL_INTEGRAL_LMUL) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(ISPECL [`g:real->real`; `a:real`; `t:real`] PDE_ME_RINT_SHIFT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* conclusion *)
  SUBGOAL_THEN `&0 <= lam pow dimindex(:N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam pow dimindex(:N) *
              pde_hs2 (s + 1) ((u:real->real^N->real^(N,N)finite_prod) (t - a))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(ACCEPT_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_me_cnorm")) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "u")) (concl th)));
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * real_integral (real_interval[&0,t - a])
                     (\r. pde_hs2 s ((GG:real->real^N->real^(N,N)finite_prod) r))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(ACCEPT_TAC o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "C1")) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "u")) (concl th) &&
      not (is_forall (concl th))));
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(ACCEPT_TAC o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "GG")) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "g")) (concl th) &&
      not (is_forall (concl th))))]);;

(* ========================================================================= *)
(* An integral Gronwall inequality (from PDE_GRONWALL_W of pc_pde_tlin).     *)
(* ========================================================================= *)

let PDE_ME_GRONWALL0 = prove
 (`!(Y:real->real) Fn C0 T1.
     &0 <= C0 /\ &0 <= T1 /\
     Y real_continuous_on real_interval[&0,T1] /\ Fn real_continuous_on real_interval[&0,T1] /\
     (!t. t IN real_interval[&0,T1] ==> &0 <= Fn t) /\
     (!t. t IN real_interval[&0,T1]
          ==> Y t <= C0 * (real_integral (real_interval[&0,t]) Fn +
                           real_integral (real_interval[&0,t]) Y))
     ==> Y T1 <= C0 * (&1 + C0 * T1 * exp(C0 * T1)) * real_integral (real_interval[&0,T1]) Fn`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = real_integral (real_interval[&0,T1]) (Fn:real->real)` THEN
  SUBGOAL_THEN `&0 <= G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,T1] ==> real_integral (real_interval[&0,t]) (Fn:real->real) <= G`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "G" THEN MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
    ASM_SIMP_TAC[SUBSET_REAL_INTERVAL; REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,T1]` THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. real_integral (real_interval[&0,t]) (Y:real->real)`; `Y:real->real`;
                 `\r:real. &0`; `\r:real. C0 * G`; `C0:real`; `C0:real`; `T1:real`]
                PDE_GRONWALL_W) THEN
  REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_CONTINUOUS_ON_CONST] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PDE_RINT_CONT] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RINT_DERIV THEN EXISTS_TAC `T1:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t IN real_interval[&0,T1]` ASSUME_TAC THENL
     [UNDISCH_TAC `t IN real_interval(&0,T1)` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "Y")) (concl th) &&
      is_forall (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "G")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C0 * (real_integral (real_interval[&0,t]) (Fn:real->real) +
                      real_integral (real_interval[&0,t]) (Y:real->real))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_ADD_RID]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + z <= y + z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `T1:real`) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_RZERO; REAL_INTEGRAL_0;
              REAL_ADD_RID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,T1]) (\r. exp(--(C0 * r)) * C0 * G) <= C0 * G * T1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,T1]) (\r:real. C0 * G)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[PDE_EXP_WEIGHT_CONT; REAL_CONTINUOUS_ON_CONST];
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
        X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
          REWRITE_TAC[REAL_EXP_MONO_LE; REAL_NEG_LE0] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_SUB_RZERO; REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `T1:real` o check (fun th ->
    can (find_term (fun t -> is_var t && fst(dest_var t) = "Y")) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN DISCH_TAC THEN
  ABBREV_TAC `IY = real_integral (real_interval[&0,T1]) (Y:real->real)` THEN
  SUBGOAL_THEN `IY <= exp(C0 * T1) * (C0 * G * T1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(C0 * T1) * (exp(--(C0 * T1)) * IY)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * (G + IY)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `G + exp(C0 * T1) * (C0 * G * T1)` THEN
  CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `(&1 + c * t * e) * g = g + e * (c * g * t)`; REAL_LE_REFL]]);;

(* The shifted form on [a,Tm]. *)

let PDE_ME_SHIFT_CONT = prove
 (`!(g:real->real) a Tm.
     a <= Tm /\ g real_continuous_on real_interval[a,Tm]
     ==> (\r. g(r + a)) real_continuous_on real_interval[&0,Tm - a]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\r. (g:real->real) (r + a)) = g o (\r. r + a)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
    SUBGOAL_THEN `IMAGE (\r. r + a) (real_interval[&0,Tm - a]) = real_interval[a,Tm]`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN X_GEN_TAC `y:real` THEN
    EQ_TAC THENL [STRIP_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    EXISTS_TAC `y - a:real` THEN ASM_REAL_ARITH_TAC]);;

let PDE_ME_GRONWALL = prove
 (`!(Y:real->real) Fn C0 a Tm.
     &0 <= C0 /\ a <= Tm /\
     Y real_continuous_on real_interval[a,Tm] /\ Fn real_continuous_on real_interval[a,Tm] /\
     (!t. t IN real_interval[a,Tm] ==> &0 <= Fn t) /\
     (!t. t IN real_interval[a,Tm]
          ==> Y t <= C0 * (real_integral (real_interval[a,t]) Fn +
                           real_integral (real_interval[a,t]) Y))
     ==> Y Tm <= C0 * (&1 + C0 * (Tm - a) * exp(C0 * (Tm - a))) *
                real_integral (real_interval[a,Tm]) Fn`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (Y:real->real) (r + a)`; `\r. (Fn:real->real) (r + a)`; `C0:real`;
                 `Tm - a:real`] PDE_ME_GRONWALL0) THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN
  MP_TAC(ISPECL [`Fn:real->real`; `a:real`; `Tm:real`] PDE_ME_RINT_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[PDE_ME_SHIFT_CONT] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "Fn")) (concl th) &&
      not (can (find_term (fun t -> is_var t && fst(dest_var t) = "Y")) (concl th)) &&
      is_forall (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= t + a /\ t + a <= Tm` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`Fn:real->real`; `a:real`; `t + a:real`] PDE_ME_RINT_SHIFT) THEN
    MP_TAC(ISPECL [`Y:real->real`; `a:real`; `t + a:real`] PDE_ME_RINT_SHIFT) THEN
    REWRITE_TAC[REAL_ARITH `(t + a) - a:real = t`] THEN
    SUBGOAL_THEN
     `(Y:real->real) real_continuous_on real_interval[a,t + a] /\
      (Fn:real->real) real_continuous_on real_interval[a,t + a]`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[a,Tm]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Enlarging the pieces of a cover so that the cutoffs are supported in      *)
(* them, and the energy estimate on M (PDE_MLIN_ENERGY).                     *)
(* ========================================================================= *)

let PDE_ME_COVER_ENLARGE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi
     ==> ?ks'. pde_cover (top,atlas) n0 cs ks' /\
               (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks' i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_cover; pde_cutoffs] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?L. !i. i < n0 ==> compact_in top (L i) /\ L i SUBSET FST((cs:num->(A->bool)#(A->real^N)) i) /\
                       !x:A. ~(x IN L i) ==> (psi:num->A->real) i x = &0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\i. (ks:num->real^N->bool) i UNION
                  IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) ((L:num->A->bool) i)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. i < n0
        ==> compact(IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) ((L:num->A->bool) i)) /\
            IMAGE (SND(cs i)) (L i) SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC PDM_CHART_IMAGE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [th]) o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "UNIONS")) (concl th))) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `IMAGE (chart_inv((cs:num->(A->bool)#(A->real^N)) i))
                    (interior((ks:num->real^N->bool) i UNION
                              IMAGE (SND(cs i)) ((L:num->A->bool) i)))` THEN
      CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:A) IN S` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> (x:A) IN IMAGE f s ==> x IN IMAGE f t`) THEN
      MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(x:A) IN S` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_OPEN_C) THEN
      ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
      ASSUME_TAC THENL
       [MP_TAC(ISPEC `(ks:num->real^N->bool) i UNION
                      IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) ((L:num->A->bool) i)`
                     INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(y:real^N) IN interior((ks:num->real^N->bool) i UNION
                      IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) ((L:num->A->bool) i))` THEN
        ASM_SIMP_TAC[] THEN ASM SET_TAC[];
        ASM SET_TAC[]]];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN (L:num->A->bool) i` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `SND((cs:num->(A->bool)#(A->real^N)) i) (x:A)` THEN
    SUBGOAL_THEN `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) i)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN DISJ2_TAC THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]);;

(* Chart norms are nonnegative. *)

let PDE_ME_CNORM_POS = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) kp (w:A->real^N^N) s.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) kp) /\ pde_tensor_smooth atlas w
     ==> &0 <= pde_me_cnorm atlas c phi s w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `kp:real^N->bool`;
                 `w:A->real^N^N`; `s:num`] PDE_ME_CNORM_ZEROEXT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MP_TAC(ISPEC `kp:real^N->bool` COMPACT_IMP_BOUNDED) THEN
  ASM_REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC PDM_SQNORM_PARTIAL_INTEGRABLE THEN EXISTS_TAC `kp:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `w:A->real^N^N`;
                 `kp:real^N->bool`] PDM_CHART_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `kp:real^N->bool`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((phi:A->real) (chart_inv (c:(A->bool)#(A->real^N)) z) %%
                         metric_local atlas c (w:A->real^N^N) z)`] PDM_ZERO_EXT_SMOOTH) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[VECTORIZE_CMUL];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "%%")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[VECTORIZE_CMUL]]);;

let PDE_ME_MNORM2_POS = prove
 (`!(top:A topology) atlas n0 cs ks psi (w:A->real^N^N) s.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tensor_smooth atlas w
     ==> &0 <= pde_mnorm2 atlas n0 cs psi s w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_ME_MNORM2_CNORM] THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_ME_CNORM_POS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) i`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pde_cover; pde_cutoffs]) THEN ASM_SIMP_TAC[]);;

let PDE_ME_CHART_ENERGY = prove
 (`!top atlas n0 cs ks psi0 (c:(A->bool)#(A->real^N)) (psi:A->real) kp a b b'
    (k:real->A->real^N^N) h s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi0 /\
     (!i x. i < n0 /\ ~(psi0 i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b' /\ b' < b /\
     mfd_smooth atlas (\x. lift(psi x)) /\ compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(psi x = &0) ==> x IN IMAGE (chart_inv c) kp)
     ==> ?K (theta:A->real) kt D.
           &0 <= K /\ &0 <= D /\
           mfd_smooth atlas (\x. lift(theta x)) /\ compact kt /\
           kt SUBSET IMAGE (SND c) (FST c) /\
           (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv c) kt) /\
           (!w. pde_tensor_smooth atlas w
                ==> pde_me_cnorm atlas c theta (s + 1) w <=
                    D * pde_mnorm2 atlas n0 cs psi0 (s + 1) w) /\
           (!f v. pde_tfam_from atlas a b f /\
                  pde_mlin_sol (top,atlas) a b k h f (\x. mat 0) v
                  ==> !t. a <= t /\ t <= b'
                          ==> pde_me_cnorm atlas c psi (s + 1) (v t) <=
                              K * real_integral (real_interval[a,t])
                                    (\r. pde_me_cnorm atlas c psi s (f r) +
                                         pde_me_cnorm atlas c theta (s + 1) (v r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `kp:real^N->bool`] PDE_ME_THETA_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:A->real` (X_CHOOSE_THEN `kt:real^N->bool`
    (X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`;
                 `kt:real^N->bool`; `a:real`; `b:real`; `b':real`; `k:real->A->real^N^N`;
                 `h:A->real^N^N`; `s:num`] PDE_ME_CE_STATIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `aaT:real->real^N->real^N^N` (X_CHOOSE_THEN
    `bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod` (X_CHOOSE_THEN
    `ccT:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod` (X_CHOOSE_THEN `lamT:real`
    (X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `C1:real` (X_CHOOSE_THEN `C2:real`
    STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi0:num->A->real`; `c:(A->bool)#(A->real^N)`; `theta:A->real`;
                 `kt:real^N->bool`; `s + 1`] PDM_MNORM_LOCALIZE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `D0:real`) THEN
  EXISTS_TAC `lam pow dimindex(:N) * C1 *
              (&2 * max (lam pow (2 * s)) (C2 * lam pow (2 * (s + 1))))` THEN
  MAP_EVERY EXISTS_TAC [`theta:A->real`; `kt:real^N->bool`; `max D0 (&0)`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_MAX] THEN
    DISJ1_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `w:A->real^N^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:A->real^N^N`) THEN ASM_REWRITE_TAC[pde_me_cnorm] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`f:real->A->real^N^N`; `v:real->A->real^N^N`] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `psi:A->real`; `kp:real^N->bool`;
                   `theta:A->real`; `kt:real^N->bool`; `O:real^N->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `s:num`; `lam:real`;
                   `b'':real`; `aaT:real->real^N->real^N^N`;
                   `bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:real`; `V:real^N->bool`; `C1:real`; `C2:real`;
                   `f:real->A->real^N^N`; `v:real->A->real^N^N`] PDE_ME_CE_DYNAMIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC]]);;

let PDE_ME_CNORM_LE_MNORM2 = prove
 (`!(top:A topology) atlas n0 cs ks psi (w:A->real^N^N) s i.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tensor_smooth atlas w /\ i < n0
     ==> pde_me_cnorm atlas (cs i) (psi i) s w <= pde_mnorm2 atlas n0 cs psi s w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_ME_MNORM2_CNORM] THEN
  MP_TAC(ISPECL [`\j. pde_me_cnorm atlas ((cs:num->(A->bool)#(A->real^N)) j)
                        ((psi:num->A->real) j) s (w:A->real^N^N)`;
                 `{j:num | j < n0}`; `i:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> s = t - x ==> x <= t`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_ME_CNORM_POS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) j`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pde_cover; pde_cutoffs]) THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The energy estimate on M (PDE_MLIN_ENERGY): sum of the chart estimates,   *)
(* localization of the theta-terms, Gronwall.                                *)
(* ========================================================================= *)

let PDE_MLIN_ENERGY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi a b b' k h s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        riemannian_metric atlas h /\
        (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
        pde_tfam_from atlas a b k /\ a < b' /\ b' < b
        ==> ?C. !f v. pde_tfam_from atlas a b f /\
                      pde_mlin_sol (top,atlas) a b k h f (\x. mat 0) v
                      ==> !t. a <= t /\ t <= b'
                              ==> pde_mnorm2 atlas n0 cs psi (s + 1) (v t) <=
                                  C * real_integral (real_interval[a,t])
                                        (\r. pde_mnorm2 atlas n0 cs psi s (f r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`] PDE_ME_COVER_ENLARGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ks':num->real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i < n0
        ==> (cs:num->(A->bool)#(A->real^N)) i IN atlas /\
            mfd_smooth atlas (\x. lift((psi:num->A->real) i x)) /\
            compact((ks':num->real^N->bool) i) /\
            ks' i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pde_cover; pde_cutoffs]) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?K (theta:A->real) kt D.
        i < n0
        ==> &0 <= K /\ &0 <= D /\
            mfd_smooth atlas (\x. lift(theta x)) /\ compact kt /\
            kt SUBSET IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)) /\
            (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv (cs i)) kt) /\
            (!w. pde_tensor_smooth atlas w
                 ==> pde_me_cnorm atlas (cs i) theta (s + 1) w <=
                     D * pde_mnorm2 atlas n0 cs (psi:num->A->real) (s + 1) w) /\
            (!f v. pde_tfam_from atlas a b f /\
                   pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h f (\x. mat 0) v
                   ==> !t. a <= t /\ t <= b'
                           ==> pde_me_cnorm atlas (cs i) (psi i) (s + 1) (v t) <=
                               K * real_integral (real_interval[a,t])
                                     (\r. pde_me_cnorm atlas (cs i) (psi i) s (f r) +
                                          pde_me_cnorm atlas (cs i) theta (s + 1) (v r)))`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC PDE_ME_CHART_ENERGY THEN
    MAP_EVERY EXISTS_TAC [`ks':num->real^N->bool`; `(ks':num->real^N->bool) i`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num->real` (X_CHOOSE_THEN `TH:num->A->real`
    (X_CHOOSE_THEN `KT:num->real^N->bool` (X_CHOOSE_THEN `D:num->real` (LABEL_TAC "ch"))))) THEN
  ABBREV_TAC `C0 = sum {i:num | i < n0} (\i. (K:num->real) i * (&1 + (D:num->real) i))` THEN
  SUBGOAL_THEN `&0 <= C0` ASSUME_TAC THENL
   [EXPAND_TAC "C0" THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "ch" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i:num < n0`))) THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `C0 * (&1 + C0 * (b' - a) * exp(C0 * (b' - a)))` THEN
  MAP_EVERY X_GEN_TAC [`f:real->A->real^N^N`; `v:real->A->real^N^N`] THEN STRIP_TAC THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  (* tensor slices *)
  SUBGOAL_THEN
   `!r. a <= r /\ r < b
        ==> pde_tensor_smooth atlas ((v:real->A->real^N^N) r) /\
            pde_tensor_smooth atlas ((f:real->A->real^N^N) r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h
                   (f:real->A->real^N^N) (\x. mat 0) (v:real->A->real^N^N)` THEN
    SIMP_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h
                   (f:real->A->real^N^N) (\x. mat 0) (v:real->A->real^N^N)` THEN
    SIMP_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  (* continuity of the chart norms *)
  SUBGOAL_THEN
   `!i. i < n0
        ==> (\r. pde_me_cnorm atlas ((cs:num->(A->bool)#(A->real^N)) i) ((psi:num->A->real) i)
                   (s + 1) ((v:real->A->real^N^N) r)) real_continuous_on real_interval[a,b'] /\
            (\r. pde_me_cnorm atlas (cs i) (psi i) s ((f:real->A->real^N^N) r))
              real_continuous_on real_interval[a,b'] /\
            (\r. pde_me_cnorm atlas (cs i) ((TH:num->A->real) i) (s + 1) (v r))
              real_continuous_on real_interval[a,b']`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "ch" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i:num < n0`))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "ks'")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_smooth")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC PDE_ME_CNORM_CONT THENL
     [MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks':num->real^N->bool) i`; `b:real`];
      MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks':num->real^N->bool) i`; `b:real`];
      MAP_EVERY EXISTS_TAC [`top:A topology`; `(KT:num->real^N->bool) i`; `b:real`]] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. pde_mnorm2 atlas n0 cs (psi:num->A->real) (s + 1) ((v:real->A->real^N^N) r))
      real_continuous_on real_interval[a,b'] /\
    (\r. pde_mnorm2 atlas n0 cs (psi:num->A->real) s ((f:real->A->real^N^N) r))
      real_continuous_on real_interval[a,b']`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PDE_ME_MNORM2_CNORM] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* nonnegativity *)
  SUBGOAL_THEN
   `!r. a <= r /\ r < b
        ==> &0 <= pde_mnorm2 atlas n0 cs (psi:num->A->real) s ((f:real->A->real^N^N) r) /\
            &0 <= pde_mnorm2 atlas n0 cs psi (s + 1) ((v:real->A->real^N^N) r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks':num->real^N->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Y = \r. pde_mnorm2 atlas n0 cs (psi:num->A->real) (s + 1)
                        ((v:real->A->real^N^N) r)` THEN
  ABBREV_TAC `Fm = \r. pde_mnorm2 atlas n0 cs (psi:num->A->real) s
                         ((f:real->A->real^N^N) r)` THEN
  (* the key inequality *)
  SUBGOAL_THEN
   `!t'. t' IN real_interval[a,t]
         ==> (Y:real->real) t' <= C0 * (real_integral (real_interval[a,t']) Fm +
                                        real_integral (real_interval[a,t']) Y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t':real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Y:real->real) real_continuous_on real_interval[a,t'] /\
                  (Fm:real->real) real_continuous_on real_interval[a,t']`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[a,b']` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_ADD; REAL_INTEGRABLE_CONTINUOUS] THEN
    SUBGOAL_THEN
     `(Y:real->real) t' =
      sum {i:num | i < n0}
        (\i. pde_me_cnorm atlas ((cs:num->(A->bool)#(A->real^N)) i) ((psi:num->A->real) i)
               (s + 1) ((v:real->A->real^N^N) t'))`
    SUBST1_TAC THENL [EXPAND_TAC "Y" THEN REWRITE_TAC[PDE_ME_MNORM2_CNORM]; ALL_TAC] THEN
    EXPAND_TAC "C0" THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "ch" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i:num < n0`))) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:real->A->real^N^N`; `v:real->A->real^N^N`] o
      check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "pde_mlin_sol")) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_var t && fst(dest_var t) = "TH")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_continuous_on"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\r. (Fm:real->real) r + (Y:real->real) r`; `&1 + (D:num->real) i`;
                   `real_interval[a,t']`] REAL_INTEGRAL_LMUL) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[ETA_AX];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[a,b']` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN EXPAND_TAC "Fm" THEN EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `a <= r /\ r < b` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks':num->real^N->bool`;
                     `psi:num->A->real`; `(f:real->A->real^N^N) r`; `s:num`; `i:num`]
                    PDE_ME_CNORM_LE_MNORM2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(v:real->A->real^N^N) r` o check (fun th ->
        can (find_term (fun t -> is_var t && fst(dest_var t) = "TH")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tensor_smooth"))
            (concl th) && is_forall (concl th))) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mnorm2")) (concl th) &&
        can (find_term (fun t -> is_var t && fst(dest_var t) = "f")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= Fv /\ y <= Dd * Yv /\ &0 <= Dd /\ &0 <= Fv /\ &0 <= Yv /\ &0 <= Dd * Fv
        ==> x + y <= (&1 + Dd) * (Fv + Yv)`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL]];
    ALL_TAC] THEN
  (* Gronwall *)
  MP_TAC(ISPECL [`Y:real->real`; `Fm:real->real`; `C0:real`; `a:real`; `t:real`]
                PDE_ME_GRONWALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[a,b']` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[a,b']` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "Fm" THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mnorm2")) (concl th) &&
        can (find_term (fun t -> is_var t && fst(dest_var t) = "f")) (concl th) &&
        is_forall (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Y:real->real) t = pde_mnorm2 atlas n0 cs (psi:num->A->real) (s + 1)
                         ((v:real->A->real^N^N) t)`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "Y" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[a,b']` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "Fm" THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mnorm2")) (concl th) &&
        can (find_term (fun t -> is_var t && fst(dest_var t) = "f")) (concl th) &&
        is_forall (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]]);;

(* ========================================================================= *)
(* Uniqueness PDE_MLIN_UNIQUE.  The difference of two solutions solves the   *)
(* homogeneous problem with zero data (linearity of the operator, in charts  *)
(* on open sets); the energy estimate with s = 0 makes its chart norms       *)
(* vanish; a vanishing chart norm forces the cut-off chart representative to *)
(* vanish, and the chart representative determines the tensor (the chart     *)
(* Jacobian is invertible).                                                  *)
(* ========================================================================= *)

(* Linearity of the operators on open sets. *)

let PDE_ME_LOP0_SUB_OPEN = prove
 (`!U (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K) v x.
     open U /\ smooth_map_on U u /\ smooth_map_on U v /\ x IN U
     ==> pde_lop0 A B C (\y. u y - v y) x = pde_lop0 A B C u x - pde_lop0 A B C v x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!l. iterated_partial l (\y. (u:real^N->real^K) y - v y) x =
        iterated_partial l u x - iterated_partial l v x`
  MP_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `u:real^N->real^K`;
                                `v:real^N->real^K`] TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(GEN `i:num` (SPEC `[i:num]` th)) THEN
    MP_TAC(GEN `i:num` (GEN `j:num` (SPEC `[i:num; j:num]` th)))) THEN
  REWRITE_TAC[iterated_partial] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[pde_lop0] THEN
  REWRITE_TAC[VECTOR_SUB_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB; VSUM_SUB_NUMSEG] THEN
  VECTOR_ARITH_TAC);;

let PDE_ME_LTRHESS_SUB = prove
 (`!U (K:real^N->real^N^N) H (V1:real^N->real^N^N) V2 y.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V1) /\
     smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V2) /\
     metric_field U H /\ y IN U
     ==> pde_ltrhess K H (\z. V1 z - V2 z) y =
         pde_ltrhess K H V1 y - pde_ltrhess K H V2 y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
  REWRITE_TAC[VECTORIZE_SUB] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z. (V1:real^N->real^N^N) z - V2 z) =
    (\z. (vectorize o V1) z - (vectorize o V2) z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     (\z. (V1:real^N->real^N^N) z - V2 z))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `\z. (V1:real^N->real^N^N) z - V2 z`; `y:real^N`] PDE_ML_LOP0_FORM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `V1:real^N->real^N^N`; `y:real^N`] PDE_ML_LOP0_FORM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `V2:real^N->real^N^N`; `y:real^N`] PDE_ML_LOP0_FORM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC PDE_ME_LOP0_SUB_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let PDE_ME_TRHESS_SUB = prove
 (`!top atlas (K:A->real^N^N) h (v:A->real^N^N) w x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     mfd_tensor2_smooth atlas v /\ mfd_tensor2_smooth atlas w /\ x IN topspace top
     ==> pde_trhess atlas K h (\x. v x - w x) x =
         pde_trhess atlas K h v x - pde_trhess atlas K h w x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_trhess; METRIC_LOCAL_SUB; ETA_AX] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_ME_LTRHESS_SUB THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_tensor2_smooth; riemannian_metric]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* Time families: differences and the zero family. *)

let PDE_ME_TFAM_SUB = prove
 (`!top atlas a b (v:real->A->real^N^N) w.
     smooth_manifold_atlas top atlas /\
     pde_tfam_from atlas a b v /\ pde_tfam_from atlas a b w
     ==> pde_tfam_from atlas a b (\t x. v t x - w t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`)) THEN
  ASM_REWRITE_TAC[METRIC_LOCAL_SUB; VECTORIZE_SUB; ETA_AX] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB] THEN MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `\x:real^(N,N)finite_prod. --x`;
                 `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas (c:(A->bool)#(A->real^N))
                             ((w:real->A->real^N^N) t) y)`]
                PDE_MT_UPTO_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC; REWRITE_TAC[]]);;

let PDE_ME_TFAM_ZERO = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a b.
     pde_tfam_from atlas a b (\t:real x:A. mat 0:real^N^N)`,
  REWRITE_TAC[PDM_TFAM_FROM_UPTO; metric_local; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO;
              VECTORIZE_0; PDE_MT_UPTO_CONST_OPEN]);;

(* The difference of two solutions solves the homogeneous problem. *)

let PDE_ME_MLIN_SOL_SUB = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v0 v w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\ pde_mlin_sol (top,atlas) a b k h f v0 w
     ==> pde_mlin_sol (top,atlas) a b k h (\t x. mat 0) (\x. mat 0)
                      (\t x. v t x - w t x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t) /\
            mfd_tensor2_smooth atlas ((w:real->A->real^N^N) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_MESON_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pde_mlin_sol]) THEN REWRITE_TAC[pde_mlin_sol] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MATRIX_SUB_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_SUB_COMPONENT; MATRIX_ADD_RID] THEN
  SUBGOAL_THEN
   `pde_trhess atlas ((k:real->A->real^N^N) t) h (\x. (v:real->A->real^N^N) t x - w t x) x =
    pde_trhess atlas (k t) h (v t) x - pde_trhess atlas (k t) h (w t) x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PDE_ME_TRHESS_SUB THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_SUB_COMPONENT] THEN
  SUBGOAL_THEN
   `pde_trhess atlas ((k:real->A->real^N^N) t) h ((v:real->A->real^N^N) t) x$i$j -
    pde_trhess atlas (k t) h ((w:real->A->real^N^N) t) x$i$j =
    (pde_trhess atlas (k t) h (v t) x + (f:real->A->real^N^N) t x)$i$j -
    (pde_trhess atlas (k t) h (w t) x + f t x)$i$j`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_ADD_COMPONENT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_SIMP_TAC[]);;

(* Zero data have zero norms. *)

let PDE_ME_MNORM2_ZERO = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) n0 cs psi s.
     pde_mnorm2 atlas n0 cs psi s (\x. mat 0) = &0`,
  REWRITE_TAC[pde_mnorm2; metric_local; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO;
              MATRIX_CMUL_RZERO; VECTORIZE_0; TEXT_ITERATED_PARTIAL_ZERO; NORM_0;
              REAL_POW_2; REAL_MUL_LZERO; LIFT_NUM; INTEGRAL_0; DROP_VEC; SUM_0]);;

(* A continuous function on an open set whose squared norm has integral 0  *)
(* vanishes there.                                                          *)

let PDE_ME_SQ_INTEGRAL_ZERO = prove
 (`!s (w:real^M->real^K).
     open s /\ w continuous_on s /\
     (\y. lift(norm(w y) pow 2)) integrable_on s /\
     drop(integral s (\y. lift(norm(w y) pow 2))) = &0
     ==> !y. y IN s ==> w y = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((\y. lift(norm((w:real^M->real^K) y) pow 2)) has_integral vec 0) s`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `integral s (\y. lift(norm((w:real^M->real^K) y) pow 2)) = vec 0`
      (fun th -> REWRITE_TAC[GSYM th]) THENL
     [ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. lift(norm((w:real^M->real^K) y) pow 2)`; `s:real^M->bool`]
                HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `{y:real^M | y IN s /\ (w:real^M->real^K) y IN (:real^K) DIFF {vec 0}} = {}`
  MP_TAC THENL
   [MATCH_MP_TAC(MESON[OPEN_NOT_NEGLIGIBLE]
      `open (u:real^M->bool) /\ negligible u ==> u = {}`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{y:real^M | y IN s /\ ~(lift(norm((w:real^M->real^K) y) pow 2) = vec 0)}` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ; REAL_POW_EQ_0; NORM_EQ_0; ARITH_EQ] THEN
      MESON_TAC[]];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
    MESON_TAC[]]);;

(* A vanishing chart norm forces the cut-off chart representative to vanish. *)

let PDE_ME_CNORM_ZERO_IMP = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) kp (w:A->real^N^N) s.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact kp /\ kp SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) kp) /\ pde_tensor_smooth atlas w /\
     pde_me_cnorm atlas c phi s w = &0
     ==> !z. z IN IMAGE (SND c) (FST c)
             ==> phi(chart_inv c z) %% metric_local atlas c w z = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `w:A->real^N^N`;
                 `kp:real^N->bool`] PDM_CHART_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l. (\y. lift(norm(iterated_partial l
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                   ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                    metric_local atlas c (w:A->real^N^N) z)) y) pow 2))
        integrable_on IMAGE (SND c) (FST c) /\
        &0 <= drop(integral (IMAGE (SND c) (FST c))
                (\y. lift(norm(iterated_partial l
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (phi(chart_inv c z) %% metric_local atlas c w z)) y) pow 2)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `kp:real^N->bool`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                         metric_local atlas c (w:A->real^N^N) z)`; `l:num list`]
                  PDM_ZERO_EXT_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `pde_me_cnorm atlas (c:(A->bool)#(A->real^N)) phi s (w:A->real^N^N) = &0` THEN
  REWRITE_TAC[pde_me_cnorm] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[SUM_POS_EQ_0]
   `!(f:(num)list->real) s. sum s f = &0
          ==> FINITE s ==> (!x. x IN s ==> &0 <= f x) ==> !x. x IN s ==> f x = &0`)) THEN
  ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  DISCH_THEN(MP_TAC o SPEC `[]:num list`) THEN
  REWRITE_TAC[PDE_INDEX_LISTS_NIL] THEN REWRITE_TAC[iterated_partial] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                       metric_local atlas c (w:A->real^N^N) z)`] PDE_ME_SQ_INTEGRAL_ZERO) THEN
  ASM_REWRITE_TAC[VECTORIZE_EQ_0] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPEC `[]:num list`) THEN
    REWRITE_TAC[iterated_partial]]);;

(* The chart representative determines the tensor. *)

let PDE_ME_METRIC_LOCAL_EQ_0 = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (W:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c /\
     metric_local atlas c W (SND c x) = mat 0
     ==> W x = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = (x:A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `J = matrix(chart_jac (c:(A->bool)#(A->real^N)) c0 (x:A))` THEN
  SUBGOAL_THEN `invertible(J:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[chart_jac] THEN
    MATCH_MP_TAC PDE_DIFFEO_JAC_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST (c:(A->bool)#(A->real^N)) INTER FST c0)`;
      `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`;
      `chart_trans (c0:(A->bool)#(A->real^N)) (c:(A->bool)#(A->real^N))`] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
                    CHART_TRANS_DIFFEO) THEN
      ASM_REWRITE_TAC[PAIR];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `metric_local atlas (c:(A->bool)#(A->real^N)) (W:A->real^N^N) (SND c x) = mat 0` THEN
  ASM_REWRITE_TAC[metric_local] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`J:real^N^N`; `(W:A->real^N^N) x`] PDE_ML_UNCONGR) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO]);;

(* Uniqueness. *)

let PDE_MLIN_UNIQUE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b k h f v0 v w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        riemannian_metric atlas h /\
        (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
        pde_tfam_from atlas a b k /\
        pde_mlin_sol (top,atlas) a b k h f v0 v /\ pde_mlin_sol (top,atlas) a b k h f v0 w
        ==> !t x. a <= t /\ t < b /\ x IN topspace top ==> v t x = w t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                 `v0:A->real^N^N`; `v:real->A->real^N^N`; `w:real->A->real^N^N`]
                PDE_ME_MLIN_SOL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                PDE_COVER_CUTOFFS_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `cs:num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `ks:num->real^N->bool` (X_CHOOSE_THEN `psi:num->A->real`
      STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
  SUBGOAL_THEN `pde_tensor_smooth atlas (\x. (v:real->A->real^N^N) t x - w t x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `\t x. (v:real->A->real^N^N) t x - w t x`; `t:real`] PDE_ML_TFAM_SLICE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  (* the energy estimate with s = 0 up to (t + b) / 2 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `a:real`; `b:real`; `(t + b) / &2`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                 `0`] PDE_MLIN_ENERGY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (MP_TAC o SPECL
    [`\t:real x:A. mat 0:real^N^N`; `\t x. (v:real->A->real^N^N) t x - w t x`])) THEN
  ASM_REWRITE_TAC[PDE_ME_TFAM_ZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PDE_ME_MNORM2_ZERO; REAL_INTEGRAL_0; REAL_MUL_RZERO; ADD_CLAUSES] THEN
  DISCH_TAC THEN
  (* a cutoff equal to 1 at x *)
  MP_TAC(ASSUME `pde_cutoffs (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                          (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real)`) THEN
  REWRITE_TAC[pde_cutoffs] THEN DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(psi:num->A->real) i x = &1` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i)) (ks i)`
  MP_TAC THENL [ASM_MESON_TAC[REAL_ARITH `~(&1 = &0)`]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  MP_TAC(ASSUME `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                         (cs:num->(A->bool)#(A->real^N)) (ks:num->real^N->bool)`) THEN
  REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) i) /\ SND(cs i) x = y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the chart norms of the difference vanish *)
  SUBGOAL_THEN
   `!j. j < n0
        ==> &0 <= pde_me_cnorm atlas ((cs:num->(A->bool)#(A->real^N)) j) ((psi:num->A->real) j)
                    1 (\x. (v:real->A->real^N^N) t x - w t x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_ME_CNORM_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) j`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pde_cover; pde_cutoffs]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_me_cnorm atlas ((cs:num->(A->bool)#(A->real^N)) i) ((psi:num->A->real) i)
                 1 (\x. (v:real->A->real^N^N) t x - w t x) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\j. pde_me_cnorm atlas ((cs:num->(A->bool)#(A->real^N)) j) ((psi:num->A->real) j)
                        1 (\x. (v:real->A->real^N^N) t x - w t x)`; `{j:num | j < n0}`]
     SUM_POS_EQ_0) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[GSYM PDE_ME_MNORM2_CNORM];
        MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]];
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* hence the chart representative of the difference vanishes at y *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`; `\x. (v:real->A->real^N^N) t x - w t x`; `1`]
                PDE_ME_CNORM_ZERO_IMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `pde_cutoffs (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                          (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real)`) THEN
      REWRITE_TAC[pde_cutoffs] THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[MATRIX_CMUL_LID] THEN
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `\x. (v:real->A->real^N^N) t x - w t x`;
                 `x:A`] PDE_ME_METRIC_LOCAL_EQ_0) THEN
  ASM_REWRITE_TAC[]);;

