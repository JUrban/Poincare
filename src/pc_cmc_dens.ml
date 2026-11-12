(* ========================================================================= *)
(* Unit pc_cmc_dens: planar densities for the compactness theorem:           *)
(*   - global weak partials of planar maps and their restrictions to open    *)
(*     sets; the energy integral cmc_pen as wan_gdir on open sets;           *)
(*     additivity and monotonicity of cmc_pen;                               *)
(*   - 2x2 algebra of the trace density: the Gram matrices of a jet, the     *)
(*     G-trace is twice the area density, area <= energy/2, the bound        *)
(*     |tau_Q| <= (M/lam) trace(Gram_G); continuity of the jet density;      *)
(*   - convergence of density integrals under L^2 convergence of jets        *)
(*     (fast subsequence, Beppo Levi dominator, dominated convergence,       *)
(*     and the sub-subsequence principle).                                   *)
(* ========================================================================= *)

needs "src/pc_cmc_defs.ml";;
needs "src/pc_cmw_reg.ml";;
needs "src/pc_hm_dexist.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Global weak partials.                                                     *)
(* ------------------------------------------------------------------------- *)

let CMC_PMAP_WD = prove
 (`!S (w:real^2->real^K) i.
     cmc_pmap S w /\ 1 <= i /\ i <= 2
     ==> wan_wd (:real^2) i w IN lspace (:real^2) (&2) /\
         wan_wpd (:real^2) i w (wan_wd (:real^2) i w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_pmap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]);;

let CMC_WD_EQ_AE = prove
 (`!(u:real^2->real^K) i v.
     wan_wpd (:real^2) i u v /\ v IN lspace (:real^2) (&2)
     ==> negligible {x | ~(wan_wd (:real^2) i u x = v x)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd (:real^2) i (u:real^2->real^K) IN lspace (:real^2) (&2) /\
                wan_wpd (:real^2) i (u:real^2->real^K) (wan_wd (:real^2) i u)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `i:num`; `u:real^2->real^K`;
                 `wan_wd (:real^2) i (u:real^2->real^K)`; `v:real^2->real^K`]
                WAN_WPD_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

(* Restriction of the global weak partials to an open set s.                 *)

let CMC_WD_RESTRICT = prove
 (`!S (w:real^2->real^K) s i.
     cmc_pmap S w /\ open s /\ 1 <= i /\ i <= 2
     ==> wan_wd (:real^2) i w IN lspace s (&2) /\
         wan_wpd s i w (wan_wd (:real^2) i w) /\
         negligible {x | x IN s /\ ~(wan_wd s i w x = wan_wd (:real^2) i w x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `i:num`] CMC_PMAP_WD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wpd s i (w:real^2->real^K) (wan_wd (:real^2) i w)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_wd (:real^2) i (w:real^2->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wan_wd s i (w:real^2->real^K) IN lspace s (&2) /\
                wan_wpd s i w (wan_wd s i w)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC WAN_WPD_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `w:real^2->real^K`] THEN ASM_REWRITE_TAC[ETA_AX]);;

(* Planar maps are W^{1,2} on bounded open sets.                             *)

let CMC_PMAP_W12 = prove
 (`!S (w:real^2->real^K) s.
     cmc_pmap S w /\ compact S /\ open s /\ bounded s ==> wan_w12 s w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_w12; DIMINDEX_2] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cmc_pmap]) THEN STRIP_TAC THEN
    MATCH_MP_TAC LSPACE_BOUNDED_MEASURABLE_SIMPLE THEN
    ASM_SIMP_TAC[MEASURABLE_OPEN; REAL_ARITH `&0 < &2`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `S:real^K->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN ASM SET_TAC[]];
    REPEAT STRIP_TAC THEN EXISTS_TAC `wan_wd (:real^2) i (w:real^2->real^K)` THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `s:real^2->bool`; `i:num`]
                  CMC_WD_RESTRICT) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The planar densities through the 3x3 jet densities of pc_cmw_reg: a     *)
(* planar jet (p,a1,a2) is the 3-jet (a1,a2,0), whose 3x3 Gram matrix has  *)
(* the 2x2 Gram matrix in its upper left corner and zeros elsewhere.       *)
(* ------------------------------------------------------------------------- *)

let cmc_j3 = new_definition
 `cmc_j3 (a1:real^K) (a2:real^K) =
    pastecart a1 (pastecart a2 (vec 0)):real^(K,(K,K)finite_sum)finite_sum`;;

let CMC_C3_J3 = prove
 (`!(a1:real^K) a2.
     cmw_c3 (cmc_j3 a1 a2) 1 = a1 /\ cmw_c3 (cmc_j3 a1 a2) 2 = a2 /\
     cmw_c3 (cmc_j3 a1 a2) 3 = vec 0`,
  REWRITE_TAC[cmw_c3; cmc_j3; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The 3x3 Gram matrix of the 3-jet (a1,a2,0) and the 2x2 Gram matrix.      *)

let CMC_GRAM3_EXPAND = prove
 (`!(a1:real^K) a2 (H:real^K^K) i j.
     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
     ==> (transp(cmw_jx (cmc_j3 a1 a2)) ** H ** cmw_jx (cmc_j3 a1 a2))$i$j =
         (if i = 3 \/ j = 3 then &0
          else (if i = 1 then a1 else a2) dot (H ** (if j = 1 then a1 else a2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[CMW_GRAM_JX] THEN
  REWRITE_TAC[cmw_c3; cmc_j3; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[DOT_LZERO; DOT_RZERO; MATRIX_VECTOR_MUL_RZERO] THEN ASM_ARITH_TAC);;

let CMC_GRAM2_ENTRIES = prove
 (`!(G:real^K->real^K^K) (w:real^2->real^K) x.
     (cmc_gram G w x)$1$1 =
       wan_wd (:real^2) 1 w x dot (G(w x) ** wan_wd (:real^2) 1 w x) /\
     (cmc_gram G w x)$1$2 =
       wan_wd (:real^2) 1 w x dot (G(w x) ** wan_wd (:real^2) 2 w x) /\
     (cmc_gram G w x)$2$1 =
       wan_wd (:real^2) 2 w x dot (G(w x) ** wan_wd (:real^2) 1 w x) /\
     (cmc_gram G w x)$2$2 =
       wan_wd (:real^2) 2 w x dot (G(w x) ** wan_wd (:real^2) 2 w x)`,
  SIMP_TAC[cmc_gram; LAMBDA_BETA; DIMINDEX_2; ARITH]);;

let CMC_GRAM_3_2 = prove
 (`!(M:real^3^3) (N:real^3^3) (A:real^2^2) (B:real^2^2).
     M$1$3 = &0 /\ M$2$3 = &0 /\ M$3$1 = &0 /\ M$3$2 = &0 /\ M$3$3 = &0 /\
     N$1$3 = &0 /\ N$2$3 = &0 /\ N$3$1 = &0 /\ N$3$2 = &0 /\ N$3$3 = &0 /\
     A$1$1 = M$1$1 /\ A$1$2 = M$1$2 /\ A$2$1 = M$2$1 /\ A$2$2 = M$2$2 /\
     B$1$1 = N$1$1 /\ B$1$2 = N$1$2 /\ B$2$1 = N$2$1 /\ B$2$2 = N$2$2
     ==> det A = p4_e2 M /\ trace A = trace M /\
         trace A * trace B - trace(A ** B) = p4_e2_pol M N`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DET_2; trace; p4_e2; p4_e2_pol; matrix_mul] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_2; DIMINDEX_3; ARITH; SUM_2; SUM_3] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMC_TDEN_3 = prove
 (`!(G:real^K->real^K^K) Q (w:real^2->real^K) x.
     cmc_tden G Q w x =
     cmw_tdens G Q (w x) (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x)) /\
     trace(cmc_gram G w x) =
     trace(transp(cmw_jx (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))) **
           G(w x) ** cmw_jx (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))) /\
     det(cmc_gram G w x) =
     p4_e2(transp(cmw_jx (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))) **
           G(w x) ** cmw_jx (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`transp(cmw_jx (cmc_j3 (wan_wd (:real^2) 1 (w:real^2->real^K) x)
                           (wan_wd (:real^2) 2 w x))) **
     (G:real^K->real^K^K)(w x) **
     cmw_jx (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))`;
    `transp(cmw_jx (cmc_j3 (wan_wd (:real^2) 1 (w:real^2->real^K) x)
                           (wan_wd (:real^2) 2 w x))) **
     (Q:real^K->real^K^K)(w x) **
     cmw_jx (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))`;
    `cmc_gram (G:real^K->real^K^K) (w:real^2->real^K) x`;
    `cmc_gram (Q:real^K->real^K^K) (w:real^2->real^K) x`] CMC_GRAM_3_2) THEN
  SIMP_TAC[CMC_GRAM3_EXPAND; CMC_GRAM2_ENTRIES; ARITH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[cmc_tden; cmw_tdens]);;

(* ------------------------------------------------------------------------- *)
(* Convergence of density integrals.  A density phi, continuous on the jet   *)
(* space and bounded by C |z|^2 on a set D containing the jets, has          *)
(* convergent integrals along any sequence of jets converging in L^2(E): a   *)
(* fast subsequence has a Beppo Levi dominator, dominated convergence        *)
(* applies, and every subsequence has such a sub-subsequence.                *)
(* ------------------------------------------------------------------------- *)

(* The sub-subsequence principle for real sequences.                         *)

let CMC_SUBSUB = prove
 (`!(a:num->real) l.
     (!r:num->num. (!m n. m < n ==> r m < r n)
                   ==> ?q:num->num. (!m n. m < n ==> q m < q n) /\
                                    ((\n. a(r(q n))) ---> l) sequentially)
     ==> (a ---> l) sequentially`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `{n:num | e <= abs((a:num->real) n - l)}` INFINITE_ENUMERATE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INFINITE] THEN DISCH_THEN(MP_TAC o ISPEC `\n:num. n` o
      MATCH_MP UPPER_BOUND_FINITE_SET) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num` o REWRITE_RULE[IN_ELIM_THM]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o SPEC `N + 1` o
      check (fun th -> is_exists(snd(dest_forall(concl th))))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:num->num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:num->num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN REWRITE_TAC[LE_REFL] THEN
  SUBGOAL_THEN `(r:num->num)(q(N:num)) IN {n:num | e <= abs((a:num->real) n - l)}` MP_TAC
  THENL [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
         REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
         REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

(* A fast subsequence of a sequence tending to 0.                            *)

let CMC_FAST_SUBSEQ = prove
 (`!(b:num->real).
     (b ---> &0) sequentially
     ==> ?q:num->num. (!m n. m < n ==> q m < q n) /\
                      !j. abs(b(q j)) <= inv(&2) pow j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. ?N. !n. N <= n ==> abs((b:num->real) n) <= inv(&2) pow j` MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2) pow j` o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_SUB_RZERO; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `NN:num->num`) THEN
  EXISTS_TAC `\j. j + nsum(0..j) (NN:num->num)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a:num <= b ==> a <= j + b`) THEN
  MP_TAC(ISPECL [`{j:num}`; `0..j`; `NN:num->num`] NSUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[NSUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; LE_0; LE_REFL]);;

let CMC_DROP_VSUM = prove
 (`!s (f:num->real^1). drop(vsum s f) = sum s (\i. drop(f i))`,
  REWRITE_TAC[DROP_VSUM; o_DEF]);;

let CMC_GEOM_LE2 = prove
 (`!n. sum(0..n) (\j. inv(&2) pow j) <= &2 - inv(&2) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; real_pow] THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;

let CMC_LIFT_SUM = prove
 (`!s (f:num->real). lift(sum s f) = vsum s (\i. lift(f i))`,
  REWRITE_TAC[LIFT_SUM; o_DEF]);;

(* A Beppo Levi dominator for nonnegative functions with geometrically       *)
(* small integrals; they also tend to 0 almost everywhere.                  *)

let CMC_BEPPO_DOM = prove
 (`!(g:num->real^2->real) E.
     lebesgue_measurable E /\
     (!j. (\x. lift(g j x)) integrable_on E) /\
     (!j x. x IN E ==> &0 <= g j x) /\
     (!j. drop(integral E (\x. lift(g j x))) <= inv(&2) pow j)
     ==> ?H N. negligible N /\ (\x. lift(H x)) integrable_on E /\
               (!j x. x IN E DIFF N ==> g j x <= H x) /\
               (!x. x IN E DIFF N ==> ((\j. g j x) ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(sum(0..n) (\j. (g:num->real^2->real) j x))`; `E:real^2->bool`]
                BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[CMC_LIFT_SUM] THEN
      MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
      REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; SUM_CLAUSES_NUMSEG; LE_0] THEN
      ASM_SIMP_TAC[REAL_LE_ADDR];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `&2` THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[CMC_LIFT_SUM] THEN
      ASM_SIMP_TAC[INTEGRAL_VSUM; FINITE_NUMSEG] THEN
      REWRITE_TAC[NORM_1; CMC_DROP_VSUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\j. inv(&2) pow j)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
          ASM_SIMP_TAC[LIFT_DROP];
          MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]];
        MP_TAC(SPEC `n:num` CMC_GEOM_LE2) THEN
        MP_TAC(SPECL [`inv(&2)`; `n:num`] REAL_POW_LE) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Hv:real^2->real^1` (X_CHOOSE_THEN `N:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`\x:real^2. drop(Hv x)`; `N:real^2->bool`] THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `x:real^2`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\n. lift(sum(0..n) (\j. (g:num->real^2->real) j x))` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `j:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`{j:num}`; `0..n`; `\j:num. (g:num->real^2->real) j x`]
                  SUM_SUBSET_SIMPLE) THEN
    REWRITE_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; LE_0] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN ASM_MESON_TAC[IN_DIFF];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\j. (g:num->real^2->real) j x) real_sums drop(Hv x)) (from 0)` MP_TAC
  THENL
   [REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
    REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP] THEN ASM_SIMP_TAC[ETA_AX];
    DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP REAL_SERIES_TERMS_TOZERO)]);;

let CMC_NORM_SQ_SPLIT = prove
 (`!a b:real^N. norm a pow 2 <= &2 * norm b pow 2 + &2 * norm(a - b) pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`b:real^N`; `a - b:real^N`] NORM_TRIANGLE) THEN
  REWRITE_TAC[VECTOR_ARITH `b + a - b:real^N = a`] THEN
  MP_TAC(ISPEC `a:real^N` NORM_POS_LE) THEN
  MP_TAC(ISPEC `b:real^N` NORM_POS_LE) THEN MP_TAC(ISPEC `a - b:real^N` NORM_POS_LE) THEN
  MAP_EVERY ABBREV_TAC [`x = norm(a:real^N)`; `y = norm(b:real^N)`; `z = norm(a - b:real^N)`] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `x pow 2 <= (y + z) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    MP_TAC(SPEC `y - z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

(* Integrability of a density of a jet in L^2.                               *)

let CMC_JET_INTEGRABLE = prove
 (`!(FF:real^2->real^N) E (phi:real^N->real) D C.
     lebesgue_measurable E /\ &0 <= C /\
     (\z. lift(phi z)) continuous_on (:real^N) /\
     (!z. z IN D ==> abs(phi z) <= C * norm z pow 2) /\
     (!x. x IN E ==> FF x IN D) /\ FF IN lspace E (&2)
     ==> (\x. lift(phi(FF x))) integrable_on E`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. C % lift(norm((FF:real^2->real^N) x) pow 2)` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`FF:real^2->real^N`; `\z:real^N. lift(phi z)`; `E:real^2->bool`]
                  HMC_MEAS_COMPOSE) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(FF:real^2->real^N) IN lspace E (&2)` THEN SIMP_TAC[lspace; IN_ELIM_THM];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP] THEN ASM_SIMP_TAC[]]);;

(* Dominated convergence for densities of jets converging in L^2.            *)

let CMC_JET_DCT = prove
 (`!(FF:num->real^2->real^N) F0 E (phi:real^N->real) D C.
     lebesgue_measurable E /\ &0 <= C /\
     (\z. lift(phi z)) continuous_on (:real^N) /\
     (!z. z IN D ==> abs(phi z) <= C * norm z pow 2) /\
     (!j x. x IN E ==> FF j x IN D) /\ (!x. x IN E ==> F0 x IN D) /\
     (!j. FF j IN lspace E (&2)) /\ F0 IN lspace E (&2) /\
     ((\j. lnorm E (&2) (\x. FF j x - F0 x)) ---> &0) sequentially
     ==> (\x. lift(phi(F0 x))) integrable_on E /\
         ((\j. drop(integral E (\x. lift(phi(FF j x))))) --->
          drop(integral E (\x. lift(phi(F0 x))))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(phi((F0:real^2->real^N) x))) integrable_on E` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_JET_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC [`D:real^N->bool`; `C:real`] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `!j. (\x. lift(phi((FF:num->real^2->real^N) j x))) integrable_on E`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMC_JET_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC [`D:real^N->bool`; `C:real`] THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. (\x. (FF:num->real^2->real^N) j x - F0 x) IN lspace E (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC CMC_SUBSUB THEN X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\j. lnorm E (&2) (\x. (FF:num->real^2->real^N) ((r:num->num) j) x - F0 x) pow 2`
               CMC_FAST_SUBSEQ) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `&0 = &0 pow 2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_POW THEN
    MP_TAC(ISPECL [`\k. lnorm E (&2) (\x. (FF:num->real^2->real^N) k x - F0 x)`; `&0`;
                   `r:num->num`] HMD_REALLIM_SUBSEQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:num->num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\j x. norm((FF:num->real^2->real^N) ((r:num->num)((q:num->num) j)) x - F0 x) pow 2`; `E:real^2->bool`]
   CMC_BEPPO_DOM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; REAL_LE_POW_2] THEN
    X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`\x. (FF:num->real^2->real^N) ((r:num->num)((q:num->num) (j:num))) x - F0 x`; `E:real^2->bool`]
                  WAN_SOB_LNORM2_SQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= a ==> y <= a`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
    MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^2->real` (X_CHOOSE_THEN `N:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`\k x. lift(phi((FF:num->real^2->real^N) ((r:num->num)((q:num->num) k)) x))`;
    `\x. lift(phi((F0:real^2->real^N) x))`;
    `\x. lift(&2 * C * (norm((F0:real^2->real^N) x) pow 2 + H x))`;
    `E DIFF (N:real^2->bool)`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `negligible((E DIFF (E DIFF N)) UNION ((E DIFF N) DIFF E):real^2->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `N:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
      EXISTS_TAC `E:real^2->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
      EXISTS_TAC `E:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIFT_CMUL; LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
      ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real^2`] THEN
      REWRITE_TAC[IN_DIFF; NORM_LIFT; LIFT_DROP] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C * norm((FF:num->real^2->real^N) ((r:num->num)((q:num->num) (k:num))) x) pow 2` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `norm((FF:num->real^2->real^N) ((r:num->num)((q:num->num) (k:num))) x - F0 x) pow 2 <= H x`
      MP_TAC THENL [ASM_SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
      MP_TAC(ISPECL [`(FF:num->real^2->real^N) ((r:num->num)((q:num->num) (k:num))) x`; `(F0:real^2->real^N) x`]
                    CMC_NORM_SQ_SPLIT) THEN
      DISCH_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C * (&2 * norm((F0:real^2->real^N) x) pow 2 +
                       &2 * norm((FF:num->real^2->real^N) ((r:num->num)((q:num->num) (k:num))) x - F0 x) pow 2)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `C * h <= C * hh ==> C * (&2 * a + &2 * h) <= &2 * C * (a + hh)`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\z:real^N. lift(phi z)`; `sequentially`;
                     `\k. (FF:num->real^2->real^N) ((r:num->num)((q:num->num) k)) x`;
                     `(F0:real^2->real^N) x`] LIM_CONTINUOUS_FUNCTION) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `(\z. lift((phi:real^N->real) z)) continuous_on (:real^N)` THEN
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `((\j. norm((FF:num->real^2->real^N) ((r:num->num)((q:num->num) j)) x - F0 x) pow 2) ---> &0) sequentially`
      MP_TAC THENL [ASM_SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; REALLIM_SEQUENTIALLY; dist; REAL_SUB_RZERO] THEN
      DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e pow 2`) THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!f:real^2->real^1. integral (E DIFF N) f = integral E f`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `N:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise facts on the planar densities: the Cauchy-Schwarz inequality    *)
(* for positive semidefinite forms, det(Gram) >= 0, the trace of G is twice  *)
(* the area density, area <= energy, and |tau_Q| <= M tr(Gram).              *)
(* ------------------------------------------------------------------------- *)

let CMC_PSD_CS = prove
 (`!(H:real^K^K) a b.
     transp H = H /\ (!v. &0 <= v dot (H ** v))
     ==> (a dot (H ** b)) pow 2 <= (a dot (H ** a)) * (b dot (H ** b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= a dot ((H:real^K^K) ** a) + &2 * t * (a dot (H ** b)) +
             t pow 2 * (b dot (H ** b))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a + t % b:real^K`) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    MP_TAC(ISPECL [`H:real^K^K`; `b:real^K`; `a:real^K`] HMC_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `b dot ((H:real^K^K) ** b) = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_CASES_TAC `a dot ((H:real^K^K) ** b) = &0` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `--(a dot ((H:real^K^K) ** a) + &1) / (&2 * (a dot (H ** b)))`) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(q = &0) ==> &2 * (--(p + &1) / (&2 * q)) * q = --(p + &1)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b dot ((H:real^K^K) ** b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(a dot ((H:real^K^K) ** b)) / (b dot (H ** b))`) THEN
  ABBREV_TAC `p = a dot ((H:real^K^K) ** a)` THEN
  ABBREV_TAC `q = a dot ((H:real^K^K) ** b)` THEN
  ABBREV_TAC `r = b dot ((H:real^K^K) ** b)` THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < r ==> p + &2 * (--q / r) * q + (--q / r) pow 2 * r = (p * r - q pow 2) / r`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

let CMC_GRAM_PSD_FACTS = prove
 (`!(G:real^K->real^K^K) (w:real^2->real^K) x.
     (!z. transp(G z) = G z) /\ (!z v. &0 <= v dot (G z ** v))
     ==> &0 <= det(cmc_gram G w x) /\ &0 <= trace(cmc_gram G w x) /\
         &2 * sqrt(det(cmc_gram G w x)) <= trace(cmc_gram G w x) /\
         cmc_tden G G w x = &2 * sqrt(det(cmc_gram G w x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cmc_tden; DET_2; trace; matrix_mul] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_2; ARITH; SUM_2; CMC_GRAM2_ENTRIES] THEN
  ABBREV_TAC `a1 = wan_wd (:real^2) 1 (w:real^2->real^K) x` THEN
  ABBREV_TAC `a2 = wan_wd (:real^2) 2 (w:real^2->real^K) x` THEN
  ABBREV_TAC `H = (G:real^K->real^K^K)((w:real^2->real^K) x)` THEN
  SUBGOAL_THEN `transp(H:real^K^K) = H /\ (!v. &0 <= v dot (H ** v))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:real^K^K`; `a1:real^K`; `a2:real^K`] CMC_PSD_CS) THEN
  MP_TAC(ISPECL [`H:real^K^K`; `a2:real^K`; `a1:real^K`] HMC_SYM_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= a1 dot ((H:real^K^K) ** a1) /\ &0 <= a2 dot (H ** a2)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `p = a1 dot ((H:real^K^K) ** a1)` THEN
  ABBREV_TAC `q = a1 dot ((H:real^K^K) ** a2)` THEN
  ABBREV_TAC `r = a2 dot ((H:real^K^K) ** a2)` THEN
  SUBGOAL_THEN `&0 <= p * r - q * q` ASSUME_TAC THENL
   [UNDISCH_TAC `q pow 2 <= p * r` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= s /\ s <= (p + r) / &2 ==> &2 * s <= p + r`) THEN
    ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `p - r:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SQRT_0; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `&0 < p * r - q * q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_FIELD `x = &2 * s pow 2 /\ &0 < s ==> x / s = &2 * s`) THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT] THEN REAL_ARITH_TAC);;

(* |tau_Q| <= M trace(Gram_G) for maps into S.                                *)

let CMC_TDEN_BOUND = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K).
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z)
     ==> ?M. &0 <= M /\
             !(w:real^2->real^K) x.
                w x IN S ==> abs(cmc_tden G Q w x) <= M * trace(cmc_gram G w x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  MP_TAC(ISPECL [`Q:real^K->real^K^K`; `S:real^K->bool`] CMT_QUAD_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M0 / lam` THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`w:real^2->real^K`; `x:real^2`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`; `w:real^2->real^K`; `x:real^2`]
                CMC_TDEN_3) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`; `w:real^2->real^K`; `x:real^2`]
                CMC_TDEN_3) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
    (ASSUME_TAC o SYM))) THEN
  REWRITE_TAC[cmw_tdens] THEN
  MP_TAC(ISPECL
   [`cmw_jx (cmc_j3 (wan_wd (:real^2) 1 (w:real^2->real^K) x) (wan_wd (:real^2) 2 w x))`;
    `(G:real^K->real^K^K)((w:real^2->real^K) x)`; `(Q:real^K->real^K^K)((w:real^2->real^K) x)`;
    `lam:real`; `M0:real`] CMT_TRDENS_BOUND) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^2->real^K`; `x:real^2`] CMC_GRAM_PSD_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2; REAL_LE_TRANS];
                  ALL_TAC] THEN
  STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `&2 * m * s <= m * t <=> m * (&2 * s) <= m * t`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Jets of planar maps and convergence of energy and trace integrals under   *)
(* L^2 convergence of values and weak partials on a bounded set.             *)
(* ------------------------------------------------------------------------- *)

let CMC_LSPACE2_PASTECART = prove
 (`!s (f:real^M->real^N) (g:real^M->real^P).
     f IN lspace s (&2) /\ g IN lspace s (&2)
     ==> (\x. pastecart (f x) (g x)) IN lspace s (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMW_LSPACE2; CMW_NORM_PASTECART_POW2] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_ON_PASTECART; LIFT_ADD; INTEGRABLE_ADD]);;

let CMC_LNORM2_PASTECART = prove
 (`!s (f:real^M->real^N) (g:real^M->real^P).
     f IN lspace s (&2) /\ g IN lspace s (&2)
     ==> lnorm s (&2) (\x. pastecart (f x) (g x)) pow 2 =
         lnorm s (&2) f pow 2 + lnorm s (&2) g pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMC_LSPACE2_PASTECART o CONJ (ASSUME `(f:real^M->real^N) IN lspace s (&2)`)) THEN
  DISCH_TAC THEN ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  REWRITE_TAC[CMW_NORM_PASTECART_POW2; LIFT_ADD] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; WAN_LSPACE2_SQNORM_INTEGRABLE; DROP_ADD]);;

let CMC_LNORM2_PASTECART_TOZERO = prove
 (`!s (f:num->real^M->real^N) (g:num->real^M->real^P).
     (!j. f j IN lspace s (&2)) /\ (!j. g j IN lspace s (&2)) /\
     ((\j. lnorm s (&2) (f j)) ---> &0) sequentially /\
     ((\j. lnorm s (&2) (g j)) ---> &0) sequentially
     ==> ((\j. lnorm s (&2) (\x. pastecart (f j x) (g j x))) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\j. sqrt(lnorm s (&2) ((f:num->real^M->real^N) j) pow 2 +
               lnorm s (&2) ((g:num->real^M->real^P) j) pow 2)) ---> &0) sequentially`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 = sqrt(&0 pow 2 + &0 pow 2)` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_0]; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT]; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_POW THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM CMC_LNORM2_PASTECART; ETA_AX] THEN
  MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC LNORM_POS_LE THEN
  ASM_SIMP_TAC[CMC_LSPACE2_PASTECART; ETA_AX; REAL_POS]);;

(* The jet (value, partial 1, partial 2, 0) of a map with given partials.   *)

let cmc_jet = new_definition
 `cmc_jet (v:real^2->real^K) (p1:real^2->real^K) (p2:real^2->real^K) (x:real^2) =
    pastecart (v x) (cmc_j3 (p1 x) (p2 x))`;;

let CMC_JET_SUB = prove
 (`!(v:real^2->real^K) p1 p2 v' p1' p2' x.
     cmc_jet v p1 p2 x - cmc_jet v' p1' p2' x =
     pastecart (v x - v' x)
       (pastecart (p1 x - p1' x) (pastecart (p2 x - p2' x) (vec 0)))`,
  REWRITE_TAC[cmc_jet; cmc_j3; PASTECART_SUB; VECTOR_SUB_REFL]);;

let CMC_JET_LSPACE = prove
 (`!(v:real^2->real^K) p1 p2 s.
     v IN lspace s (&2) /\ p1 IN lspace s (&2) /\ p2 IN lspace s (&2)
     ==> cmc_jet v p1 p2 IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cmc_jet (v:real^2->real^K) p1 p2 =
                \x. pastecart (v x) (pastecart (p1 x) (pastecart (p2 x) (vec 0)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cmc_jet; cmc_j3]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC LSPACE_0 THEN REAL_ARITH_TAC);;

(* L^2 convergence of jets from that of the components.                      *)

let CMC_JET_TOZERO = prove
 (`!(w:num->real^2->real^K) q1 q2 v p1 p2 s.
     (!j. (\x. w j x - v x) IN lspace s (&2)) /\
     (!j. (\x. q1 j x - p1 x) IN lspace s (&2)) /\
     (!j. (\x. q2 j x - p2 x) IN lspace s (&2)) /\
     ((\j. lnorm s (&2) (\x. w j x - v x)) ---> &0) sequentially /\
     ((\j. lnorm s (&2) (\x. q1 j x - p1 x)) ---> &0) sequentially /\
     ((\j. lnorm s (&2) (\x. q2 j x - p2 x)) ---> &0) sequentially
     ==> ((\j. lnorm s (&2) (\x. cmc_jet (w j) (q1 j) (q2 j) x - cmc_jet v p1 p2 x))
          ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CMC_JET_SUB] THEN
  SUBGOAL_THEN `(\x:real^2. vec 0:real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_0 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. lnorm s (&2)
          (\x. pastecart ((w:num->real^2->real^K) j x - v x)
                 (pastecart ((q1:num->real^2->real^K) j x - p1 x)
                    (pastecart ((q2:num->real^2->real^K) j x - p2 x) (vec 0:real^K)))) =
        sqrt(lnorm s (&2) (\x. w j x - v x) pow 2 +
             lnorm s (&2) (\x. q1 j x - p1 x) pow 2 +
             lnorm s (&2) (\x. q2 j x - p2 x) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN REWRITE_TAC[REAL_POS] THEN
      REPEAT(MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CMC_LNORM2_PASTECART o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CMC_LNORM2_PASTECART o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CMC_LNORM2_PASTECART o rand o rand o lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[LNORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = sqrt(&0 pow 2 + &0 pow 2 + &0 pow 2)` SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_0]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT] THEN
  REPEAT(MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC) THEN MATCH_MP_TAC REALLIM_POW THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Convergence of the trace and energy integrals of planar maps whose jets   *)
(* converge in L^2(E), and the basic facts on cmc_pen and cmc_ptr.           *)
(* ------------------------------------------------------------------------- *)

let CMC_EDEN_3 = prove
 (`!(G:real^K->real^K^K) (w:real^2->real^K) x.
     trace(cmc_gram G w x) =
     sum(1..3) (\i. cmw_edens G i (w x)
                      (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[trace; DIMINDEX_2; SUM_2; SUM_3; cmw_edens; CMC_C3_J3; CMC_GRAM2_ENTRIES] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_ADD_RID]);;

(* The two jet densities: continuous, homogeneous of degree 2, hence bounded *)
(* by M |a|^2 for p in the compact S.                                        *)

let CMC_JDENS_FACTS = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K).
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z)
     ==> (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
              lift(cmw_tdens G Q (fstcart z) (sndcart z))) continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) /\
         (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
              lift(sum(1..3) (\i. cmw_edens G i (fstcart z) (sndcart z))))
           continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) /\
         ?M. &0 <= M /\
             !p a. p IN S
                   ==> abs(cmw_tdens G Q p a) <= M * norm a pow 2 /\
                       abs(sum(1..3) (\i. cmw_edens G i p a)) <= M * norm a pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  SUBGOAL_THEN
   `(\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
         lift(cmw_tdens G Q (fstcart z) (sndcart z))) continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_TDENS_CONT THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
         lift(sum(1..3) (\i. cmw_edens G i (fstcart z) (sndcart z))))
    continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUM_3; LIFT_ADD] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`] CMW_EDENS_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmw_tdens (G:real^K->real^K^K) Q`; `S:real^K->bool`] CMW_HOMOG_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`]
      CMW_TDENS_HOMOG) THEN SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `M1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B1")))] THEN
  MP_TAC(ISPECL [`\p a. sum(1..3) (\i. cmw_edens (G:real^K->real^K^K) i p a)`;
                 `S:real^K->bool`] CMW_HOMOG_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`] CMW_EDENS_FACTS) THEN
    ASM_SIMP_TAC[GSYM SUM_LMUL; SUM_0];
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B2")))] THEN
  EXISTS_TAC `max M1 M2` THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= M1`; `&0 <= M2`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^K`; `a:real^(K,(K,K)finite_sum)finite_sum`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `M1 * norm(a:real^(K,(K,K)finite_sum)finite_sum) pow 2 <= max M1 M2 * norm a pow 2 /\
                M2 * norm(a:real^(K,(K,K)finite_sum)finite_sum) pow 2 <= max M1 M2 * norm a pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "B1" (MP_TAC o SPECL [`p:real^K`; `a:real^(K,(K,K)finite_sum)finite_sum`]) THEN
  REMOVE_THEN "B2" (MP_TAC o SPECL [`p:real^K`; `a:real^(K,(K,K)finite_sum)finite_sum`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`M1 * norm(a:real^(K,(K,K)finite_sum)finite_sum) pow 2 <= max M1 M2 * norm a pow 2`;
    `M2 * norm(a:real^(K,(K,K)finite_sum)finite_sum) pow 2 <= max M1 M2 * norm a pow 2`] THEN
  REAL_ARITH_TAC);;

(* Convergence of the trace and energy integrals.                            *)

let CMC_DENS_JET_CONV = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (w:num->real^2->real^K) v p1 p2 E.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\ lebesgue_measurable E /\
     (!j x. x IN E ==> w j x IN S) /\ (!x. x IN E ==> v x IN S) /\
     (!j. cmc_jet (w j) (wan_wd (:real^2) 1 (w j)) (wan_wd (:real^2) 2 (w j))
          IN lspace E (&2)) /\
     cmc_jet v p1 p2 IN lspace E (&2) /\
     ((\j. lnorm E (&2)
             (\x. cmc_jet (w j) (wan_wd (:real^2) 1 (w j)) (wan_wd (:real^2) 2 (w j)) x -
                  cmc_jet v p1 p2 x)) ---> &0) sequentially
     ==> ((\j. cmc_ptr G Q E (w j)) --->
          drop(integral E (\x. lift(cmw_tdens G Q (v x) (cmc_j3 (p1 x) (p2 x))))))
         sequentially /\
         ((\j. cmc_pen G E (w j)) --->
          drop(integral E (\x. lift(sum(1..3) (\i. cmw_edens G i (v x)
                                                      (cmc_j3 (p1 x) (p2 x)))))))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
                CMC_JDENS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MB"))))) THEN
  SUBGOAL_THEN
   `!z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
       z IN {z | fstcart z IN S}
       ==> abs(cmw_tdens G Q (fstcart z) (sndcart z)) <= M * norm z pow 2 /\
           abs(sum(1..3) (\i. cmw_edens G i (fstcart z) (sndcart z))) <= M * norm z pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `M * norm(sndcart(z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)) pow 2
                  <= M * norm z pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE; NORM_SNDCART];
      ALL_TAC] THEN
    REMOVE_THEN "MB" (MP_TAC o SPECL
     [`fstcart(z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`;
      `sndcart(z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `M * norm(sndcart(z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)) pow 2
                 <= M * norm z pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j x. x IN E
          ==> cmc_jet ((w:num->real^2->real^K) j) (wan_wd (:real^2) 1 (w j))
                      (wan_wd (:real^2) 2 (w j)) x IN {z | fstcart z IN S}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[cmc_jet; IN_ELIM_THM; FSTCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN E ==> cmc_jet (v:real^2->real^K) p1 p2 x IN {z | fstcart z IN S}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[cmc_jet; IN_ELIM_THM; FSTCART_PASTECART]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\j. cmc_jet ((w:num->real^2->real^K) j) (wan_wd (:real^2) 1 (w j))
                   (wan_wd (:real^2) 2 (w j))`;
      `cmc_jet (v:real^2->real^K) p1 p2`; `E:real^2->bool`;
      `\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
          cmw_tdens G Q (fstcart z) (sndcart z)`;
      `{z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum | fstcart z IN S}`;
      `M:real`] CMC_JET_DCT);
    MP_TAC(ISPECL
     [`\j. cmc_jet ((w:num->real^2->real^K) j) (wan_wd (:real^2) 1 (w j))
                   (wan_wd (:real^2) 2 (w j))`;
      `cmc_jet (v:real^2->real^K) p1 p2`; `E:real^2->bool`;
      `\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
          sum(1..3) (\i. cmw_edens G i (fstcart z) (sndcart z))`;
      `{z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum | fstcart z IN S}`;
      `M:real`] CMC_JET_DCT)] THEN
  REWRITE_TAC[] THEN
  (ANTS_TAC THENL [ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o CONJUNCT2) THEN
   REWRITE_TAC[cmc_jet; FSTCART_PASTECART; SNDCART_PASTECART] THEN
   REWRITE_TAC[cmc_ptr; cmc_pen; CMC_TDEN_3; CMC_EDEN_3]));;

(* ------------------------------------------------------------------------- *)
(* The energy and trace integrals of a planar map: integrability,            *)
(* positivity, monotonicity, additivity, |cmc_ptr| <= M cmc_pen, and cmc_pen *)
(* = wan_gdir on open sets.                                                  *)
(* ------------------------------------------------------------------------- *)

let CMC_TRACE_GRAM = prove
 (`!(G:real^K->real^K^K) (w:real^2->real^K) x.
     trace(cmc_gram G w x) =
     wan_wd (:real^2) 1 w x dot (G(w x) ** wan_wd (:real^2) 1 w x) +
     wan_wd (:real^2) 2 w x dot (G(w x) ** wan_wd (:real^2) 2 w x)`,
  REWRITE_TAC[trace; DIMINDEX_2; SUM_2; CMC_GRAM2_ENTRIES]);;

let CMC_PEN_INTEGRABLE = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) E.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable E
     ==> (\x. lift(trace(cmc_gram G w x))) absolutely_integrable_on E /\
         (!x. &0 <= trace(cmc_gram G w x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `!x. &0 <= trace(cmc_gram (G:real^K->real^K^K) (w:real^2->real^K) x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[CMC_TRACE_GRAM] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_MESON_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2; REAL_LE_TRANS];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_UNIV; DIMINDEX_1; FORALL_1; GSYM drop] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> wan_wd (:real^2) i (w:real^2->real^K) IN lspace (:real^2) (&2)`
  ASSUME_TAC THENL [ASM_MESON_TAC[CMC_PMAP_WD]; ALL_TAC] THEN
  REWRITE_TAC[CMC_TRACE_GRAM; LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
  ASM_SIMP_TAC[ARITH; ETA_AX] THEN
  (CONJ_TAC THENL
    [SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o
                   (\x. (G:real^K->real^K^K)((w:real^2->real^K) x)) =
                   ((vectorize o G) o w)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
     MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
     MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
      [UNDISCH_TAC `cmc_pmap S (w:real^2->real^K)` THEN SIMP_TAC[cmc_pmap];
       MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
       ASM_REWRITE_TAC[SUBSET_UNIV]];
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
     ASM_MESON_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2; REAL_LE_TRANS]]));;

let CMC_PEN_POS = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) E.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable E
     ==> &0 <= cmc_pen G E w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_pen] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  MP_TAC(SPEC_ALL CMC_PEN_INTEGRABLE) THEN
  ASM_SIMP_TAC[LIFT_DROP; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let CMC_PEN_MONO = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) E E'.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable E /\ lebesgue_measurable E' /\
     E SUBSET E'
     ==> cmc_pen G E w <= cmc_pen G E' w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_pen] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E':real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let CMC_PEN_UNION = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) E E'.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable E /\ lebesgue_measurable E' /\
     DISJOINT E E'
     ==> cmc_pen G (E UNION E') w = cmc_pen G E w + cmc_pen G E' w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_pen; GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNION THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E':real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{}:real^2->bool` THEN
  REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The trace integrals: integrability, |cmc_ptr| <= M cmc_pen, additivity;   *)
(* the defect density trace - tau_G is nonnegative; cmc_pen is wan_gdir on   *)
(* open sets.                                                                *)
(* ------------------------------------------------------------------------- *)

let CMC_TDEN_MEASURABLE = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (w:real^2->real^K) E.
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z) /\ cmc_pmap S w /\ lebesgue_measurable E
     ==> (\x. lift(cmc_tden G Q w x)) measurable_on E`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
                CMC_JDENS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[CMC_TDEN_3] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2 ==> wan_wd (:real^2) i (w:real^2->real^K) measurable_on E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `i:num`] CMC_PMAP_WD) THEN
    ASM_SIMP_TAC[lspace; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. pastecart ((w:real^2->real^K) x)
           (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))) measurable_on E`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmc_j3] THEN
    REPEAT(MATCH_MP_TAC MEASURABLE_ON_PASTECART THEN CONJ_TAC) THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      UNDISCH_TAC `cmc_pmap S (w:real^2->real^K)` THEN SIMP_TAC[cmc_pmap];
      ASM_SIMP_TAC[ETA_AX; ARITH];
      ASM_SIMP_TAC[ETA_AX; ARITH];
      MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; MEASURABLE_ON_CONST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. pastecart ((w:real^2->real^K) x)
           (cmc_j3 (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))`;
    `\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
       lift(cmw_tdens G Q (fstcart z) (sndcart z))`; `E:real^2->bool`] HMC_MEAS_COMPOSE) THEN
  ASM_REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART]);;

let CMC_PTR_FACTS = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K).
     cm_target S G d /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z)
     ==> ?M. &0 <= M /\
             !(w:real^2->real^K) E.
                cmc_pmap S w /\ lebesgue_measurable E
                ==> (\x. lift(cmc_tden G Q w x)) absolutely_integrable_on E /\
                    abs(cmc_ptr G Q E w) <= M * cmc_pen G E w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
                CMC_TDEN_BOUND) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`w:real^2->real^K`; `E:real^2->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. abs(cmc_tden G Q (w:real^2->real^K) x) <= M * trace(cmc_gram G w x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `cmc_pmap S (w:real^2->real^K)` THEN SIMP_TAC[cmc_pmap];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(cmc_tden G Q (w:real^2->real^K) x)) absolutely_integrable_on E`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x. M % lift(trace(cmc_gram G (w:real^2->real^K) x))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMC_TDEN_MEASURABLE THEN ASM_MESON_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP]];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[cmc_ptr; cmc_pen] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral E (\x. lift(M * trace(cmc_gram G (w:real^2->real^K) x))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_CMUL; INTEGRABLE_CMUL;
                 NORM_LIFT; DROP_CMUL; LIFT_DROP];
    REWRITE_TAC[LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_CMUL;
                 REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Cmc_pen is wan_gdir on open sets; wan_dir with the global partials;       *)
(* additivity of the trace integrals.                                        *)
(* ------------------------------------------------------------------------- *)

let CMC_GQUAD = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
                   ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
                   !z xi. &0 <= xi dot (G z ** xi) /\
                          lam * norm xi pow 2 <= xi dot (G z ** xi) /\
                          xi dot (G z ** xi) <= Lam * norm xi pow 2 /\
                          abs(xi dot (G z ** xi)) <= Lam * norm xi pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPECL [`z:real^K`; `xi:real^K`]) THEN
  SUBGOAL_THEN `&0 <= lam * norm(xi:real^K) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMC_QTERM_INTEGRABLE = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) E i.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable E /\ 1 <= i /\ i <= 2
     ==> (\x. lift(wan_wd (:real^2) i w x dot (G(w x) ** wan_wd (:real^2) i w x)))
         absolutely_integrable_on E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMC_GQUAD) THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  REWRITE_TAC[LIFT_DROP; IN_UNIV; DIMINDEX_1; FORALL_1; GSYM drop] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `i:num`] CMC_PMAP_WD) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\x. (G:real^K->real^K^K)((w:real^2->real^K) x)) =
                  ((vectorize o G) o w)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [UNDISCH_TAC `cmc_pmap S (w:real^2->real^K)` THEN SIMP_TAC[cmc_pmap];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ASM_REWRITE_TAC[]]);;

let CMC_GDIR_PEN = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) s.
     cm_target S G d /\ cmc_pmap S w /\ open s
     ==> wan_gdir s G w = cmc_pen G s w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  REWRITE_TAC[wan_gdir; cmc_pen; DIMINDEX_2; SUM_2; CMC_TRACE_GRAM] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> integral s (\x. lift(wan_wd s i (w:real^2->real^K) x dot
                                 (G(w x) ** wan_wd s i w x))) =
            integral s (\x. lift(wan_wd (:real^2) i w x dot
                                 (G(w x) ** wan_wd (:real^2) i w x)))`
  (fun th -> SIMP_TAC[th; ARITH]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN s /\ ~(wan_wd s i (w:real^2->real^K) x = wan_wd (:real^2) i w x)}` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `s:real^2->bool`; `i:num`]
                    CMC_WD_RESTRICT) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIFT_ADD] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC CMC_QTERM_INTEGRABLE THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; ARITH]);;

