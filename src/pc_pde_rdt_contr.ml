(* ========================================================================= *)
(* pc_pde_rdt_contr: the Ricci-DeTurck existence, part 6.  The step of the   *)
(* frozen-coefficient iteration contracts in sup_t L^2 + int H^1, and        *)
(* PDE_RDT_ITERATION.                                                        *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_iter.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* tr_k Hess_h v for time-dependent k and v is a smooth family, and the      *)
(* difference of two step solutions solves the frozen problem with the       *)
(* coefficients of the first one and the forcing                             *)
(*   (tr_k Hess_h v' - tr_k' Hess_h v') - (f' - f).                          *)
(* ------------------------------------------------------------------------- *)

(* The same statement as PDE_MX_LOP_UPTO of pc_pde_mexist (which this unit  *)
(* does not load); the proof uses lemmas of pc_pde_mtor only.                *)

let RDT_LOP_UPTO = prove
 (`!a b (U:real^N->bool) (A:real->real^N->real^N^N) (B:real->real^N->num->real^K^K) C
    (W:real->real^N->real^K).
     open U /\
     pde_upto a b U (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (A t z)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> pde_upto a b U (\t z. (vectorize:real^K^K->real^(K,K)finite_prod) (B t z i))) /\
     pde_upto a b U (\t z. (vectorize:real^K^K->real^(K,K)finite_prod) (C t z)) /\
     pde_upto a b U W
     ==> pde_upto a b U (\t z. pde_lop A B C W t z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lop] THEN
  SUBGOAL_THEN `!i j. pde_upto a b U (\t z. lift((A:real->real^N->real^N^N) t z$i$j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`;
                   `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((A:real->real^N->real^N^N) t z)`] PDE_MT_UPTO_LINEAR) THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> pde_upto a b U (\t z. partial_derivative i ((W:real->real^N->real^K) t) z) /\
            !j. 1 <= j /\ j <= dimindex(:N)
                ==> pde_upto a b U
                      (\t z. partial_derivative i (partial_derivative j (W t)) z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC PDE_MT_UPTO_PARTIAL_OPEN THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                     `\t z. partial_derivative j ((W:real->real^N->real^K) t) z`; `i:num`]
                    PDE_MT_UPTO_PARTIAL_OPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_MT_UPTO_PARTIAL_OPEN THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[ETA_AX] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THENL
   [MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\t z. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((B:real->real^N->num->real^K^K) t z i)`;
                   `\t z. partial_derivative i ((W:real->real^N->real^K) t) z`]
                  PDE_MT_UPTO_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE; INST_TYPE [`:K`,`:N`] LRG_BILINEAR_MATRIFY_MUL; ETA_AX];
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\t z. (vectorize:real^K^K->real^(K,K)finite_prod) ((C:real->real^N->real^K^K) t z)`;
                   `W:real->real^N->real^K`] PDE_MT_UPTO_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE; INST_TYPE [`:K`,`:N`] LRG_BILINEAR_MATRIFY_MUL; ETA_AX]]);;

let RDT_TRHESS_TFAM = prove
 (`!top atlas a b (k:real->A->real^N^N) h (v:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b v /\ a < b
     ==> pde_tfam_from atlas a b (\t x. pde_trhess atlas (k t) h (v t) x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[PDM_TFAM_FROM_UPTO] o check (fun th ->
    concl th = `pde_tfam_from atlas a b (v:real->A->real^N^N)`)) THEN DISCH_TAC THEN
  REWRITE_TAC[PDM_TFAM_FROM_UPTO; ETA_AX] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  MATCH_MP_TAC PDM_UPTO_CONG THEN
  EXISTS_TAC `\t z. pde_lop (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N))
                            (pde_mlbt atlas c k h) (pde_mlct atlas c k h)
                            (\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                     (metric_local atlas c ((v:real->A->real^N^N) t) z)) t z` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                  PDE_MT_CHART_COEFF_UPTO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC RDT_LOP_UPTO THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[PDE_LOP_LOP0] THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(k:real->A->real^N^N) t`; `h:A->real^N^N`;
                 `(v:real->A->real^N^N) t`; `z:real^N`] PDE_ML_TRHESS_CHART) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t)`;
                 `z:real^N`] PDE_ML_LOP0_FORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[mfd_tensor2_smooth]) THEN ASM_SIMP_TAC[];
      ASM_MESON_TAC[riemannian_metric]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PDE_ML_COEFF_FUN; o_DEF]]);;

let RDT_DIFF_SOL = prove
 (`!top atlas a b (k:real->A->real^N^N) k' h f f' v0 v v'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\ pde_mlin_sol (top,atlas) a b k' h f' v0 v'
     ==> pde_mlin_sol (top,atlas) a b k h
           (\t x. (pde_trhess atlas (k t) h (v' t) x - pde_trhess atlas (k' t) h (v' t) x) -
                  (f' t x - f t x))
           (\x. mat 0) (\t x. v t x - v' t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mlin_sol] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MATRIX_SUB_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t) /\
                mfd_tensor2_smooth atlas ((v':real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(k:real->A->real^N^N) t`; `h:A->real^N^N`; `(v:real->A->real^N^N) t`;
                 `(v':real->A->real^N^N) t`; `x:A`] PDE_ME_TRHESS_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `i:num`; `j:num`] o check (fun th ->
    is_forall(concl th) && rdt_has_const "has_real_derivative" th &&
    can (find_term ((=) `v':real->A->real^N^N`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `i:num`; `j:num`] o check (fun th ->
    is_forall(concl th) && rdt_has_const "has_real_derivative" th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_SUB o CONJ
   (ASSUME `((\s. (v:real->A->real^N^N) s x$i$j) has_real_derivative
             (pde_trhess atlas ((k:real->A->real^N^N) t) h (v t) x + (f:real->A->real^N^N) t x)$i$j)
            (atreal t)`)) THEN
  REWRITE_TAC[MATRIX_SUB_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The energy of one chart at level 0 with a forcing and the                 *)
(* commutator: Young's inequality, the pointwise bound of pde_lop0, the L^2  *)
(* bound of the commutator by H^1 of the localized field.                    *)
(* ------------------------------------------------------------------------- *)

let RDT_LOP0_PT = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) (C:real^N->real^K^K) (u:real^N->real^K) x.
     norm(pde_lop0 A B C u x) <=
     &(dimindex(:N) * dimindex(:N)) * norm(vectorize(A x)) * pde_jetn 2 u x +
     sum(1..dimindex(:N)) (\c. norm(vectorize(B x c))) * pde_jetn 1 u x +
     norm(vectorize(C x)) * pde_jetn 0 u x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_lop0] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:real^K) <= x /\ norm(b:real^K) <= y /\ norm(c:real^K) <= z
    ==> norm(a + b + c) <= x + y + z`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                  (\j. norm(vectorize((A:real^N->real^N^N) x)) *
                       pde_jetn 2 (u:real^N->real^K) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((A:real^N->real^N^N) x$i)` THEN
        REWRITE_TAC[COMPONENT_LE_NORM; PDE_ROW_LE_VECTORIZE];
        MP_TAC(ISPECL [`2`; `u:real^N->real^K`; `[i; j]:num list`; `x:real^N`]
          PDE_ME_TERM_LE_JETN) THEN
        REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL] THEN ASM_ARITH_TAC];
      SIMP_TAC[SUM_CONST_NUMSEG; ADD_SUB; GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\c. norm(vectorize((B:real^N->num->real^K^K) x c)) *
                                          pde_jetn 1 (u:real^N->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize((B:real^N->num->real^K^K) x c)) *
                  norm(partial_derivative c (u:real^N->real^K) x)` THEN
      REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC(ISPECL [`1`; `u:real^N->real^K`; `[c]:num list`; `x:real^N`]
        PDE_ME_TERM_LE_JETN) THEN
      REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_RMUL; REAL_LE_REFL]];
    REWRITE_TAC[RDT_JETN_0; COMPATIBLE_NORM_VECTORIZE]]);;

let RDT_YOUNG = prove
 (`!e (a:real^N) b. &0 < e ==> abs(&2 * (a dot b)) <= inv e * norm a pow 2 + e * norm b pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * norm(a:real^N) * norm(b:real^N)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
  MP_TAC(SPEC `norm(a:real^N) - e * norm(b:real^N)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let RDT_HS_0 = prove
 (`!U (u:real^N->real^Q). rdt_hs U 0 u = rdt_int U (\y. norm(u y) pow 2)`,
  REWRITE_TAC[rdt_hs; PDE_INDEX_LISTS_0; SUM_SING; iterated_partial]);;

(* Smoothness and support of the commutator, and its L^2 bound by H^1.      *)

let RDT_COMM_FACTS = prove
 (`!U K (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) p (W:real^N->real^Q).
     open U /\ compact K /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U p /\
     smooth_map_on U W /\ (!y. y IN U /\ ~(y IN K) ==> p y = vec 0)
     ==> smooth_map_on U (pde_mt_comm A B p W) /\
         (!y. y IN U /\ ~(y IN K) ==> pde_mt_comm A B p W y = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[RDT_COMM_LOP0_FUN] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                   `p:real^N->real^1`] RDT_COMM_COEFF_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC RDT_LOP0_SMOOTH THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN
    EXISTS_TAC `U DIFF (K:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF]]);;

let RDT_COMM_HS0 = prove
 (`!(K:real^N->bool) KW M Ap.
     compact K /\ compact KW /\ &0 <= M /\ &0 <= Ap
     ==> ?C. &0 <= C /\
             !U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) p W.
               open U /\ K SUBSET U /\ KW SUBSET U /\
               smooth_map_on U (\x. vectorize(A x)) /\
               (!i. smooth_map_on U (\x. vectorize(B x i))) /\
               smooth_map_on U (\x. vectorize(C0 x)) /\
               smooth_map_on U p /\ smooth_map_on U W /\
               (!y. y IN U /\ ~(y IN K) ==> p y = vec 0) /\
               (!y. y IN U /\ ~(y IN KW) ==> W y = vec 0) /\
               (!y. y IN K ==> pde_jetn 2 p y <= Ap) /\
               (!y. y IN K ==> rdt_cjet 0 A B C0 y <= M)
               ==> rdt_hs U 0 (pde_mt_comm A B p W) <= C * rdt_hs U 1 W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Kc = (&(CARD(pde_index_lists 0 (:N))) * &2 pow 0 * &(0 + 1)) *
                   (&3 * &(dimindex(:N)) pow 2 * norm(vectorize(mat 1:real^Q^Q)) + &1)` THEN
  SUBGOAL_THEN `&0 <= Kc` ASSUME_TAC THENL [EXPAND_TAC "Kc" THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists 0 (:N))) *
              (&2 * (Kc * Ap * M) pow 2 * (&1 pow 2 * &(CARD(pde_index_lists 1 (:N)))))` THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `A:real^N->real^N^N`;
                 `B:real^N->num->real^Q^Q`; `p:real^N->real^1`; `W:real^N->real^Q`]
    RDT_COMM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `KW:real^N->bool`;
                 `pde_mt_comm (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) p
                              (W:real^N->real^Q)`; `W:real^N->real^Q`; `\y:real^N. &0`;
                 `0`; `1`; `Kc * Ap * M`; `&1`; `&0`; `&0`] RDT_HS_FROM_POINTWISE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; REAL_POS; LIFT_NUM; REAL_POW_ZERO; ARITH_EQ;
                    INTEGRAL_0; DROP_VEC; REAL_LE_REFL] THEN
    CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
    REWRITE_TAC[PDE_INDEX_LISTS_0; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[iterated_partial; REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID] THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`0`; `U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                   `C0:real^N->real^Q^Q`; `p:real^N->real^1`; `y:real^N`; `Ap:real`]
      RDT_COMM_CJET) THEN
    ASM_SIMP_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    REWRITE_TAC[RDT_COMM_LOP0] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rdt_cjet 0 (\z:real^N. mat 0:real^N^N)
                  (rdt_cdd (A:real^N->real^N^N) (p:real^N->real^1):real^N->num->real^Q^Q)
                  (rdt_cee A (B:real^N->num->real^Q^Q) p) y *
                pde_jetn 1 (W:real^N->real^Q) y` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z:real^N. mat 0:real^N^N`;
                     `rdt_cdd (A:real^N->real^N^N) (p:real^N->real^1):real^N->num->real^Q^Q`;
                     `rdt_cee (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) p`;
                     `W:real^N->real^Q`; `y:real^N`] RDT_LOP0_PT) THEN
      REWRITE_TAC[VECTORIZE_0; NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      REWRITE_TAC[rdt_cjet; RDT_JETN_0; VECTORIZE_0; NORM_0; REAL_ADD_LID] THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
      REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC(ISPECL [`0`; `1`; `W:real^N->real^Q`; `y:real^N`] PDE_JETN_MONO) THEN
      REWRITE_TAC[RDT_JETN_0; ARITH_RULE `0 <= 1`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[PDE_JETN_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Kc * Ap * rdt_cjet 0 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                     (C0:real^N->real^Q^Q) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The level-0 energy of one chart with a forcing and the commutator term,   *)
(* by RDT_CHART_ENERGY0, Young's inequality and the level-0 commutator       *)
(* bound.                                                                    *)
(* ------------------------------------------------------------------------- *)

let RDT_CHART_ENERGY0_F = prove
 (`!(K:real^N->bool) KW lam M Ap.
     compact K /\ compact KW /\ &0 < lam /\ &0 <= M /\ &0 <= Ap
     ==> ?CE CM. &0 <= CE /\ &0 <= CM /\
           !U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
            u pF p W e1 e2.
             open U /\ K SUBSET U /\ KW SUBSET U /\
             smooth_map_on U (\x. vectorize(A x)) /\
             (!i. smooth_map_on U (\x. vectorize(B x i))) /\
             smooth_map_on U (\x. vectorize(C0 x)) /\
             smooth_map_on U u /\ smooth_map_on U pF /\ smooth_map_on U p /\
             smooth_map_on U W /\
             (!y. y IN U /\ ~(y IN K) ==> u y = vec 0 /\ pF y = vec 0 /\ p y = vec 0) /\
             (!y. y IN U /\ ~(y IN KW) ==> W y = vec 0) /\
             (!y w. y IN K ==> lam * norm w pow 2 <= w dot (A y ** w)) /\
             (!y. y IN K ==> rdt_cjet 1 A B C0 y <= M) /\
             (!y. y IN K ==> pde_jetn 2 p y <= Ap) /\ &0 < e1 /\ &0 < e2
             ==> rdt_int U (\y. &2 * (u y dot (pde_lop0 A B C0 u y +
                                               (pF y - pde_mt_comm A B p W y))))
                 <= --(lam / &2) * rdt_hs U 1 u + (CE + inv e1 + inv e2) * rdt_hs U 0 u +
                    e1 * rdt_hs U 0 pF + e2 * CM * rdt_hs U 1 W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `lam:real`; `M:real`] RDT_CHART_ENERGY0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CE:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ce"))) THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `KW:real^N->bool`; `M:real`; `Ap:real`] RDT_COMM_HS0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CM:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cm"))) THEN
  MAP_EVERY EXISTS_TAC [`CE:real`; `CM:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!y. y IN U /\ ~(y IN K) ==> (u:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (pF:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (p:real^N->real^1) y = vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `A:real^N->real^N^N`;
                 `B:real^N->num->real^Q^Q`; `p:real^N->real^1`; `W:real^N->real^Q`]
    RDT_COMM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                          (C0:real^N->real^Q^Q) (u:real^N->real^Q))`
  ASSUME_TAC THENL [MATCH_MP_TAC RDT_LOP0_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_cs U K (\y. &2 * ((u:real^N->real^Q) y dot
                          pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                   (C0:real^N->real^Q^Q) u y)) /\
    rdt_cs U K (\y. &2 * (u y dot (pF:real^N->real^Q) y) -
                    &2 * (u y dot pde_mt_comm A B (p:real^N->real^1) (W:real^N->real^Q) y)) /\
    rdt_cs U K (\y. norm(u y) pow 2) /\ rdt_cs U K (\y. norm(pF y) pow 2) /\
    rdt_cs U K (\y. norm(pde_mt_comm A B p W y) pow 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CS_CMUL THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC RDT_CS_SUB THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_CMUL THEN
      MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[ETA_AX];
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `[]:num list`]
        RDT_CS_SQNORM) THEN ASM_REWRITE_TAC[iterated_partial];
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `pF:real^N->real^Q`; `[]:num list`]
        RDT_CS_SQNORM) THEN ASM_REWRITE_TAC[iterated_partial];
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                     `pde_mt_comm (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                  (p:real^N->real^1) (W:real^N->real^Q)`; `[]:num list`]
        RDT_CS_SQNORM) THEN ASM_REWRITE_TAC[iterated_partial]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. &2 * ((u:real^N->real^Q) y dot
               (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
                         u y + ((pF:real^N->real^Q) y -
                                pde_mt_comm A B (p:real^N->real^1) (W:real^N->real^Q) y)))) =
    (\y. &2 * (u y dot pde_lop0 A B C0 u y) +
         (&2 * (u y dot pF y) - &2 * (u y dot pde_mt_comm A B p W y)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DOT_RADD; DOT_RSUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\y. &2 * ((u:real^N->real^Q) y dot
                            pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                     (C0:real^N->real^Q^Q) u y)`;
                 `\y. &2 * ((u:real^N->real^Q) y dot (pF:real^N->real^Q) y) -
                      &2 * (u y dot pde_mt_comm (A:real^N->real^N^N)
                                       (B:real^N->num->real^Q^Q) (p:real^N->real^1)
                                       (W:real^N->real^Q) y)`] RDT_INT_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `rdt_int U (\y. &2 * ((u:real^N->real^Q) y dot (pF:real^N->real^Q) y) -
                   &2 * (u y dot pde_mt_comm (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                   (p:real^N->real^1) (W:real^N->real^Q) y))
    <= (inv e1 + inv e2) * rdt_hs U 0 u + e1 * rdt_hs U 0 pF +
       e2 * rdt_hs U 0 (pde_mt_comm A B p W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rdt_int U (\y. (inv e1 + inv e2) * norm((u:real^N->real^Q) y) pow 2 +
                               (e1 * norm((pF:real^N->real^Q) y) pow 2 +
                                e2 * norm(pde_mt_comm (A:real^N->real^N^N)
                                            (B:real^N->num->real^Q^Q) (p:real^N->real^1)
                                            (W:real^N->real^Q) y) pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_INT_LE THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RDT_CS_ADD THEN ASM_SIMP_TAC[RDT_CS_CMUL; RDT_CS_ADD]; ALL_TAC] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`e1:real`; `(u:real^N->real^Q) y`; `(pF:real^N->real^Q) y`] RDT_YOUNG) THEN
      MP_TAC(ISPECL [`e2:real`; `(u:real^N->real^Q) y`;
                     `pde_mt_comm (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                  (p:real^N->real^1) (W:real^N->real^Q) y`] RDT_YOUNG) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. (inv e1 + inv e2) * norm((u:real^N->real^Q) y) pow 2`;
                   `\y. e1 * norm((pF:real^N->real^Q) y) pow 2 +
                        e2 * norm(pde_mt_comm (A:real^N->real^N^N)
                                    (B:real^N->num->real^Q^Q) (p:real^N->real^1)
                                    (W:real^N->real^Q) y) pow 2`] RDT_INT_ADD) THEN
    ASM_SIMP_TAC[RDT_CS_CMUL; RDT_CS_ADD] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. e1 * norm((pF:real^N->real^Q) y) pow 2`;
                   `\y. e2 * norm(pde_mt_comm (A:real^N->real^N^N)
                                    (B:real^N->num->real^Q^Q) (p:real^N->real^1)
                                    (W:real^N->real^Q) y) pow 2`] RDT_INT_ADD) THEN
    ASM_SIMP_TAC[RDT_CS_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RDT_HS_0] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THENL
     [MATCH_MP_TAC RDT_INT_CMUL THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BINOP_TAC THEN MATCH_MP_TAC RDT_INT_CMUL THEN EXISTS_TAC `K:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ce" (MP_TAC o SPECL [`U:real^N->bool`; `A:real^N->real^N^N`;
    `B:real^N->num->real^Q^Q`; `C0:real^N->real^Q^Q`; `u:real^N->real^Q`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "cm" (MP_TAC o SPECL [`U:real^N->bool`; `A:real^N->real^N^N`;
    `B:real^N->num->real^Q^Q`; `C0:real^N->real^Q^Q`; `p:real^N->real^1`;
    `W:real^N->real^Q`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rdt_cjet 1 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                         (C0:real^N->real^Q^Q) y` THEN
    ASM_SIMP_TAC[RDT_CJET_MONO; LE_0];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= inv e2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `e2 * rdt_hs U 0 (pde_mt_comm (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                   (p:real^N->real^1) (W:real^N->real^Q)) <=
                e2 * CM * rdt_hs U 1 W` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The level-0 energy of one chart for a solution of the frozen              *)
(* problem (setup as in RDT_MCHART of pc_pde_rdt_energy).                    *)
(* ------------------------------------------------------------------------- *)

let RDT_MCHART0 = prove
 (`!(K:real^N->bool) KT lam M Ap.
     compact K /\ compact KT /\ &0 < lam /\ &0 <= M /\ &0 <= Ap
     ==> ?CE CM. &0 <= CE /\ &0 <= CM /\
             !top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) (theta:A->real) O a b
              (k:real->A->real^N^N) h f v0 v t e1 e2.
               smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
               (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
               pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b f /\
               pde_mlin_sol (top,atlas) a b k h f v0 v /\ a < t /\ t < b /\
               mfd_smooth atlas (\x. lift(phi x)) /\ K SUBSET IMAGE (SND c) (FST c) /\
               (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) K) /\
               mfd_smooth atlas (\x. lift(theta x)) /\ KT SUBSET IMAGE (SND c) (FST c) /\
               (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv c) KT) /\
               open O /\ K SUBSET O /\ O SUBSET IMAGE (SND c) (FST c) /\
               (!z. z IN O ==> theta(chart_inv c z) = &1) /\
               (!y. y IN K ==> pde_jetn 2 (\z. lift(phi(chart_inv c z))) y <= Ap) /\
               (!y w. y IN K ==> lam * norm w pow 2 <= w dot (pde_mlaa atlas c k t y ** w)) /\
               (!y. y IN K ==> rdt_cjet 1 (pde_mlaa atlas c k t)
                                        (pde_mlbt atlas c k h t) (pde_mlct atlas c k h t) y
                               <= M) /\
               &0 < e1 /\ &0 < e2
               ==> sum (pde_index_lists 0 (:N))
                     (\l. drop(integral (IMAGE (SND c) (FST c))
                       (\z. lift(&2 *
                          (iterated_partial l
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (phi(chart_inv c z) %% metric_local atlas c (v t) z)) z dot
                           iterated_partial l
                             (\z. partial_derivative 1
                                    (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                           (phi(chart_inv c (sndcart w)) %%
                                            metric_local atlas c (v(drop(fstcart w))) (sndcart w)))
                                    (pastecart (lift t) z)) z)))))
                   <= --(lam / &2) *
                      rdt_hs (IMAGE (SND c) (FST c)) 1
                        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                               (phi(chart_inv c z) %% metric_local atlas c (v t) z)) +
                      (CE + inv e1 + inv e2) *
                      rdt_hs (IMAGE (SND c) (FST c)) 0
                        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                               (phi(chart_inv c z) %% metric_local atlas c (v t) z)) +
                      e1 * rdt_hs (IMAGE (SND c) (FST c)) 0
                        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                               (phi(chart_inv c z) %% metric_local atlas c (f t) z)) +
                      e2 * CM * rdt_hs (IMAGE (SND c) (FST c)) 1
                        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                               (theta(chart_inv c z) %% metric_local atlas c (v t) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `KT:real^N->bool`; `lam:real`; `M:real`; `Ap:real`]
    (INST_TYPE [`:(N,N)finite_prod`,`:Q`] RDT_CHART_ENERGY0_F)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CE:real` (X_CHOOSE_THEN `CM:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ce"))))) THEN
  MAP_EVERY EXISTS_TAC [`CE:real`; `CM:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) /\ a < b /\ a <= t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `K:real^N->bool`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `theta:A->real`; `KT:real^N->bool`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t) /\
                mfd_tensor2_smooth atlas ((f:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_MESON_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND c) (FST c))
      (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t) y)) /\
    smooth_map_on (IMAGE (SND c) (FST c))
      (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas (c:(A->bool)#(A->real^N)) ((f:real->A->real^N^N) t) y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t)`;
      UNDISCH_TAC `mfd_tensor2_smooth atlas ((f:real->A->real^N^N) t)`] THEN
    REWRITE_TAC[mfd_tensor2_smooth; o_DEF] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `c:(A->bool)#(A->real^N)`]
    PDE_MT_CHART_COEFF_UPTO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND c) (FST c))
      (\x. (vectorize:real^N^N->real^(N,N)finite_prod)
             (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t x)) /\
    (!i. smooth_map_on (IMAGE (SND c) (FST c))
           (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlbt atlas c k (h:A->real^N^N) t x i))) /\
    smooth_map_on (IMAGE (SND c) (FST c))
      (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                      ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
             (pde_mlct atlas c k h t x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                     `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                        (k:real->A->real^N^N) t z)`;
                     `t:real`] PDE_ML_UPTO_SLICE_OPEN);
      GEN_TAC THEN
      MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                     `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                       ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                              (pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)
                                        (h:A->real^N^N) t z i)`;
                     `t:real`] PDE_ML_UPTO_SLICE_OPEN);
      MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                     `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                       ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                              (pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)
                                        (h:A->real^N^N) t z)`;
                     `t:real`] PDE_ML_UPTO_SLICE_OPEN)] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the cut-off pieces *)
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN
   `!(g:real->A->real^N^N) (cut:A->real) KC.
      smooth_map_on U (\z. lift(cut(chart_inv (c:(A->bool)#(A->real^N)) z))) /\
      (!z. z IN U /\ ~(z IN KC) ==> lift(cut(chart_inv c z)) = vec 0) /\
      smooth_map_on U (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas c (g t) y))
      ==> smooth_map_on U (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 (cut(chart_inv c z) %% metric_local atlas c (g t) z)) /\
          (!z. z IN U /\ ~(z IN KC)
               ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                     (cut(chart_inv c z) %% metric_local atlas c (g t) z) = vec 0)`
  (LABEL_TAC "piece") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[VECTORIZE_CMUL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`;
                     `\z. lift((cut:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))`;
                     `\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (c:(A->bool)#(A->real^N))
                               ((g:real->A->real^N^N) t) y)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[LIFT_DROP];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\ K SUBSET U /\ KT SUBSET U /\ O SUBSET U`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\z. lift((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))) /\
    (!z. z IN U /\ ~(z IN K) ==> lift(phi(chart_inv c z)) = vec 0) /\
    smooth_map_on U (\z. lift((theta:A->real)(chart_inv c z))) /\
    (!z. z IN U /\ ~(z IN KT) ==> lift(theta(chart_inv c z)) = vec 0) /\
    smooth_map_on U (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas c ((v:real->A->real^N^N) t) y)) /\
    smooth_map_on U (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas c ((f:real->A->real^N^N) t) y)) /\
    smooth_map_on U (\x. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (pde_mlaa atlas c (k:real->A->real^N^N) t x)) /\
    (!i. smooth_map_on U
           (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlbt atlas c k (h:A->real^N^N) t x i))) /\
    smooth_map_on U
      (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                      ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
             (pde_mlct atlas c k h t x))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "piece" (MP_TAC o SPECL [`v:real->A->real^N^N`; `phi:A->real`; `K:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "piece" (MP_TAC o SPECL [`f:real->A->real^N^N`; `phi:A->real`; `K:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "piece" (MP_TAC o SPECL [`v:real->A->real^N^N`; `theta:A->real`; `KT:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REMOVE_THEN "piece" (K ALL_TAC) THEN
  (* the cut-off pieces and the forcing of the cut-off equation *)
  ABBREV_TAC `p = \z. lift((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))` THEN
  ABBREV_TAC `W = \z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((theta:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                         metric_local atlas c ((v:real->A->real^N^N) t) z)` THEN
  ABBREV_TAC `u = \z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                         metric_local atlas c ((v:real->A->real^N^N) t) z)` THEN
  ABBREV_TAC `pF = \z. (vectorize:real^N^N->real^(N,N)finite_prod)
                         ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                          metric_local atlas c ((f:real->A->real^N^N) t) z)` THEN
  SUBGOAL_THEN
   `smooth_map_on U (u:real^N->real^(N,N)finite_prod) /\
    (!z. z IN U /\ ~(z IN K) ==> u z = vec 0) /\
    smooth_map_on U (pF:real^N->real^(N,N)finite_prod) /\
    (!z. z IN U /\ ~(z IN K) ==> pF z = vec 0) /\
    smooth_map_on U (W:real^N->real^(N,N)finite_prod) /\
    (!z. z IN U /\ ~(z IN KT) ==> W z = vec 0) /\
    smooth_map_on U (p:real^N->real^1) /\ (!z. z IN U /\ ~(z IN K) ==> p z = vec 0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "pF"; "W"; "p"] THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U
      (pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
                   (pde_mlbt atlas c k (h:A->real^N^N) t)
                   (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod)) /\
    (!z. z IN U /\ ~(z IN K)
         ==> pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t) p W z = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[RDT_COMM_LOP0_FUN] THEN
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t`;
                     `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)
                               (h:A->real^N^N) t`; `p:real^N->real^1`]
        RDT_COMM_COEFF_SMOOTH) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC RDT_LOP0_SMOOTH THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN
      EXISTS_TAC `U DIFF (K:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF]];
    ALL_TAC] THEN
  (* the time derivative on the chart in pde_lop0 form *)
  SUBGOAL_THEN
   `!z. z IN U
        ==> partial_derivative 1
              (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)) %%
                      metric_local atlas c ((v:real->A->real^N^N) (drop(fstcart w)))
                        (sndcart w)))
              (pastecart (lift t) z) =
            pde_lop0 (pde_mlaa atlas c (k:real->A->real^N^N) t)
                     (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t)
                     (u:real^N->real^(N,N)finite_prod) z +
            ((pF:real^N->real^(N,N)finite_prod) z -
             pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t)
                         (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                   `v0:A->real^N^N`; `v:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                   `phi:A->real`; `theta:A->real`; `K:real^N->bool`; `O:real^N->bool`;
                   `t:real`; `z:real^N`] RDT_CHART_TD_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXPAND_TAC ["u"; "pF"; "p"; "W"] THEN
    REWRITE_TAC[VECTORIZE_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (pde_index_lists 0 (:N))
      (\l. drop(integral U
         (\z. lift(&2 *
            (iterated_partial l (u:real^N->real^(N,N)finite_prod) z dot
             iterated_partial l
               (\z. partial_derivative 1
                      (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                             ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)) %%
                              metric_local atlas c ((v:real->A->real^N^N) (drop(fstcart w)))
                                (sndcart w)))
                      (pastecart (lift t) z)) z))))) =
    sum (pde_index_lists 0 (:N))
      (\l. rdt_int U
         (\z. &2 *
            (iterated_partial l u z dot
             iterated_partial l
               (\y. pde_lop0 (pde_mlaa atlas c (k:real->A->real^N^N) t)
                             (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t)
                             u y +
                    ((pF:real^N->real^(N,N)finite_prod) y -
                     pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t)
                                 (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) y)) z)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    REWRITE_TAC[rdt_int] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the chart energy at level 0 *)
  REWRITE_TAC[PDE_INDEX_LISTS_0; SUM_SING; iterated_partial; ETA_AX] THEN
  USE_THEN "ce" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "p" THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The level-0 energy on the manifold with dissipation:                      *)
(*   d/dt |v|_0^2 <= -(lam/4) |v|_1^2 + C |v|_0^2 + e |f|_0^2                 *)
(* for solutions of the frozen problem, C depending on e, lam, M and the     *)
(* cover data (RDT_MCHART0 per chart, the commutator absorbed by the         *)
(* dissipation).                                                             *)
(* ------------------------------------------------------------------------- *)

let RDT_MENERGY_0 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi lam M e.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     &0 < lam /\ &0 <= M /\ &0 < e
     ==> ?C. &0 <= C /\
             !a b k h f v0 v t.
               riemannian_metric atlas h /\
               (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
               pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b f /\
               pde_mlin_sol (top,atlas) a b k h f v0 v /\ a < t /\ t < b /\
               (!i y w. i < n0 /\ y IN ks i
                        ==> lam * norm w pow 2 <= w dot (pde_mlaa atlas (cs i) k t y ** w)) /\
               (!i y. i < n0 /\ y IN ks i
                      ==> rdt_cjet 1 (pde_mlaa atlas (cs i) k t)
                                   (pde_mlbt atlas (cs i) k h t) (pde_mlct atlas (cs i) k h t) y
                          <= M)
               ==> ?D. ((\r. pde_mnorm2 atlas n0 cs psi 0 (v r)) has_real_derivative D)
                       (atreal t) /\
                       D <= --(lam / &4) * pde_mnorm2 atlas n0 cs psi 1 (v t) +
                            C * pde_mnorm2 atlas n0 cs psi 0 (v t) +
                            e * pde_mnorm2 atlas n0 cs psi 0 (f t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `1`; `2`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
    (GEN `i:num` (ISPECL [`(ks:num->real^N->bool) i`; `(KT:num->real^N->bool) i`;
                          `lam:real`; `M:real`; `(AP:num->real) i`] RDT_MCHART0))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CE:num->real` (X_CHOOSE_THEN `CM:num->real` (LABEL_TAC "cc"))) THEN
  SUBGOAL_THEN `!i. i < n0 ==> &0 <= (CE:num->real) i /\ &0 <= (CM:num->real) i /\
                               &0 <= (DD:num->real) i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "cc" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `CES = sum {i | i < n0} (CE:num->real)` THEN
  ABBREV_TAC `CMS = sum {i | i < n0} (CM:num->real)` THEN
  ABBREV_TAC `DS = sum {i | i < n0} (DD:num->real)` THEN
  SUBGOAL_THEN `&0 <= CES /\ &0 <= CMS /\ &0 <= DS` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["CES"; "CMS"; "DS"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n0 ==> (CE:num->real) i <= CES /\ (CM:num->real) i <= CMS`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["CES"; "CMS"] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`CE:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM);
      MP_TAC(ISPECL [`CM:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e2 = lam * inv(&4 * (CMS * DS + &1))` THEN
  SUBGOAL_THEN `&0 < e2 /\ e2 * (CMS * DS) <= lam / &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * (CMS * DS + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "e2" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div; REAL_ARITH `(lam / x) * y = (lam * y) / x`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= lam * CMS * DS` MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `CES + inv e + inv e2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N) /\
                pde_tensor_smooth atlas ((v:real->A->real^N^N) t) /\
                pde_tensor_smooth atlas ((f:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N)` ASSUME_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_mlin_sol]); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `v:real->A->real^N^N`; `a:real`; `b:real`; `0`] PDM_MNORM2_TFAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN REWRITE_TAC[th]) THEN
  ABBREV_TAC `E1 = pde_mnorm2 atlas n0 cs psi 1 ((v:real->A->real^N^N) t)` THEN
  SUBGOAL_THEN `&0 <= E1` ASSUME_TAC THENL
   [EXPAND_TAC "E1" THEN MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {i | i < n0}
      (\i. --(lam / &2) *
           rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) 1
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) +
           (CES + inv e + inv e2) *
           rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) 0
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (psi i (chart_inv (cs i) z) %% metric_local atlas (cs i) (v t) z)) +
           e * rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) 0
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (psi i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) ((f:real->A->real^N^N) t) z)) +
           e2 * CMS * (DD:num->real) i * E1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cc" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`; `(TH:num->A->real) i`;
      `(OO:num->real^N->bool) i`; `a:real`; `b:real`; `k:real->A->real^N^N`;
      `h:A->real^N^N`; `f:real->A->real^N^N`; `v0:A->real^N^N`; `v:real->A->real^N^N`;
      `t:real`; `e:real`; `e2:real`] o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(v:real->A->real^N^N) t` o check (fun th ->
      rdt_has_const "pde_tensor_smooth" th && is_forall (concl th) &&
      rdt_has_const "rdt_hs" th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) 0
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((psi:num->A->real) i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) /\
      &0 <= rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) 1
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((TH:num->A->real) i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) (v t) z))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[rdt_hs; rdt_int] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                       `(ks:num->real^N->bool) i`] PDE_ME_CNORM_POS) THEN
        ASM_REWRITE_TAC[pde_me_cnorm; rdt_hs; rdt_int] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[rdt_hs; rdt_int] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `(cs:num->(A->bool)#(A->real^N)) i`; `(TH:num->A->real) i`;
                       `(KT:num->real^N->bool) i`] PDE_ME_CNORM_POS) THEN
        ASM_REWRITE_TAC[pde_me_cnorm; rdt_hs; rdt_int] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(CE:num->real) i <= CES /\ (CM:num->real) i <= CMS /\
                  &0 <= CE i /\ &0 <= CM i /\ &0 <= (DD:num->real) i`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `H0 = rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) 0
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((psi:num->A->real) i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) ((v:real->A->real^N^N) t) z))` THEN
    ABBREV_TAC `HW = rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) 1
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((TH:num->A->real) i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) ((v:real->A->real^N^N) t) z))` THEN
    SUBGOAL_THEN `(CE i + inv e + inv e2) * H0 <= (CES + inv e + inv e2) * H0 /\
                  e2 * (CM:num->real) i * HW <= e2 * CMS * (DD:num->real) i * E1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CMS * HW` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mnorm2 atlas n0 cs psi 1 ((v:real->A->real^N^N) t) =
    sum {i | i < n0}
      (\i. rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) 1
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) (v t) z))) /\
    pde_mnorm2 atlas n0 cs psi 0 ((v:real->A->real^N^N) t) =
    sum {i | i < n0}
      (\i. rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) 0
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) (v t) z))) /\
    pde_mnorm2 atlas n0 cs psi 0 ((f:real->A->real^N^N) t) =
    sum {i | i < n0}
      (\i. rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) 0
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) (f t) z)))`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [REWRITE_TAC[RDT_MNORM2_HS]; ALL_TAC] THEN
  SIMP_TAC[SUM_LMUL; SUM_ADD; FINITE_NUMSEG_LT] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SUM_RMUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e2 * CMS * DS * E1 <= (lam / &4) * E1` MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lipschitz bounds of the fixed outer maps on the compact                   *)
(* convex sets rdt_sk, and the pointwise bound of the forcing of the         *)
(* difference of two steps in one chart:                                     *)
(*   |L(G) V' - L(G') V' - (P(G') - P(G))| <= L (1 + |V'|_2) |G - G'|_1.     *)
(* ------------------------------------------------------------------------- *)

let RDT_SK_CONVEX = prove
 (`!K1 R. convex(rdt_sk K1 R:real^((N,N)finite_prod,Q)finite_sum->bool)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[convex; rdt_sk; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^((N,N)finite_prod,Q)finite_sum`;
                       `y:real^((N,N)finite_prod,Q)finite_sum`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN REWRITE_TAC[FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD; SNDCART_CMUL] THEN
  SUBGOAL_THEN `!X. u * X + v * X = X` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `!a b p q r. norm(a:real^(N,N)finite_prod) <= p /\
                                         norm(b:real^(N,N)finite_prod) <= q /\
                                         p + q <= r ==> norm(a + b) <= r`) THEN
    EXISTS_TAC `u * K1` THEN EXISTS_TAC `v * K1` THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 <= u ==> abs u = u`; REAL_LE_REFL] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^N` THEN
    REWRITE_TAC[MATRIFY_ADD; MATRIFY_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
                DOT_RADD; DOT_RMUL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      is_forall(concl th) && rdt_has_const "matrify" th &&
      can (find_term ((=) `fstcart(x:real^((N,N)finite_prod,Q)finite_sum)`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      is_forall(concl th) && rdt_has_const "matrify" th &&
      can (find_term ((=) `fstcart(y:real^((N,N)finite_prod,Q)finite_sum)`)) (concl th))) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `u * norm(w:real^N) pow 2 <=
      u * (K1 * (w dot ((matrify(fstcart(x:real^((N,N)finite_prod,Q)finite_sum)):real^N^N) ** w))) /\
      v * norm(w:real^N) pow 2 <=
      v * (K1 * (w dot ((matrify(fstcart(y:real^((N,N)finite_prod,Q)finite_sum)):real^N^N) ** w)))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `norm(w:real^N) pow 2` o check (is_forall o concl)) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(NORM_ARITH `!a b p q r. norm(a:real^Q) <= p /\ norm(b:real^Q) <= q /\
                                         p + q <= r ==> norm(a + b) <= r`) THEN
    EXISTS_TAC `u * R` THEN EXISTS_TAC `v * R` THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 <= u ==> abs u = u`; REAL_LE_REFL] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let RDT_SK_LIPSCHITZ = prove
 (`!(Phi:real^((N,N)finite_prod,Q)finite_sum->real^P) K1 R.
     smooth_map_on {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} Phi
     ==> ?L. &0 <= L /\
             !x y. x IN rdt_sk K1 R /\ y IN rdt_sk K1 R
                   ==> norm(Phi x - Phi y) <= L * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {x:real^((N,N)finite_prod,Q)finite_sum |
                   ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}` THEN
  SUBGOAL_THEN `open (S:real^((N,N)finite_prod,Q)finite_sum->bool) /\
                rdt_sk K1 R SUBSET (S:real^((N,N)finite_prod,Q)finite_sum->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[RDT_SK_SUBSET] THEN MATCH_MP_TAC RDT_OPEN_INV THEN
    REWRITE_TAC[LINEAR_FSTCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^((N,N)finite_prod,Q)finite_sum->bool`;
                 `rdt_sk K1 R:real^((N,N)finite_prod,Q)finite_sum->bool`;
                 `Phi:real^((N,N)finite_prod,Q)finite_sum->real^P`; `1`]
    RDT_JETS_BOUNDED_COMPACT) THEN
  ASM_REWRITE_TAC[RDT_SK_COMPACT] THEN
  DISCH_THEN(X_CHOOSE_THEN `MP:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&(dimindex(:((N,N)finite_prod,Q)finite_sum)) * MP` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
  EXISTS_TAC `\x. frechet_derivative (Phi:real^((N,N)finite_prod,Q)finite_sum->real^P) (at x)` THEN
  REWRITE_TAC[RDT_SK_CONVEX] THEN
  SUBGOAL_THEN `!x. x IN rdt_sk K1 R
                    ==> (Phi:real^((N,N)finite_prod,Q)finite_sum->real^P) differentiable (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^((N,N)finite_prod,Q)finite_sum->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^((N,N)finite_prod,Q)finite_sum` THEN DISCH_TAC THEN
  REWRITE_TAC[] THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Phi:real^((N,N)finite_prod,Q)finite_sum->real^P)
                                          (at x))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o MATCH_MP ONORM) THEN
  X_GEN_TAC `hh:real^((N,N)finite_prod,Q)finite_sum` THEN
  ASM_SIMP_TAC[PDM_FRECHET_PARTIALS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:((N,N)finite_prod,Q)finite_sum))
                (\k. norm(hh:real^((N,N)finite_prod,Q)finite_sum) * MP)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE; COMPONENT_LE_NORM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn 1 (Phi:real^((N,N)finite_prod,Q)finite_sum->real^P) x` THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`1`; `Phi:real^((N,N)finite_prod,Q)finite_sum->real^P`; `[k]:num list`;
                   `x:real^((N,N)finite_prod,Q)finite_sum`] PDE_ME_TERM_LE_JETN) THEN
    REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL] THEN ASM_ARITH_TAC;
    SIMP_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

(* Coefficient differences of pde_lop0 and the difference of rdt_dgv.        *)

let RDT_LOP0_SUB_COEF = prove
 (`!(A1:real^N->real^N^N) A2 (B1:real^N->num->real^K^K) B2 (C1:real^N->real^K^K) C2 u x.
     pde_lop0 A1 B1 C1 u x - pde_lop0 A2 B2 C2 u x =
     pde_lop0 (\y. A1 y - A2 y) (\y c. B1 y c - B2 y c) (\y. C1 y - C2 y) u x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_lop0] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
       (\j. ((A1:real^N->real^N^N) x - A2 x)$i$j %
            partial_derivative i (partial_derivative j (u:real^N->real^K)) x)) =
    vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
       (\j. A1 x$i$j % partial_derivative i (partial_derivative j u) x)) -
    vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
       (\j. (A2:real^N->real^N^N) x$i$j % partial_derivative i (partial_derivative j u) x))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; VECTOR_SUB_RDISTRIB];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
  SIMP_TAC[VSUM_SUB; FINITE_NUMSEG] THEN VECTOR_ARITH_TAC);;

let RDT_LAMBDA_SUB = prove
 (`!(f:num->real^K) g.
     ((lambda c. f c):real^K^N) - (lambda c. g c) = lambda c. f c - g c`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_SUB_COMPONENT; VECTOR_SUB_COMPONENT]);;

let RDT_DGV_SUB = prove
 (`!(G:real^N->real^N^N) G' y.
     (vectorize o G) differentiable (at y) /\ (vectorize o G') differentiable (at y)
     ==> rdt_dgv G y - rdt_dgv G' y = rdt_dgv (\z. G z - G' z) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_dgv; GSYM VECTORIZE_SUB; RDT_LAMBDA_SUB] THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[CART_EQ] THEN SIMP_TAC[LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF; VECTORIZE_SUB] THEN
  MATCH_MP_TAC(GSYM PARTIAL_DERIVATIVE_SUB) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The pointwise bound in one chart of the forcing of the difference of two  *)
(* steps,                                                                    *)
(*   (L(G) V - L(G') V) - (P(G') - P(G)),                                    *)
(* by the Lipschitz bounds of the fixed outer maps on rdt_sk.                *)
(* ------------------------------------------------------------------------- *)

let RDT_NORM_PASTECART_BOUND = prove
 (`!(x:real^M) (y:real^P) a b. norm x <= a /\ norm y <= b ==> norm(pastecart x y) <= a + b`,
  MESON_TAC[NORM_PASTECART_LE; REAL_LE_ADD2; REAL_LE_TRANS]);;

let RDT_FD_PT = prove
 (`!K1 MG BH LH.
     &0 <= MG
     ==> ?L. &0 <= L /\
             !U (G:real^N->real^N^N) G' H (V:real^N->real^N^N) y.
               metric_field U G /\ metric_field U G' /\ metric_field U H /\ y IN U /\
               smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
               norm(vectorize(G y)) <= K1 /\ (!w. norm w pow 2 <= K1 * (w dot (G y ** w))) /\
               norm(vectorize(G' y)) <= K1 /\
               (!w. norm w pow 2 <= K1 * (w dot (G' y ** w))) /\
               pde_jetn 1 (vectorize o G) y <= MG /\ pde_jetn 1 (vectorize o G') y <= MG /\
               pde_jetn 3 (vectorize o H) y <= BH /\ norm(vectorize(matrix_inv(H y))) <= LH
               ==> norm((pde_lop0 (\y. transp(matrix_inv(G y))) (\y c. pde_mlbb G H y c)
                                  (\y. pde_mlcc G H y) (vectorize o V) y -
                         pde_lop0 (\y. transp(matrix_inv(G' y))) (\y c. pde_mlbb G' H y c)
                                  (\y. pde_mlcc G' H y) (vectorize o V) y) -
                        (rdt_psi(rdt_kf G' H y) - rdt_psi(rdt_kf G H y)))
                   <= L * (&1 + pde_jetn 2 (vectorize o V) y) *
                      pde_jetn 1 (\z. vectorize(G z) - vectorize(G' z)) y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`0`; `BH:real`; `LH:real`] (INST_TYPE [`:N`,`:N`] RDT_GV_JETN)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gv"))) THEN
  MP_TAC(SPECL [`0`; `BH:real`; `LH:real`] (INST_TYPE [`:N`,`:N`] RDT_GDV_JETN)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gdv"))) THEN
  ABBREV_TAC `cD = &(dimindex(:N) * dimindex(:(N,N)finite_prod))` THEN
  SUBGOAL_THEN `&0 <= cD` ASSUME_TAC THENL [EXPAND_TAC "cD" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`K1:real`; `Cg + Cd:real`]
    (MATCH_MP RDT_SK_LIPSCHITZ RDT_PHIA_SMOOTH)) THEN
  DISCH_THEN(X_CHOOSE_THEN `LA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "la"))) THEN
  MP_TAC(SPECL [`K1:real`; `Cg + Cd:real`]
    (MATCH_MP RDT_SK_LIPSCHITZ RDT_PHIC_SMOOTH)) THEN
  DISCH_THEN(X_CHOOSE_THEN `LC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lc"))) THEN
  MP_TAC(REWRITE_RULE[SKOLEM_THM] (GEN `c:num` (SPECL [`K1:real`; `Cg + Cd:real`]
    (MATCH_MP RDT_SK_LIPSCHITZ (SPEC `c:num` RDT_PHIB_SMOOTH))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `LB:num->real` (LABEL_TAC "lb")) THEN
  SUBGOAL_THEN `!c. &0 <= (LB:num->real) c` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "lb" (MP_TAC o SPEC `c:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`K1:real`; `cD * MG + Cg + Cd:real`]
    (MATCH_MP RDT_SK_LIPSCHITZ RDT_PSI_SMOOTH)) THEN
  DISCH_THEN(X_CHOOSE_THEN `LP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp"))) THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) (LB:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(&(dimindex(:N) * dimindex(:N)) * LA + sum(1..dimindex(:N)) LB + LC) +
              LP * (&1 + cD)` THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G') /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o H) /\
                (!z. z IN U ==> ~(det((H:real^N->real^N^N) z) = &0))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(rdt_gv (H:real^N->real^N^N) y) <= Cg /\ norm(rdt_gdv H y) <= Cd`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "gv" (MP_TAC o SPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`]);
      USE_THEN "gdv" (MP_TAC o SPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`])] THEN
    REWRITE_TAC[RDT_JETN_0] THEN
    (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn 3 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                            (H:real^N->real^N^N)) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(rdt_dgv (G:real^N->real^N^N) y) <= cD * MG /\
                norm(rdt_dgv (G':real^N->real^N^N) y) <= cD * MG /\
                norm(rdt_dgv (\z. G z - G' z) y) <=
                cD * pde_jetn 1 (\z. vectorize(G z) - vectorize(G' z)) y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RDT_DGV_JETN);
      MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G':real^N->real^N^N`; `y:real^N`] RDT_DGV_JETN);
      MP_TAC(ISPECL [`0`; `U:real^N->bool`; `\z. (G:real^N->real^N^N) z - G' z`; `y:real^N`]
        RDT_DGV_JETN)] THEN
    ASM_REWRITE_TAC[RDT_JETN_0; ARITH_RULE `SUC 0 = 1`] THENL
     [STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cD * pde_jetn 1 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                   (G:real^N->real^N^N)) y` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cD * pde_jetn 1 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                   (G':real^N->real^N^N)) y` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_DEF; VECTORIZE_SUB] THEN ANTS_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_kc (G:real^N->real^N^N) H y IN rdt_sk K1 (Cg + Cd) /\
    rdt_kc (G':real^N->real^N^N) H y IN rdt_sk K1 (Cg + Cd) /\
    rdt_kf G H y IN rdt_sk K1 (cD * MG + Cg + Cd) /\
    rdt_kf G' H y IN rdt_sk K1 (cD * MG + Cg + Cd)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rdt_sk; IN_ELIM_THM; rdt_kc; rdt_kf; FSTCART_PASTECART; SNDCART_PASTECART;
                MATRIFY_VECTORIZE] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC RDT_NORM_PASTECART_BOUND THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  ABBREV_TAC `J1 = pde_jetn 1 (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (G z) -
                                    vectorize((G':real^N->real^N^N) z)) y` THEN
  ABBREV_TAC `J2 = pde_jetn 2 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               (V:real^N->real^N^N)) y` THEN
  SUBGOAL_THEN `&0 <= J2 /\ pde_jetn 0 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                         (V:real^N->real^N^N)) y <= J2 /\
                pde_jetn 1 ((vectorize:real^N^N->real^(N,N)finite_prod) o V) y <= J2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J2" THEN REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THEN
    MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((vectorize:real^N^N->real^(N,N)finite_prod) ((G:real^N->real^N^N) y) -
                     vectorize((G':real^N->real^N^N) y)) <= J1`
  ASSUME_TAC THENL
   [EXPAND_TAC "J1" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn 0 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                  ((G:real^N->real^N^N) z) - vectorize((G':real^N->real^N^N) z)) y` THEN
    CONJ_TAC THENL [REWRITE_TAC[RDT_JETN_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= J1` ASSUME_TAC THENL
   [EXPAND_TAC "J1" THEN REWRITE_TAC[PDE_JETN_POS]; ALL_TAC] THEN
  ABBREV_TAC `dG = norm((vectorize:real^N^N->real^(N,N)finite_prod) ((G:real^N->real^N^N) y) -
                        vectorize((G':real^N->real^N^N) y))` THEN
  SUBGOAL_THEN `norm(rdt_kc (G:real^N->real^N^N) H y - rdt_kc G' H y) = dG`
  ASSUME_TAC THENL
   [EXPAND_TAC "dG" THEN REWRITE_TAC[rdt_kc; PASTECART_SUB; VECTOR_SUB_REFL] THEN
    REWRITE_TAC[PASTECART_VEC; NORM_PASTECART_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(rdt_kf (G':real^N->real^N^N) H y - rdt_kf G H y) <= dG + cD * J1`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [NORM_SUB] THEN
    REWRITE_TAC[rdt_kf; PASTECART_SUB; VECTOR_SUB_REFL; PASTECART_VEC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^N^N->real^(N,N)finite_prod) ((G:real^N->real^N^N) y) -
                     vectorize((G':real^N->real^N^N) y)) +
                norm(pastecart (rdt_dgv G y - rdt_dgv G' y)
                               (vec 0:real^((N,(N,N)finite_prod)finite_prod,
                                            (N,(N,(N,N)finite_prod)finite_prod)finite_prod)
                                           finite_sum))` THEN
    REWRITE_TAC[NORM_PASTECART_LE; NORM_PASTECART_0] THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `G':real^N->real^N^N`; `y:real^N`] RDT_DGV_SUB) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "dG" THEN EXPAND_TAC "J1" THEN ASM_REWRITE_TAC[REAL_LE_LADD];
    ALL_TAC] THEN
  (* the coefficient part and the remainder part *)
  REWRITE_TAC[RDT_LOP0_SUB_COEF] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(dimindex(:N) * dimindex(:N)) * LA + sum(1..dimindex(:N)) LB + LC) * dG * J2 +
              LP * (dG + cD * J1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
      SUBGOAL_THEN `dG <= J1 /\ &0 <= dG` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "dG" THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&(dimindex(:N) * dimindex(:N)) * LA + sum(1..dimindex(:N)) LB + LC)`
    ASSUME_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&(dimindex(:N) * dimindex(:N)) * LA + sum(1..dimindex(:N)) LB + LC) * dG * J2 <=
      (&(dimindex(:N) * dimindex(:N)) * LA + sum(1..dimindex(:N)) LB + LC) * J2 * J1 /\
      LP * (dG + cD * J1) <= LP * (&1 + cD) * J1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y x' y' z. x <= x' /\ y <= y' /\ x' + y' <= z ==> x + y <= z`) THEN
    EXISTS_TAC `(&(dimindex(:N) * dimindex(:N)) * LA + sum(1..dimindex(:N)) LB + LC) * J2 * J1` THEN
    EXISTS_TAC `LP * (&1 + cD) * J1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= LP * (&1 + cD) * J1 /\
                  &0 <= (&(dimindex(:N) * dimindex(:N)) * LA +
                         sum(1..dimindex(:N)) LB + LC) * J1 /\
                  &0 <= (&(dimindex(:N) * dimindex(:N)) * LA +
                         sum(1..dimindex(:N)) LB + LC) * J2 * J1 /\
                  &0 <= LP * (&1 + cD) * J2 * J1`
    MP_TAC THENL [REPEAT CONJ_TAC THEN RDT_NN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH `!x:real^(N,N)finite_prod y a b.
                             norm x <= a /\ norm y <= b ==> norm(x - y) <= a + b`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `LP * norm(rdt_kf (G':real^N->real^N^N) H y - rdt_kf G H y)` THEN
    CONJ_TAC THENL [USE_THEN "lp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`\y:real^N. transp(matrix_inv((G:real^N->real^N^N) y)) -
                             transp(matrix_inv((G':real^N->real^N^N) y))`;
                 `\y c. pde_mlbb (G:real^N->real^N^N) H y c - pde_mlbb (G':real^N->real^N^N) H y c`;
                 `\y. pde_mlcc (G:real^N->real^N^N) H y - pde_mlcc (G':real^N->real^N^N) H y`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (V:real^N->real^N^N)`;
                 `y:real^N`] RDT_LOP0_PT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[VECTORIZE_SUB] THEN
  SUBGOAL_THEN
   `norm((vectorize:real^N^N->real^(N,N)finite_prod) (transp(matrix_inv((G:real^N->real^N^N) y))) -
         vectorize(transp(matrix_inv((G':real^N->real^N^N) y)))) <= LA * dG /\
    (!c. norm((vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                         ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                (pde_mlbb G H y c) - vectorize(pde_mlbb G' H y c)) <= (LB:num->real) c * dG) /\
    norm((vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                    ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
           (pde_mlcc G H y) - vectorize(pde_mlcc G' H y)) <= LC * dG`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM RDT_PHIA_KC] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rdt_has_const "rdt_kc" th && not(is_forall(concl th)))) THEN
      USE_THEN "la" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `c:num` THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `H:real^N->real^N^N`; `y:real^N`;
                     `c:num`] RDT_PHIB_KC) THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G':real^N->real^N^N`; `H:real^N->real^N^N`; `y:real^N`;
                     `c:num`] RDT_PHIB_KC) THEN
      ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
      EXPAND_TAC "dG" THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rdt_has_const "rdt_kc" th && not(is_forall(concl th)))) THEN
      USE_THEN "lb" (MP_TAC o SPEC `c:num`) THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `H:real^N->real^N^N`; `y:real^N`]
        RDT_PHIC_KC) THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G':real^N->real^N^N`; `H:real^N->real^N^N`; `y:real^N`]
        RDT_PHIC_KC) THEN
      ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
      EXPAND_TAC "dG" THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rdt_has_const "rdt_kc" th && not(is_forall(concl th)))) THEN
      USE_THEN "lc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= dG` ASSUME_TAC THENL [EXPAND_TAC "dG" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c a' b' c'. a <= a' /\ b <= b' /\ c <= c'
                           ==> a + b + c <= a' + b' + c'`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; PDE_JETN_POS]]);;

(* ------------------------------------------------------------------------- *)
(* tr_k Hess_h v is a smooth tensor field, and the L^2 bound of              *)
(* the forcing of the difference of two steps by |g - g'|_1^2, for g, g' in  *)
(* the ball and |v|_s^2 <= K.                                                *)
(* ------------------------------------------------------------------------- *)

let RDT_TRHESS_SMOOTH = prove
 (`!top atlas (k:A->real^N^N) h v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas k /\ riemannian_metric atlas h /\
     mfd_tensor2_smooth atlas v
     ==> mfd_tensor2_smooth atlas (\x. pde_trhess atlas k h v x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_tensor2_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) /\
    metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (k:A->real^N^N)) /\
    metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (h:A->real^N^N)) /\
    smooth_map_on (IMAGE (SND c) (FST c))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c (v:A->real^N^N))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ASM_MESON_TAC[riemannian_metric];
      ASM_MESON_TAC[riemannian_metric]; ASM_MESON_TAC[mfd_tensor2_smooth]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (k:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`]
    RDT_COEF_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `pde_lop0 (\y. transp(matrix_inv(metric_local atlas (c:(A->bool)#(A->real^N))
                                                (k:A->real^N^N) y)))
                       (\y c'. pde_mlbb (metric_local atlas c k)
                                        (metric_local atlas c (h:A->real^N^N)) y c')
                       (\y. pde_mlcc (metric_local atlas c k) (metric_local atlas c h) y)
                       ((vectorize:real^N^N->real^(N,N)finite_prod) o
                        metric_local atlas c (v:A->real^N^N))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(\x. pde_trhess atlas (k:A->real^N^N) h (v:A->real^N^N) x) =
                  pde_trhess atlas k h v` SUBST1_TAC THENL [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `k:A->real^N^N`; `h:A->real^N^N`;
                   `v:A->real^N^N`; `z:real^N`] PDE_ML_TRHESS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC PDE_ML_LOP0_FORM THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RDT_LOP0_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let RDT_FORCING_SMOOTH = prove
 (`!top atlas (h:A->real^N^N) g.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ riemannian_metric atlas g
     ==> mfd_tensor2_smooth atlas (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_tensor2_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `h:A->real^N^N`; `g:A->real^N^N`]
    RDT_FORCING_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[o_DEF]);;

let RDT_ML_SUB4 = prove
 (`!atlas (c:(A->bool)#(A->real^N)) (a:A->real^N^N) b c' d y.
     (vectorize:real^N^N->real^(N,N)finite_prod)
       (metric_local atlas c (\x. (a x - b x) - (c' x - d x)) y) =
     (vectorize(metric_local atlas c a y) - vectorize(metric_local atlas c b y)) -
     (vectorize(metric_local atlas c c' y) - vectorize(metric_local atlas c d y))`,
  REWRITE_TAC[METRIC_LOCAL_SUB; VECTORIZE_SUB; ETA_AX]);;

let RDT_FD_MNORM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s m B K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ s + 3 <= m /\ &0 <= B /\ &0 <= K
     ==> ?CL. &0 <= CL /\
           !h g g' v.
             riemannian_metric atlas h /\ pde_cbound atlas n0 cs ks m B h /\
             riemannian_metric atlas g /\ pde_cbound atlas n0 cs ks 0 K g /\
             pde_mnorm2 atlas n0 cs psi s g <= K /\
             riemannian_metric atlas g' /\ pde_cbound atlas n0 cs ks 0 K g' /\
             pde_mnorm2 atlas n0 cs psi s g' <= K /\
             mfd_tensor2_smooth atlas v /\ pde_mnorm2 atlas n0 cs psi s v <= K
             ==> pde_mnorm2 atlas n0 cs psi 0
                   (\x. (pde_trhess atlas g h v x - pde_trhess atlas g' h v x) -
                        ((pde_rdt_rhs atlas h g' x - pde_trhess atlas g' h g' x) -
                         (pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x)))
                 <= CL * pde_mnorm2 atlas n0 cs psi 1 (\x. g x - g' x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `1`; `0`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `m:num`; `B:real`; `K:real`] RDT_BALL_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `MJ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s - dimindex(:N)`] RDT_SOB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s - dimindex(:N) + dimindex(:N) = s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CJ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  MP_TAC(SPECL [`K:real`; `MJ:real`; `&(CARD(pde_index_lists m (:N))) * B`;
                `&(dimindex(:N) * dimindex(:N)) * B`] RDT_FD_PT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fd"))) THEN
  SUBGOAL_THEN `1 <= s - dimindex(:N) /\ 2 <= s - dimindex(:N) /\ 3 <= m` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c1 = L * (&1 + CJ * (&1 + K))` THEN
  SUBGOAL_THEN `&0 <= c1` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN RDT_NN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `DS = sum {i | i < n0} (DD:num->real)` THEN
  SUBGOAL_THEN `!i. i < n0 ==> &0 <= (DD:num->real) i /\ DD i <= DS` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!j. j < n0 ==> &0 <= (DD:num->real) j` ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "cd" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "DS" THEN
    MP_TAC(ISPECL [`DD:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= DS` ASSUME_TAC THENL
   [EXPAND_TAC "DS" THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `CC = &(CARD(pde_index_lists 0 (:N))) *
                   (&2 * c1 pow 2 * (&1 pow 2 * &(CARD(pde_index_lists 1 (:N)))))` THEN
  SUBGOAL_THEN `&0 <= CC` ASSUME_TAC THENL [EXPAND_TAC "CC" THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `CC * DS` THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
                                            ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N^N`; `g:A->real^N^N`; `g':A->real^N^N`; `v:A->real^N^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Fd = \x. (pde_trhess atlas (g:A->real^N^N) h (v:A->real^N^N) x -
                        pde_trhess atlas (g':A->real^N^N) h v x) -
                       ((pde_rdt_rhs atlas h g' x - pde_trhess atlas g' h g' x) -
                        (pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x))` THEN
  SUBGOAL_THEN
   `mfd_tensor2_smooth atlas (\x. pde_trhess atlas (g:A->real^N^N) h (v:A->real^N^N) x) /\
    mfd_tensor2_smooth atlas (\x. pde_trhess atlas (g':A->real^N^N) h v x) /\
    mfd_tensor2_smooth atlas (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x) /\
    mfd_tensor2_smooth atlas (\x. pde_rdt_rhs atlas h g' x - pde_trhess atlas g' h g' x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_TRHESS_SMOOTH; MATCH_MP_TAC RDT_TRHESS_SMOOTH;
      MATCH_MP_TAC RDT_FORCING_SMOOTH; MATCH_MP_TAC RDT_FORCING_SMOOTH] THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_tensor2_smooth atlas
      (\x. pde_trhess atlas (g:A->real^N^N) h (v:A->real^N^N) x -
           pde_trhess atlas (g':A->real^N^N) h v x) /\
    mfd_tensor2_smooth atlas
      (\x. (pde_rdt_rhs atlas h g' x - pde_trhess atlas g' h g' x) -
           (pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x)) /\
    mfd_tensor2_smooth atlas (\x. (g:A->real^N^N) x - g' x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[RIEMANNIAN_METRIC_TENSOR2_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas (Fd:A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Fd" THEN MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RDT_MNORM2_HS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {i | i < n0}
                (\i. CC * (DD:num->real) i * pde_mnorm2 atlas n0 cs psi 1
                                              (\x. (g:A->real^N^N) x - g' x))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM RDT_MNORM2_HS] THEN
    SIMP_TAC[SUM_LMUL; SUM_RMUL; FINITE_NUMSEG_LT] THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC;
                                                                           REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `U = IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`; `Fd:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `mfd_tensor2_smooth atlas (Fd:A->real^N^N)` THEN
    REWRITE_TAC[mfd_tensor2_smooth] THEN DISCH_THEN(MP_TAC o SPEC `(cs:num->(A->bool)#(A->real^N)) i`) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(TH:num->A->real) i`;
                 `(KT:num->real^N->bool) i`; `\x. (g:A->real^N^N) x - g' x`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `mfd_tensor2_smooth atlas (\x. (g:A->real^N^N) x - g' x)` THEN
    REWRITE_TAC[mfd_tensor2_smooth] THEN DISCH_THEN(MP_TAC o SPEC `(cs:num->(A->bool)#(A->real^N)) i`) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `CC * rdt_hs U 1 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                     ((TH:num->A->real) i
                                        (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                                      metric_local atlas (cs i) (\x. (g:A->real^N^N) x - g' x) z))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      rdt_has_const "pde_tensor_smooth" th && is_forall (concl th) &&
      rdt_has_const "rdt_hs" th)) THEN
    ASM_REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ]] THEN
  EXPAND_TAC "CC" THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(ks:num->real^N->bool) i`; `(KT:num->real^N->bool) i`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                         metric_local atlas (cs i) (Fd:A->real^N^N) z)`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                         metric_local atlas (cs i) (\x. (g:A->real^N^N) x - g' x) z)`;
                 `\y:real^N. &0`; `0`; `1`; `c1:real`; `&1`; `&0`; `&0`] RDT_HS_FROM_POINTWISE) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]] THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; REAL_POS; LIFT_NUM; REAL_POW_ZERO; ARITH_EQ;
                  INTEGRAL_0; DROP_VEC; REAL_LE_REFL] THEN
  REWRITE_TAC[PDE_INDEX_LISTS_0; IN_SING] THEN
  MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[iterated_partial; REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID] THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`h:A->real^N^N`; `g:A->real^N^N`; `i:num`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`h:A->real^N^N`; `g':A->real^N^N`; `i:num`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "sob" (MP_TAC o SPECL [`v:A->real^N^N`; `K:real`; `i:num`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (v:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_tensor2_smooth atlas (v:A->real^N^N)` THEN
    REWRITE_TAC[mfd_tensor2_smooth] THEN
    DISCH_THEN(MP_TAC o SPEC `(cs:num->(A->bool)#(A->real^N)) i`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the chart representative of Fd at y *)
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [VECTORIZE_CMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [NORM_MUL] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod)
      (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (Fd:A->real^N^N) y) =
    (pde_lop0 (\y. transp(matrix_inv(metric_local atlas (cs i) (g:A->real^N^N) y)))
              (\y c. pde_mlbb (metric_local atlas (cs i) g) (metric_local atlas (cs i) h) y c)
              (\y. pde_mlcc (metric_local atlas (cs i) g) (metric_local atlas (cs i) h) y)
              ((vectorize:real^N^N->real^(N,N)finite_prod) o
               metric_local atlas (cs i) (v:A->real^N^N)) y -
     pde_lop0 (\y. transp(matrix_inv(metric_local atlas (cs i) (g':A->real^N^N) y)))
              (\y c. pde_mlbb (metric_local atlas (cs i) g') (metric_local atlas (cs i) h) y c)
              (\y. pde_mlcc (metric_local atlas (cs i) g') (metric_local atlas (cs i) h) y)
              (vectorize o metric_local atlas (cs i) v) y) -
    (rdt_psi(rdt_kf (metric_local atlas (cs i) g') (metric_local atlas (cs i) h) y) -
     rdt_psi(rdt_kf (metric_local atlas (cs i) g) (metric_local atlas (cs i) h) y))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Fd" THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `(cs:num->(A->bool)#(A->real^N)) i`;
                   `\x. pde_trhess atlas (g:A->real^N^N) h (v:A->real^N^N) x`;
                   `\x. pde_trhess atlas (g':A->real^N^N) h (v:A->real^N^N) x`;
                   `\x. pde_rdt_rhs atlas h (g':A->real^N^N) x - pde_trhess atlas g' h g' x`;
                   `\x. pde_rdt_rhs atlas h (g:A->real^N^N) x - pde_trhess atlas g h g x`;
                   `y:real^N`] RDT_ML_SUB4) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `h:A->real^N^N`; `g:A->real^N^N`]
      RDT_FORCING_CHART) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `h:A->real^N^N`; `g':A->real^N^N`]
      RDT_FORCING_CHART) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && rdt_has_const "rdt_psi" th &&
      can (find_term ((=) `g:A->real^N^N`)) (concl th) &&
      not(can (find_term ((=) `g':A->real^N^N`)) (concl th)))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && rdt_has_const "rdt_psi" th &&
      can (find_term ((=) `g':A->real^N^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    SUBGOAL_THEN `(\x. pde_trhess atlas (g:A->real^N^N) h (v:A->real^N^N) x) =
                  pde_trhess atlas g h v /\
                  (\x. pde_trhess atlas (g':A->real^N^N) h v x) = pde_trhess atlas g' h v`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `g:A->real^N^N`; `h:A->real^N^N`;
                   `v:A->real^N^N`; `y:real^N`] PDE_ML_TRHESS_CHART) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `g':A->real^N^N`; `h:A->real^N^N`;
                   `v:A->real^N^N`; `y:real^N`] PDE_ML_TRHESS_CHART) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THEN
    MATCH_MP_TAC PDE_ML_LOP0_FORM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) y))
                <= &1` ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cutoffs (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) psi` THEN
    REWRITE_TAC[pde_cutoffs] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `chart_inv ((cs:num->(A->bool)#(A->real^N)) i) y` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&1`)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_const t) = "compact_in" with _ -> false))
            (concl th)))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn 1 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                       metric_local atlas (cs i) (\x. (g:A->real^N^N) x - g' x) z)) y =
    pde_jetn 1 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas (cs i) g z) - vectorize(metric_local atlas (cs i) g' z)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `(OO:num->real^N->bool) i` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[METRIC_LOCAL_SUB; MATRIX_CMUL_LID; VECTORIZE_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn 1 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y <= MJ /\
    pde_jetn 1 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                metric_local atlas (cs i) (g':A->real^N^N)) y <= MJ /\
    pde_jetn 3 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                metric_local atlas (cs i) (h:A->real^N^N)) y <=
    &(CARD(pde_index_lists m (:N))) * B /\
    pde_jetn 2 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                metric_local atlas (cs i) (v:A->real^N^N)) y <= CJ * (&1 + K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `pde_jetn (s - dimindex(:N)) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y`;
      EXISTS_TAC `pde_jetn (s - dimindex(:N)) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g':A->real^N^N)) y`;
      EXISTS_TAC `pde_jetn m ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)) y`;
      EXISTS_TAC `pde_jetn (s - dimindex(:N)) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (v:A->real^N^N)) y`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm((pde_lop0 (\y. transp(matrix_inv(metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                                       (g:A->real^N^N) y)))
                   (\y c. pde_mlbb (metric_local atlas (cs i) g)
                                   (metric_local atlas (cs i) (h:A->real^N^N)) y c)
                   (\y. pde_mlcc (metric_local atlas (cs i) g) (metric_local atlas (cs i) h) y)
                   ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas (cs i) (v:A->real^N^N)) y -
          pde_lop0 (\y. transp(matrix_inv(metric_local atlas (cs i) (g':A->real^N^N) y)))
                   (\y c. pde_mlbb (metric_local atlas (cs i) g') (metric_local atlas (cs i) h) y c)
                   (\y. pde_mlcc (metric_local atlas (cs i) g') (metric_local atlas (cs i) h) y)
                   (vectorize o metric_local atlas (cs i) v) y) -
         (rdt_psi(rdt_kf (metric_local atlas (cs i) g') (metric_local atlas (cs i) h) y) -
          rdt_psi(rdt_kf (metric_local atlas (cs i) g) (metric_local atlas (cs i) h) y)))` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `L * (&1 + pde_jetn 2 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                   metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                     (v:A->real^N^N)) y) *
              pde_jetn 1 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                (metric_local atlas (cs i) (g:A->real^N^N) z) -
                              vectorize(metric_local atlas (cs i) (g':A->real^N^N) z)) y` THEN
  CONJ_TAC THENL
   [USE_THEN "fd" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "c1" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[PDE_JETN_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Gronwall with dissipation,                                                *)
(*   Y' <= -c Z + C Y + Gf, Y(a) = 0  ==>  Y(T) + c int Z <= exp(C(T-a)) int Gf.*)
(* ------------------------------------------------------------------------- *)

let RDT_SHIFT_DERIV0 = prove
 (`!(Y:real->real) D a t.
     (Y has_real_derivative D) (atreal (t + a))
     ==> ((\r. Y(r + a)) has_real_derivative D) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r:real. r + a`; `Y:real->real`; `&1`; `D:real`; `t:real`]
    REAL_DIFF_CHAIN_ATREAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\r:real. r`; `&1`; `\r:real. a:real`; `&0`; `atreal t`]
      HAS_REAL_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_ADD_RID];
    REWRITE_TAC[o_DEF; REAL_MUL_RID]]);;

let RDT_EXP_NEG_CONT = prove
 (`!C s. (\r. exp(--(C * r))) real_continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\r. exp(--(C * r))) = exp o (\r. --(C * r))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[REAL_CONTINUOUS_ON_NEG; REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID;
           REAL_CONTINUOUS_ON_EXP]);;

let RDT_GRONWALL_DISS = prove
 (`!(Y:real->real) Z Gf D a Tm c C.
     &0 <= c /\ &0 <= C /\ a <= Tm /\ Y a = &0 /\
     Y real_continuous_on real_interval[a,Tm] /\ Z real_continuous_on real_interval[a,Tm] /\
     Gf real_continuous_on real_interval[a,Tm] /\
     (!t. a <= t /\ t <= Tm ==> &0 <= Z t /\ &0 <= Gf t) /\
     (!t. a < t /\ t < Tm ==> (Y has_real_derivative D t) (atreal t) /\
                              D t <= --(c * Z t) + C * Y t + Gf t)
     ==> Y Tm + c * real_integral (real_interval[a,Tm]) Z <=
         exp(C * (Tm - a)) * real_integral (real_interval[a,Tm]) Gf`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (Y:real->real)(r + a)`; `\r. (D:real->real)(r + a)`;
                 `\r. c * (Z:real->real)(r + a)`; `\r. (Gf:real->real)(r + a)`; `C:real`;
                 `C:real`; `Tm - a:real`] PDE_GRONWALL_W) THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ME_SHIFT_CONT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC PDE_ME_SHIFT_CONT THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_ME_SHIFT_CONT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r + a:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "has_real_derivative" th)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_SIMP_TAC[RDT_SHIFT_DERIV0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Tm - a:real`) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_ADD; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,Tm - a]) (\r. (Z:real->real)(r + a)) =
    real_integral (real_interval[a,Tm]) Z /\
    real_integral (real_interval[&0,Tm - a]) (\r. (Gf:real->real)(r + a)) =
    real_integral (real_interval[a,Tm]) Gf`
  (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_ME_RINT_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. (Z:real->real)(r + a)) real_integrable_on real_interval[&0,Tm - a] /\
    (\r. (Gf:real->real)(r + a)) real_integrable_on real_interval[&0,Tm - a] /\
    (\r. exp(--(C * r)) * c * (Z:real->real)(r + a)) real_integrable_on
       real_interval[&0,Tm - a] /\
    (\r. exp(--(C * r)) * (Gf:real->real)(r + a)) real_integrable_on real_interval[&0,Tm - a]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THENL
     [MATCH_MP_TAC PDE_ME_SHIFT_CONT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_ME_SHIFT_CONT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN REWRITE_TAC[RDT_EXP_NEG_CONT] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC PDE_ME_SHIFT_CONT THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN REWRITE_TAC[RDT_EXP_NEG_CONT] THEN
      MATCH_MP_TAC PDE_ME_SHIFT_CONT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `T1 = Tm - a:real` THEN
  SUBGOAL_THEN `&0 <= T1` ASSUME_TAC THENL [EXPAND_TAC "T1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--(C * T1)) * c * real_integral (real_interval[&0,T1]) (\r. (Z:real->real)(r + a)) <=
    real_integral (real_interval[&0,T1]) (\r. exp(--(C * r)) * c * Z(r + a)) /\
    real_integral (real_interval[&0,T1]) (\r. exp(--(C * r)) * (Gf:real->real)(r + a)) <=
    real_integral (real_interval[&0,T1]) (\r. Gf(r + a))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_LMUL] THEN
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> --y <= --x`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `r + a:real` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Z:real->real`)) (concl th) &&
          not(rdt_has_const "has_real_derivative" th))) THEN
        ANTS_TAC THENL [EXPAND_TAC "T1" THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `r + a:real` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Gf:real->real`)) (concl th) &&
          not(rdt_has_const "has_real_derivative" th))) THEN
        ANTS_TAC THENL [EXPAND_TAC "T1" THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `exp(--(C * T1)) * ((Y:real->real) Tm +
                c * real_integral (real_interval[&0,T1]) (\r. (Z:real->real)(r + a))) <=
                real_integral (real_interval[&0,T1]) (\r. (Gf:real->real)(r + a))`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(C * T1)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (MATCH_MP REAL_LT_IMP_LE
    (ASSUME `&0 < exp(C * T1)`))) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0; REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* The contraction of the step in sup_t L^2 + int H^1 (RDT_CONTRACT): the    *)
(* level-0 energy of v - v' with dissipation, the forcing bounded by         *)
(* |g - g'|_1^2, Gronwall with dissipation, and tau small so that            *)
(* exp(C tau) <= 2.                                                          *)
(* ------------------------------------------------------------------------- *)

let RDT_CONTRACT_ARITH = prove
 (`!Yt IZ IG D E c0 lam ep CL.
     &0 <= Yt /\ &0 <= IZ /\ &0 <= IG /\ IG <= D /\ &0 <= D /\ &0 < c0 /\ c0 <= &1 /\
     c0 <= lam / &4 /\ &0 <= ep /\ &0 <= CL /\ &4 * ep * (CL + &1) = c0 /\
     &0 <= E /\ E <= &2 /\ Yt + lam / &4 * IZ <= E * (ep * CL * IG)
     ==> Yt + IZ <= D / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `E * (ep * CL * IG) <= &2 * (ep * CL * D)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ep * CL * D <= ep * (CL + &1) * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (ep * (CL + &1) * D) = c0 / &2 * D` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `c0:real`)) (concl th))) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 * Yt <= Yt /\ c0 * IZ <= lam / &4 * IZ` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 * (Yt + IZ) <= c0 * (D / &2)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let RDT_CONTRACT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s m B K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ s + 3 <= m /\ &0 <= B /\ &0 < K
     ==> ?tau2. &0 < tau2 /\
           !tau g0 a. &0 < tau /\ tau <= tau2 /\
                      riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks m B g0
             ==> !g g' v v' D.
                   pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
                   pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g' /\
                   pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v' /\
                   pde_rdt_step (top,atlas) a (a + tau) g0 g v /\
                   pde_rdt_step (top,atlas) a (a + tau) g0 g' v' /\
                   (!t. a <= t /\ t < a + tau
                        ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) +
                            real_integral (real_interval[a,t])
                              (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) <= D)
                   ==> !t. a <= t /\ t < a + tau
                           ==> pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - v' t x) +
                               real_integral (real_interval[a,t])
                                 (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x))
                               <= D / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `m:num`; `B:real`; `K:real`] RDT_BALL_COEF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `Qb:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bc"))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `m:num`; `B:real`; `K:real`] RDT_FD_MNORM) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `CL:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fm"))) THEN
  ABBREV_TAC `c0 = min (&1) (lam / &4)` THEN
  SUBGOAL_THEN `&0 < c0 /\ c0 <= &1 /\ c0 <= lam / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ep = c0 * inv(&4 * (CL + &1))` THEN
  SUBGOAL_THEN `&0 < ep /\ &4 * ep * (CL + &1) = c0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * (CL + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "ep" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      REWRITE_TAC[REAL_ARITH `&4 * (c * i) * x = c * ((&4 * x) * i)`] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_RID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `lam:real`; `M:real`; `ep:real`] RDT_MENERGY_0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "me0"))) THEN
  EXISTS_TAC `inv(&2 * (C + &1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `g0:A->real^N^N`; `a:real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`g:real->A->real^N^N`; `g':real->A->real^N^N`; `v:real->A->real^N^N`;
                       `v':real->A->real^N^N`; `D:real`] THEN
  STRIP_TAC THEN
  (* facts from the balls and the steps *)
  SUBGOAL_THEN
   `(!t. a <= t /\ t < a + tau
         ==> riemannian_metric atlas ((g:real->A->real^N^N) t) /\
             pde_cbound atlas n0 cs ks 0 K (g t) /\ pde_mnorm2 atlas n0 cs psi s (g t) <= K) /\
    (!t. a <= t /\ t < a + tau
         ==> riemannian_metric atlas ((g':real->A->real^N^N) t) /\
             pde_cbound atlas n0 cs ks 0 K (g' t) /\ pde_mnorm2 atlas n0 cs psi s (g' t) <= K) /\
    (!t. a <= t /\ t < a + tau
         ==> riemannian_metric atlas ((v':real->A->real^N^N) t) /\
             pde_cbound atlas n0 cs ks 0 K (v' t) /\ pde_mnorm2 atlas n0 cs psi s (v' t) <= K) /\
    pde_tfam_from atlas a (a + tau) g /\ pde_tfam_from atlas a (a + tau) g' /\
    pde_tfam_from atlas a (a + tau) v' /\ pde_tfam_from atlas a (a + tau) v /\
    (!x. x IN topspace top ==> v a x = (g0:A->real^N^N) x /\ v' a x = g0 x)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (g:real->A->real^N^N)`;
      `pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (g':real->A->real^N^N)`;
      `pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (v':real->A->real^N^N)`;
      `pde_rdt_step (top,atlas) a (a + tau) g0 g (v:real->A->real^N^N)`;
      `pde_rdt_step (top,atlas) a (a + tau) g0 g' (v':real->A->real^N^N)`] THEN
    REWRITE_TAC[pde_rdt_ball; pde_rdt_step; pde_mlin_sol] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < a + tau` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the difference solves the frozen problem *)
  ABBREV_TAC `Fd = \t x. (pde_trhess atlas ((g:real->A->real^N^N) t) g0
                                 ((v':real->A->real^N^N) t) x -
                          pde_trhess atlas ((g':real->A->real^N^N) t) g0 (v' t) x) -
                         ((pde_rdt_rhs atlas g0 (g' t) x - pde_trhess atlas (g' t) g0 (g' t) x) -
                          (pde_rdt_rhs atlas g0 (g t) x - pde_trhess atlas (g t) g0 (g t) x))` THEN
  SUBGOAL_THEN
   `pde_mlin_sol (top,atlas) a (a + tau) g g0 Fd (\x. mat 0)
      (\t x. (v:real->A->real^N^N) t x - v' t x)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Fd" THEN MATCH_MP_TAC RDT_DIFF_SOL THEN
    EXISTS_TAC `g0:A->real^N^N` THEN
    ASM_SIMP_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`pde_rdt_step (top,atlas) a (a + tau) g0 g (v:real->A->real^N^N)`;
      `pde_rdt_step (top,atlas) a (a + tau) g0 g' (v':real->A->real^N^N)`] THEN
    REWRITE_TAC[pde_rdt_step] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* smoothness of the families *)
  SUBGOAL_THEN
   `pde_tfam_from atlas a (a + tau) (Fd:real->A->real^N^N) /\
    pde_tfam_from atlas a (a + tau) (\t x. (v:real->A->real^N^N) t x - v' t x) /\
    pde_tfam_from atlas a (a + tau) (\t x. (g:real->A->real^N^N) t x - g' t x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]] THEN
    EXPAND_TAC "Fd" THEN MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_ME_TFAM_SUB THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_TRHESS_TFAM THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RDT_TRHESS_TFAM THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC PDE_RDT_REMAINDER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC PDE_RDT_REMAINDER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the energy inequality at each time *)
  SUBGOAL_THEN
   `?Dfn. !r. a < r /\ r < a + tau
              ==> ((\r. pde_mnorm2 atlas n0 cs psi 0 (\x. (v:real->A->real^N^N) r x - v' r x))
                   has_real_derivative Dfn r) (atreal r) /\
                  Dfn r <= --(lam / &4) * pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x) +
                           C * pde_mnorm2 atlas n0 cs psi 0 (\x. v r x - v' r x) +
                           ep * CL * pde_mnorm2 atlas n0 cs psi 1
                                       (\x. (g:real->A->real^N^N) r x - g' r x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `a <= r /\ r < a + tau` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "me0" (MP_TAC o SPECL
     [`a:real`; `a + tau`; `g:real->A->real^N^N`; `g0:A->real^N^N`; `Fd:real->A->real^N^N`;
      `\x:A. mat 0:real^N^N`; `\t x. (v:real->A->real^N^N) t x - v' t x`; `r:real`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_cbound" th &&
        can (find_term ((=) `g:real->A->real^N^N`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "bc" (MP_TAC o SPECL [`g0:A->real^N^N`; `(g:real->A->real^N^N) r`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[PDE_ML_COEFF_FUN] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `rdt_cjet (s DIV 2 + 1)
                    (\y. transp(matrix_inv(metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                             ((g:real->A->real^N^N) r) y)))
                    (\y c. pde_mlbb (metric_local atlas (cs i) (g r))
                                    (metric_local atlas (cs i) (g0:A->real^N^N)) y c)
                    (\y. pde_mlcc (metric_local atlas (cs i) (g r)) (metric_local atlas (cs i) g0) y)
                    y` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC RDT_CJET_MONO THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Dr:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Dr:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x <= a + b + e * f ==> e * f <= e * g ==> x <= a + b + e * g`)) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN
    USE_THEN "fm" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `a + tau`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. a <= r /\ r < a + tau
        ==> mfd_tensor2_smooth atlas (\x. (v:real->A->real^N^N) r x - v' r x) /\
            mfd_tensor2_smooth atlas (\x. (g:real->A->real^N^N) r x - g' r x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                     `a + tau`; `\t x. (v:real->A->real^N^N) t x - v' t x`; `r:real`]
        PDE_ML_TFAM_SLICE);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                     `a + tau`; `\t x. (g:real->A->real^N^N) t x - g' t x`; `r:real`]
        PDE_ML_TFAM_SLICE)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. a <= r /\ r < a + tau
        ==> &0 <= pde_mnorm2 atlas n0 cs psi 0 (\x. (v:real->A->real^N^N) r x - v' r x) /\
            &0 <= pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x) /\
            &0 <= pde_mnorm2 atlas n0 cs psi 0 (\x. (g:real->A->real^N^N) r x - g' r x) /\
            &0 <= pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
    ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. pde_mnorm2 atlas n0 cs psi 0 (\x. (v:real->A->real^N^N) r x - v' r x))
      real_continuous_on real_interval[a,t] /\
    (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (v:real->A->real^N^N) r x - v' r x))
      real_continuous_on real_interval[a,t] /\
    (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (g:real->A->real^N^N) r x - g' r x))
      real_continuous_on real_interval[a,t]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                     `psi:num->A->real`; `a:real`; `a + tau`; `t:real`;
                     `\t x. (v:real->A->real^N^N) t x - v' t x`; `0`] RDT_MNORM2_CONT);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                     `psi:num->A->real`; `a:real`; `a + tau`; `t:real`;
                     `\t x. (v:real->A->real^N^N) t x - v' t x`; `1`] RDT_MNORM2_CONT);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                     `psi:num->A->real`; `a:real`; `a + tau`; `t:real`;
                     `\t x. (g:real->A->real^N^N) t x - g' t x`; `1`] RDT_MNORM2_CONT)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. pde_mnorm2 atlas n0 cs psi 0 (\x. (v:real->A->real^N^N) r x - v' r x)`;
    `\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (v:real->A->real^N^N) r x - v' r x)`;
    `\r. ep * CL * pde_mnorm2 atlas n0 cs psi 1 (\x. (g:real->A->real^N^N) r x - g' r x)`;
    `Dfn:real->real`; `a:real`; `t:real`; `lam / &4`; `C:real`] RDT_GRONWALL_DISS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `pde_mnorm2 atlas n0 cs psi 0 (\x. (v:real->A->real^N^N) a x - v' a x) =
        pde_mnorm2 atlas n0 cs psi 0 (\x:A. mat 0:real^N^N)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC RDT_MNORM2_CONG THEN EXISTS_TAC `top:A topology` THEN
        ASM_SIMP_TAC[MATRIX_SUB_REFL] THEN
        UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
        REWRITE_TAC[pde_cover] THEN MESON_TAC[];
        REWRITE_TAC[PDE_ME_MNORM2_ZERO]];
      REPEAT(MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_mnorm2" th &&
        not(rdt_has_const "real_integral" th) && not(rdt_has_const "has_real_derivative" th) &&
        not(rdt_has_const "pde_cbound" th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "has_real_derivative" th &&
        can (find_term ((=) `Dfn:real->real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (g:real->A->real^N^N) r x - g' r x))
      real_integrable_on real_interval[a,t] /\
    (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (v:real->A->real^N^N) r x - v' r x))
      real_integrable_on real_interval[a,t]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_LMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= real_integral (real_interval[a,t])
            (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (g:real->A->real^N^N) r x - g' r x)) /\
    &0 <= real_integral (real_interval[a,t])
            (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (v:real->A->real^N^N) r x - v' r x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    (MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
       is_forall(concl th) && rdt_has_const "pde_mnorm2" th &&
       not(rdt_has_const "real_integral" th) && not(rdt_has_const "has_real_derivative" th) &&
       not(rdt_has_const "pde_cbound" th))) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,t])
      (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (g:real->A->real^N^N) r x - g' r x)) <= D /\
    &0 <= D /\
    &0 <= pde_mnorm2 atlas n0 cs psi 0 (\x. (v:real->A->real^N^N) t x - v' t x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "real_integral" th &&
        can (find_term ((=) `D:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_mnorm2" th &&
        not(rdt_has_const "real_integral" th) && not(rdt_has_const "has_real_derivative" th) &&
        not(rdt_has_const "pde_cbound" th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "real_integral" th &&
        can (find_term ((=) `D:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_ADD_RID] THEN DISCH_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_mnorm2" th &&
        not(rdt_has_const "real_integral" th) && not(rdt_has_const "has_real_derivative" th) &&
        not(rdt_has_const "pde_cbound" th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_mnorm2" th &&
        not(rdt_has_const "real_integral" th) && not(rdt_has_const "has_real_derivative" th) &&
        not(rdt_has_const "pde_cbound" th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(C * (t - a)) <= &2 /\ &0 <= exp(C * (t - a))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE] THEN
    SUBGOAL_THEN `&0 <= C * (t - a) /\ C * (t - a) <= inv(&2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * inv(&2 * (C + &1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &2 * (C + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `C * (t - a):real` REAL_EXP_BOUND_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RDT_CONTRACT_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`real_integral (real_interval[a,t])
       (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (g:real->A->real^N^N) r x - g' r x))`;
    `exp(C * (t - a))`; `c0:real`; `lam:real`; `ep:real`; `CL:real`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* PDE_RDT_ITERATION: s = 2N+4, m = s+3; K and tau from RDT_BALL_INV and     *)
(* RDT_CONTRACT applied to max B 0.                                          *)
(* ------------------------------------------------------------------------- *)

let PDE_RDT_ITERATION = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))
        ==> ?s m. !B. ?K tau. &0 < tau /\
              !g0 a. riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks m B g0
                ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (\t. g0) /\
                    (!g v. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
                           pde_rdt_step (top,atlas) a (a + tau) g0 g v
                           ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v) /\
                    (!g g' v v' D.
                        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
                        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g' /\
                        pde_rdt_step (top,atlas) a (a + tau) g0 g v /\
                        pde_rdt_step (top,atlas) a (a + tau) g0 g' v' /\
                        (!t. a <= t /\ t < a + tau
                             ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) +
                                 real_integral (real_interval[a,t])
                                   (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x))
                                 <= D)
                        ==> !t. a <= t /\ t < a + tau
                                ==> pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - v' t x) +
                                    real_integral (real_interval[a,t])
                                      (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x))
                                    <= D / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `2 * dimindex(:N) + 4` THEN EXISTS_TAC `(2 * dimindex(:N) + 4) + 3` THEN
  X_GEN_TAC `B:real` THEN
  ABBREV_TAC `B' = max B (&0)` THEN
  SUBGOAL_THEN `&0 <= B' /\ B <= B'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `2 * dimindex(:N) + 4`; `(2 * dimindex(:N) + 4) + 3`; `B':real`]
    RDT_BALL_INV) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `tau1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inv"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `2 * dimindex(:N) + 4`; `(2 * dimindex(:N) + 4) + 3`; `B':real`; `K:real`]
    RDT_CONTRACT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "con"))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `min tau1 tau2`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`g0:A->real^N^N`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_cbound atlas n0 cs ks ((2 * dimindex(:N) + 4) + 3) B' (g0:A->real^N^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_CBOUND_MONO THEN
    MAP_EVERY EXISTS_TAC [`(2 * dimindex(:N) + 4) + 3`; `B:real`] THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "inv" (MP_TAC o SPECL [`min tau1 tau2`; `g0:A->real^N^N`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "con" (MP_TAC o SPECL [`min tau1 tau2`; `g0:A->real^N^N`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g:real->A->real^N^N`; `g':real->A->real^N^N`; `v:real->A->real^N^N`;
                       `v':real->A->real^N^N`; `D:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) && rdt_has_const "real_integral" th &&
    rdt_has_const "pde_rdt_step" th)) THEN
  MAP_EVERY EXISTS_TAC [`g:real->A->real^N^N`; `g':real->A->real^N^N`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_rdt_step" th &&
    not(rdt_has_const "real_integral" th))) THEN
  EXISTS_TAC `g':real->A->real^N^N` THEN ASM_REWRITE_TAC[]);;

