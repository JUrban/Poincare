(* ========================================================================= *)
(* pc_pde_rdt_hi: the Ricci-DeTurck existence, part 7.  Tame energy          *)
(* estimates at every level l (linear in the top norm of the coefficients),  *)
(* tame bounds of the coefficients and of the forcing, and bounds of the     *)
(* frozen-coefficient iterates at every level, uniform in the iteration, on  *)
(* the interval of the ball.                                                 *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_contr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The chart energy and the cut-off commutator with the low jet              *)
(* bound Lam of the unknown as a hypothesis, so that the top norm of the     *)
(* coefficients enters linearly (tame forms of RDT_CHART_ENERGY and          *)
(* RDT_COMM_HS).                                                             *)
(* ------------------------------------------------------------------------- *)

let RDT_CHART_ENERGY_T = prove
 (`!s lam M.
     &0 < lam /\ &0 <= M
     ==> ?C. &0 <= C /\
             !U K (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
              (u:real^N->real^Q) Fo Lam.
               open U /\ compact K /\ K SUBSET U /\
               smooth_map_on U (\x. vectorize(A x)) /\
               (!i. smooth_map_on U (\x. vectorize(B x i))) /\
               smooth_map_on U (\x. vectorize(C0 x)) /\
               smooth_map_on U u /\ smooth_map_on U Fo /\
               (!y. y IN U /\ ~(y IN K) ==> u y = vec 0 /\ Fo y = vec 0) /\
               (!y w. y IN K ==> lam * norm w pow 2 <= w dot (A y ** w)) /\
               (!y. y IN K ==> rdt_cjet (s DIV 2 + 1) A B C0 y <= M) /\
               &0 <= Lam /\ (!y. y IN K ==> pde_jetn (s DIV 2 + 2) u y <= Lam)
               ==> sum (pde_index_lists s (:N))
                     (\l. rdt_int U (\y. &2 * (iterated_partial l u y dot
                                               iterated_partial l
                                                 (\y. pde_lop0 A B C0 u y + Fo y) y)))
                   <= --(lam / &2) * rdt_hs U (s + 1) u +
                      C * (rdt_hs U s u +
                           Lam pow 2 * drop(integral K (\y. lift(rdt_cjet s A B C0 y pow 2))) +
                           rdt_hs U (s - 1) Fo)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow s * &(s + 1))` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN RDT_NN_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:num`; `lam:real`; `M:real`; `c:real`] RDT_ENERGY_ABS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "abs"))) THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the bound of the remainders *)
  SUBGOAL_THEN
   `!l y. l IN pde_index_lists s (:N) /\ y IN K
          ==> norm(iterated_partial l (pde_lop0 A B C0 (u:real^N->real^Q)) y -
                   vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                     (\j. (A:real^N->real^N^N) y$i$j %
                          partial_derivative i (partial_derivative j (iterated_partial l u)) y)))
              <= c * (M * pde_jetn (s + 1) u y + rdt_cjet s A B C0 y * Lam)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `A:real^N->real^N^N`;
                   `B:real^N->num->real^Q^Q`; `C0:real^N->real^Q^Q`; `u:real^N->real^Q`;
                   `y:real^N`] RDT_LOP0_COMM_CJET) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    SUBGOAL_THEN `LENGTH(l:num list) DIV 2 <= s DIV 2` ASSUME_TAC THENL
     [MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `n = LENGTH(l:num list)` THEN
    SUBGOAL_THEN
     `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1)) <= c`
    ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rdt_cjet (n DIV 2 + 1) A B C0 y * pde_jetn (n + 1) (u:real^N->real^Q) y <=
      M * pde_jetn (s + 1) u y /\
      rdt_cjet n (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y *
      pde_jetn (n DIV 2 + 2) u y <= rdt_cjet s A B C0 y * Lam`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[RDT_CJET_POS; PDE_JETN_POS] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rdt_cjet (s DIV 2 + 1)
          (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC RDT_CJET_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC RDT_CJET_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (s DIV 2 + 2) (u:real^N->real^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1))) *
                (M * pde_jetn (s + 1) (u:real^N->real^Q) y +
                 rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                          (C0:real^N->real^Q^Q) y * Lam)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[RDT_CJET_POS; PDE_JETN_POS]];
    ALL_TAC] THEN
  USE_THEN "abs" (MP_TAC o SPECL
   [`U:real^N->bool`; `K:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
    `C0:real^N->real^Q^Q`; `u:real^N->real^Q`; `Fo:real^N->real^Q`;
    `\y. rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y`;
    `Lam:real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RDT_CJET_POS; ETA_AX] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `rdt_cjet (s DIV 2 + 1) (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                           (C0:real^N->real^Q^Q) y` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `rdt_cjet 1 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                           (C0:real^N->real^Q^Q) y` THEN
      REWRITE_TAC[RDT_CJET_A] THEN MATCH_MP_TAC RDT_CJET_MONO THEN ARITH_TAC;
      MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;
let RDT_INTK_SQ_POS = prove
 (`!K (f:real^N->real).
     compact K /\ (\y. lift(f y)) continuous_on K
     ==> &0 <= drop(integral K (\y. lift(f y pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN MATCH_MP_TAC RDT_INTK_INTEGRABLE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_POW]);;

let RDT_TAME_ARITH = prove
 (`!a b m q h l i.
     &0 <= a /\ &0 <= b /\ &0 <= m /\ &0 <= q /\ &0 <= h /\ &0 <= i
     ==> a * (&2 * b * (m * q * h + l pow 2 * i)) <=
         (a * (&2 * b * (m * q + &1))) * (h + l pow 2 * i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= m * q * (l pow 2 * i)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RDT_COMM_HS_T = prove
 (`!s M Ap.
     2 * dimindex(:N) + 4 <= s /\ &0 <= M /\ &0 <= Ap
     ==> ?C. &0 <= C /\
             !U K KW (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
              p W Lam.
               open U /\ compact K /\ compact KW /\ K SUBSET U /\ KW SUBSET U /\
               smooth_map_on U (\x. vectorize(A x)) /\
               (!i. smooth_map_on U (\x. vectorize(B x i))) /\
               smooth_map_on U (\x. vectorize(C0 x)) /\
               smooth_map_on U p /\ smooth_map_on U W /\
               (!y. y IN U /\ ~(y IN K) ==> p y = vec 0) /\
               (!y. y IN U /\ ~(y IN KW) ==> W y = vec 0) /\
               (!y. y IN K ==> pde_jetn (s + 1) p y <= Ap) /\
               (!y. y IN K ==> rdt_cjet (s DIV 2 + 1) A B C0 y <= M) /\
               &0 <= Lam /\ (!y. y IN K ==> pde_jetn (s DIV 2 + 2) W y <= Lam)
               ==> rdt_hs U (s - 1) (pde_mt_comm A B p W) <=
                   C * (rdt_hs U s W +
                        Lam pow 2 * drop(integral K (\y. lift(rdt_cjet s A B C0 y pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Kc = (&(CARD(pde_index_lists s (:N))) * &2 pow s * &(s + 1)) *
                   (&3 * &(dimindex(:N)) pow 2 * norm(vectorize(mat 1:real^Q^Q)) + &1)` THEN
  ABBREV_TAC `c = &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow s * &(s + 1))` THEN
  SUBGOAL_THEN `&0 <= Kc /\ &0 <= c` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kc"; "c"] THEN CONJ_TAC THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists (s - 1) (:N))) *
              (&2 * (c * Kc * Ap) pow 2 *
               (M pow 2 * &(CARD(pde_index_lists s (:N))) + &1))` THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                 `p:real^N->real^1`] RDT_COMM_COEFF_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[RDT_COMM_LOP0_FUN] THEN
  SUBGOAL_THEN
   `smooth_map_on U (pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p)
                              (W:real^N->real^Q))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_LOP0_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U /\ ~(y IN K)
        ==> pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p)
                     (W:real^N->real^Q) y = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN REWRITE_TAC[GSYM RDT_COMM_LOP0] THEN
    MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `U DIFF (K:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rdt_hs U s (W:real^N->real^Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `KW:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the pointwise bound *)
  SUBGOAL_THEN
   `!l y. l IN pde_index_lists (s - 1) (:N) /\ y IN K
          ==> norm(iterated_partial l
                     (pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p)
                               (W:real^N->real^Q)) y) <=
              (c * Kc * Ap) *
              (M * pde_jetn s W y +
               rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                        (C0:real^N->real^Q^Q) y * Lam)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!m. m <= s - 1
          ==> rdt_cjet m (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) y <=
              Kc * Ap * rdt_cjet m (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                   (C0:real^N->real^Q^Q) y`
    ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `A:real^N->real^N^N`;
                     `B:real^N->num->real^Q^Q`; `C0:real^N->real^Q^Q`; `p:real^N->real^1`;
                     `y:real^N`; `Ap:real`] RDT_COMM_CJET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (s + 1) (p:real^N->real^1) y` THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [EXPAND_TAC "Kc" THEN MATCH_MP_TAC RDT_KC_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[RDT_CJET_POS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `\z:real^N. mat 0:real^N^N`;
                   `rdt_cdd (A:real^N->real^N^N) (p:real^N->real^1):real^N->num->real^Q^Q`;
                   `rdt_cee (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (p:real^N->real^1)`;
                   `W:real^N->real^Q`; `y:real^N`] RDT_LOP0_COMM_CJET) THEN
    ASM_REWRITE_TAC[MAT_0_COMPONENT; VECTOR_MUL_LZERO; VSUM_0; VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    ABBREV_TAC `n = LENGTH(l:num list)` THEN
    SUBGOAL_THEN `n DIV 2 + 1 <= s - 1 /\ n DIV 2 + 1 <= s DIV 2 + 1 /\ n <= s - 1 /\
                  n + 1 <= s /\ n DIV 2 + 2 <= s DIV 2 + 2` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `n DIV 2 <= s DIV 2` ASSUME_TAC THENL
       [MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rdt_cjet (n DIV 2 + 1) (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) y *
      pde_jetn (n + 1) (W:real^N->real^Q) y <= (Kc * Ap * M) * pde_jetn s W y /\
      rdt_cjet n (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) y *
      pde_jetn (n DIV 2 + 2) W y <=
      (Kc * Ap * rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                          (C0:real^N->real^Q^Q) y) * Lam`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[RDT_CJET_POS; PDE_JETN_POS] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Kc * Ap * rdt_cjet (n DIV 2 + 1) (A:real^N->real^N^N)
                      (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `rdt_cjet (s DIV 2 + 1) (A:real^N->real^N^N)
                      (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[RDT_CJET_MONO];
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Kc * Ap * rdt_cjet n (A:real^N->real^N^N)
                      (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RDT_CJET_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (s DIV 2 + 2) (W:real^N->real^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1)) <= c`
    ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC];
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1))) *
                ((Kc * Ap * M) * pde_jetn s (W:real^N->real^Q) y +
                 (Kc * Ap * rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                     (C0:real^N->real^Q^Q) y) * Lam)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * ((Kc * Ap * M) * pde_jetn s (W:real^N->real^Q) y +
                     (Kc * Ap * rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                         (C0:real^N->real^Q^Q) y) * Lam)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[PDE_JETN_POS] THEN ASM_REWRITE_TAC[] THEN RDT_NN_TAC THEN
      REWRITE_TAC[RDT_CJET_POS];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `KW:real^N->bool`;
    `pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) (W:real^N->real^Q)`;
    `W:real^N->real^Q`;
    `\y. rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y`;
    `s - 1`; `s:num`; `c * Kc * Ap`; `M:real`; `Lam:real`;
    `drop(integral K (\y. lift(rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                         (C0:real^N->real^Q^Q) y pow 2)))`]
    RDT_HS_FROM_POINTWISE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      RDT_NN_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC RDT_TAME_ARITH THEN ASM_REWRITE_TAC[REAL_POS] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC RDT_INTK_SQ_POS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;


(* The energy of one chart in tame form (RDT_MCHART with the low jet bound Lv). *)

let RDT_MCHART_T = prove
 (`!(K:real^N->bool) KT s lam M Ap.
     compact K /\ compact KT /\ 2 * dimindex(:N) + 4 <= s /\ &0 < lam /\ &0 <= M /\
     &0 <= Ap
     ==> ?C. &0 <= C /\
             !top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) (theta:A->real) O a b
              (k:real->A->real^N^N) h f v0 v t Lv.
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
               (!y. y IN K ==> pde_jetn (s + 1) (\z. lift(phi(chart_inv c z))) y <= Ap) /\
               (!y w. y IN K ==> lam * norm w pow 2 <= w dot (pde_mlaa atlas c k t y ** w)) /\
               (!y. y IN K ==> rdt_cjet (s DIV 2 + 1) (pde_mlaa atlas c k t)
                                        (pde_mlbt atlas c k h t) (pde_mlct atlas c k h t) y
                               <= M) /\
               &0 <= Lv /\
               (!y. y IN K
                    ==> pde_jetn (s DIV 2 + 2)
                          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 (metric_local atlas c (v t) z)) y <= Lv)
               ==> &0 <= drop(integral K (\y. lift(rdt_cjet s (pde_mlaa atlas c k t)
                                                          (pde_mlbt atlas c k h t)
                                                          (pde_mlct atlas c k h t) y pow 2))) /\
                   sum (pde_index_lists s (:N))
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
                   <= C * (rdt_hs (IMAGE (SND c) (FST c)) s
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (phi(chart_inv c z) %% metric_local atlas c (v t) z)) +
                           rdt_hs (IMAGE (SND c) (FST c)) (s - 1)
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (phi(chart_inv c z) %% metric_local atlas c (f t) z)) +
                           rdt_hs (IMAGE (SND c) (FST c)) s
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (theta(chart_inv c z) %% metric_local atlas c (v t) z)) +
                           Lv pow 2 *
                           drop(integral K (\y. lift(rdt_cjet s (pde_mlaa atlas c k t)
                                                            (pde_mlbt atlas c k h t)
                                                            (pde_mlct atlas c k h t) y pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:num`; `lam:real`; `M:real`]
    (INST_TYPE [`:(N,N)finite_prod`,`:Q`] RDT_CHART_ENERGY_T)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CE:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ce"))) THEN
  MP_TAC(ISPECL [`s:num`; `M:real`; `Ap:real`]
    (INST_TYPE [`:(N,N)finite_prod`,`:Q`] RDT_COMM_HS_T)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CM:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cm"))) THEN
  ABBREV_TAC `cB = &(CARD(pde_index_lists (s DIV 2 + 2) (:N))) *
                   (&2 pow (s DIV 2 + 2) * &1 * &((s DIV 2 + 2) + 1) * Ap)` THEN
  SUBGOAL_THEN `&0 <= cB` ASSUME_TAC THENL [EXPAND_TAC "cB" THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `CE * (&3 + &2 * CM + cB pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `cB:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) /\ a < b /\ a <= t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
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
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_mlin_sol]);
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
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_SQ_POS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RDT_CJET_CONT THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
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
   `sum (pde_index_lists s (:N))
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
    sum (pde_index_lists s (:N))
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
  (* the low jets of the two cut-off pieces *)
  SUBGOAL_THEN
   `&0 <= cB * Lv /\
    (!y. y IN K ==> pde_jetn (s DIV 2 + 2) (u:real^N->real^(N,N)finite_prod) y <= cB * Lv) /\
    (!y. y IN K ==> pde_jetn (s DIV 2 + 2) (W:real^N->real^(N,N)finite_prod) y <= Lv)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    (SUBGOAL_THEN `(y:real^N) IN U /\ y IN O` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `(y:real^N) IN K` THEN UNDISCH_TAC `(K:real^N->bool) SUBSET U` THEN
       UNDISCH_TAC `(K:real^N->bool) SUBSET O` THEN SET_TAC[];
       ALL_TAC]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Lv:real`)) (concl th))) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THENL
     [MP_TAC(ISPECL [`\(x:real^1) (v:real^(N,N)finite_prod). drop x % v`; `&1`; `s DIV 2 + 2`;
                     `U:real^N->bool`; `p:real^N->real^1`;
                     `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (c:(A->bool)#(A->real^N))
                                          ((v:real->A->real^N^N) t) z)`;
                     `y:real^N`; `Ap:real`] RDT_JETN_BILINEAR_BOUNDED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[INST_TYPE [`:N`,`:Q`] RDT_BB_E2; REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (s + 1) (p:real^N->real^1) y` THEN CONJ_TAC THENL
         [MATCH_MP_TAC PDE_JETN_MONO THEN MP_TAC(SPEC `s:num` RDT_DIV2) THEN ASM_ARITH_TAC;
          EXPAND_TAC "p" THEN ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(\x. (\(x:real^1) (v:real^(N,N)finite_prod). drop x % v) ((p:real^N->real^1) x)
              ((\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (metric_local atlas (c:(A->bool)#(A->real^N))
                                   ((v:real->A->real^N^N) t) z)) x)) =
        (u:real^N->real^(N,N)finite_prod)`
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["p"; "u"] THEN
        REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; VECTORIZE_CMUL];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD(pde_index_lists (s DIV 2 + 2) (:N))) *
                  (&2 pow (s DIV 2 + 2) * &1 * &((s DIV 2 + 2) + 1) * Ap) * Lv` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RDT_NN_TAC;
        EXPAND_TAC "cB" THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]];
      SUBGOAL_THEN
       `pde_jetn (s DIV 2 + 2) (W:real^N->real^(N,N)finite_prod) y =
        pde_jetn (s DIV 2 + 2)
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t) z)) y`
      SUBST1_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "W" THEN
      ASM_SIMP_TAC[MATRIX_CMUL_LID]];
    ALL_TAC] THEN
  (* the chart energy *)
  USE_THEN "ce" (MP_TAC o SPECL
   [`U:real^N->bool`; `K:real^N->bool`;
    `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t`;
    `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `u:real^N->real^(N,N)finite_prod`;
    `\z. (pF:real^N->real^(N,N)finite_prod) z -
         pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas c k (h:A->real^N^N) t)
                     (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) z`;
    `cB * Lv:real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
      ASM_SIMP_TAC[VECTOR_SUB_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `pF:real^N->real^(N,N)finite_prod`;
                 `pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
                              (pde_mlbt atlas c k (h:A->real^N^N) t)
                              (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod)`;
                 `s - 1`] RDT_HS_SUB2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "cm" (MP_TAC o SPECL
   [`U:real^N->bool`; `K:real^N->bool`; `KT:real^N->bool`;
    `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t`;
    `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `p:real^N->real^1`; `W:real^N->real^(N,N)finite_prod`; `Lv:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= rdt_hs U (s + 1) (u:real^N->real^(N,N)finite_prod) /\
    &0 <= rdt_hs U s u /\ &0 <= rdt_hs U (s - 1) (pF:real^N->real^(N,N)finite_prod) /\
    &0 <= rdt_hs U s (W:real^N->real^(N,N)finite_prod)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC RDT_HS_POS THENL
     [EXISTS_TAC `K:real^N->bool`; EXISTS_TAC `K:real^N->bool`; EXISTS_TAC `K:real^N->bool`;
      EXISTS_TAC `KT:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= drop(integral K (\y. lift(rdt_cjet s
            (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
            (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t) y pow 2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_INTK_SQ_POS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
  ABBREV_TAC `H1 = rdt_hs U (s + 1) (u:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `H0 = rdt_hs U s (u:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `HF = rdt_hs U (s - 1) (pF:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `HW = rdt_hs U s (W:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `HC = rdt_hs U (s - 1)
                    (pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                           (k:real->A->real^N^N) t)
                                 (pde_mlbt atlas c k (h:A->real^N^N) t)
                                 (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod))` THEN
  ABBREV_TAC `HO = rdt_hs U (s - 1)
                    (\z. (pF:real^N->real^(N,N)finite_prod) z -
                         pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                               (k:real->A->real^N^N) t)
                                     (pde_mlbt atlas c k (h:A->real^N^N) t)
                                     (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) z)` THEN
  ABBREV_TAC `IQ = drop(integral K (\y. lift(rdt_cjet s
            (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
            (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t) y pow 2)))` THEN
  SUBGOAL_THEN `&0 <= Lv pow 2 * IQ` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `LQ = Lv pow 2 * IQ` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `CE * HO <= CE * (&2 * HF + &2 * (CM * (HW + LQ)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`HO <= &2 * HF + &2 * HC`; `HC <= CM * (HW + LQ)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= lam / &2 * H1 /\ &0 <= CE * H0 /\ &0 <= CE * HF /\ &0 <= CE * HW /\
    &0 <= CE * LQ /\ &0 <= CE * CM * H0 /\ &0 <= CE * CM * HF /\ &0 <= CE * CM * HW /\
    &0 <= CE * CM * LQ /\ &0 <= CE * cB pow 2 * H0 /\ &0 <= CE * cB pow 2 * HF /\
    &0 <= CE * cB pow 2 * HW /\ &0 <= CE * cB pow 2 * LQ`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN RDT_NN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `--(lam / &2) * H1 + CE * (H0 + cB pow 2 * LQ + HO)` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The energy at level s on the manifold in tame form: the top               *)
(* norm of the coefficients enters linearly, with the factor Lv^2 (Lv the   *)
(* low jet bound of the solution in the charts).                            *)
(* ------------------------------------------------------------------------- *)

let RDT_MENERGY_T = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s lam M.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ &0 < lam /\ &0 <= M
     ==> ?C. &0 <= C /\
             !a b k h f v0 v t Lv.
               riemannian_metric atlas h /\
               (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
               pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b f /\
               pde_mlin_sol (top,atlas) a b k h f v0 v /\ a < t /\ t < b /\
               (!i y w. i < n0 /\ y IN ks i
                        ==> lam * norm w pow 2 <= w dot (pde_mlaa atlas (cs i) k t y ** w)) /\
               (!i y. i < n0 /\ y IN ks i
                      ==> rdt_cjet (s DIV 2 + 1) (pde_mlaa atlas (cs i) k t)
                                   (pde_mlbt atlas (cs i) k h t) (pde_mlct atlas (cs i) k h t) y
                          <= M) /\
               &0 <= Lv /\
               (!i y. i < n0 /\ y IN ks i
                      ==> pde_jetn (s DIV 2 + 2)
                            (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                   (metric_local atlas (cs i) (v t) z)) y <= Lv)
               ==> ?D. ((\r. pde_mnorm2 atlas n0 cs psi s (v r)) has_real_derivative D)
                       (atreal t) /\
                       D <= C * (pde_mnorm2 atlas n0 cs psi s (v t) +
                                 pde_mnorm2 atlas n0 cs psi (s - 1) (f t) +
                                 Lv pow 2 *
                                 sum {i | i < n0}
                                   (\i. drop(integral (ks i)
                                     (\y. lift(rdt_cjet s (pde_mlaa atlas (cs i) k t)
                                                     (pde_mlbt atlas (cs i) k h t)
                                                     (pde_mlct atlas (cs i) k h t) y pow 2)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `s + 1`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
    (GEN `i:num` (ISPECL [`(ks:num->real^N->bool) i`; `(KT:num->real^N->bool) i`; `s:num`;
                          `lam:real`; `M:real`; `(AP:num->real) i`] RDT_MCHART_T))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:num->real` (LABEL_TAC "cc")) THEN
  SUBGOAL_THEN `!i. i < n0 ==> &0 <= (CC:num->real) i /\ &0 <= (DD:num->real) i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "cc" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `CS = sum {i | i < n0} (CC:num->real)` THEN
  ABBREV_TAC `DS = sum {i | i < n0} (DD:num->real)` THEN
  SUBGOAL_THEN `&0 <= CS /\ &0 <= DS` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["CS"; "DS"] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n0 ==> (CC:num->real) i <= CS /\ (DD:num->real) i <= DS`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["CS"; "DS"] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUM_SING] (ISPECL [`{i:num}`; `{i:num | i < n0}`]
      SUM_SUBSET_SIMPLE)) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_DIFF; IN_ELIM_THM; SING_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `CS * (&1 + &n0 * DS)` THEN CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N) /\
                pde_tensor_smooth atlas ((v:real->A->real^N^N) t) /\
                pde_tensor_smooth atlas ((f:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N)` ASSUME_TAC THENL
     [UNDISCH_TAC `pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h f v0
                     (v:real->A->real^N^N)` THEN SIMP_TAC[pde_mlin_sol];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `v:real->A->real^N^N`; `a:real`; `b:real`; `s:num`] PDM_MNORM2_TFAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `&0 <= pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t) /\
    &0 <= pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n0 ==> &0 <= drop(integral ((ks:num->real^N->bool) i)
                   (\y. lift(rdt_cjet s
                     (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas (cs i) k (h:A->real^N^N) t)
                     (pde_mlct atlas (cs i) k h t) y pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cc" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`; `(TH:num->A->real) i`;
      `(OO:num->real^N->bool) i`; `a:real`; `b:real`; `k:real->A->real^N^N`;
      `h:A->real^N^N`; `f:real->A->real^N^N`; `v0:A->real^N^N`; `v:real->A->real^N^N`;
      `t:real`; `Lv:real`] o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {i | i < n0}
      (\i. CS * (rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) +
                 rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) (s - 1)
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (psi i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((f:real->A->real^N^N) t) z)) +
                 DS * pde_mnorm2 atlas n0 cs psi s (v t) +
                 Lv pow 2 * drop(integral ((ks:num->real^N->bool) i)
                   (\y. lift(rdt_cjet s
                     (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas (cs i) k (h:A->real^N^N) t)
                     (pde_mlct atlas (cs i) k h t) y pow 2)))))` THEN
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
      `t:real`; `Lv:real`] o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(v:real->A->real^N^N) t` o check (fun th ->
      can (find_term ((=) `pde_tensor_smooth:(((A->bool)#(A->real^N))->bool)->(A->real^N^N)->bool`))
          (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((psi:num->A->real) i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) /\
      &0 <= rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) (s - 1)
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (psi i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) ((f:real->A->real^N^N) t) z))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[rdt_hs; rdt_int] THEN
      CONJ_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                     `(ks:num->real^N->bool) i`] PDE_ME_CNORM_POS) THEN
      ASM_REWRITE_TAC[pde_me_cnorm; rdt_hs; rdt_int] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(CC:num->real) i <= CS /\ (DD:num->real) i <= DS /\
                  &0 <= CC i /\ &0 <= DD i` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Lv pow 2 * drop(integral ((ks:num->real^N->bool) i)
                   (\y. lift(rdt_cjet s
                     (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas (cs i) k (h:A->real^N^N) t)
                     (pde_mlct atlas (cs i) k h t) y pow 2)))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ABBREV_TAC `E = pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t)` THEN
    ABBREV_TAC `LQ = Lv pow 2 * drop(integral ((ks:num->real^N->bool) i)
                   (\y. lift(rdt_cjet s
                     (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas (cs i) k (h:A->real^N^N) t)
                     (pde_mlct atlas (cs i) k h t) y pow 2)))` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(CC:num->real) i *
                (rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) +
                 rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) (s - 1)
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (psi i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((f:real->A->real^N^N) t) z)) +
                 DS * E + LQ)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `c <= d ==> a + b + c + e <= a + b + d + e`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(DD:num->real) i * E` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t) =
    sum {i | i < n0}
      (\i. rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) (v t) z))) /\
    pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) t) =
    sum {i | i < n0}
      (\i. rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) (s - 1)
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) (f t) z)))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [REWRITE_TAC[pde_mnorm2; rdt_hs; rdt_int]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum {i | i < n0} (\i. drop(integral ((ks:num->real^N->bool) i)
                   (\y. lift(rdt_cjet s
                     (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas (cs i) k (h:A->real^N^N) t)
                     (pde_mlct atlas (cs i) k h t) y pow 2))))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  SIMP_TAC[SUM_LMUL; SUM_ADD; FINITE_NUMSEG_LT; SUM_CONST; CARD_NUMSEG_LT] THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM(fun th1 -> POP_ASSUM(fun th2 -> REWRITE_TAC[GSYM th1; GSYM th2])) THEN
  ABBREV_TAC `IQS = sum {i | i < n0} (\i. drop(integral ((ks:num->real^N->bool) i)
                   (\y. lift(rdt_cjet s
                     (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas (cs i) k (h:A->real^N^N) t)
                     (pde_mlct atlas (cs i) k h t) y pow 2))))` THEN DISCH_TAC THEN
  ABBREV_TAC `E = pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t)` THEN
  ABBREV_TAC `EF = pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) t)` THEN
  SUBGOAL_THEN `&0 <= CS * &n0 * DS * EF /\ &0 <= CS * &n0 * DS * Lv pow 2 * IQS`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tame bounds of the coefficients and of the forcing at level               *)
(* l: the squared level-l jets of the coefficients, integrated over the      *)
(* pieces, and the level-(l-1) norm of P_h(g) - tr_g Hess_h g are bounded by *)
(* C (1 + |g|_l^2), with C depending only on pointwise bounds of low jets.   *)
(* ------------------------------------------------------------------------- *)

let RDT_MLCOEF_EQ = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c (k:real->A->real^N^N) h t.
     pde_mlaa atlas c k t = (\y. transp(matrix_inv(metric_local atlas c (k t) y))) /\
     pde_mlbt atlas c k h t =
       (\y i. pde_mlbb (metric_local atlas c (k t)) (metric_local atlas c h) y i) /\
     pde_mlct atlas c k h t =
       (\y. pde_mlcc (metric_local atlas c (k t)) (metric_local atlas c h) y)`,
  REWRITE_TAC[FUN_EQ_THM; pde_mlaa; pde_mlbt; pde_mlct]);;

let RDT_COEF_INT_T = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi l K1 MG BH LH.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\ &0 <= MG
     ==> ?CQ. &0 <= CQ /\
           !h g. riemannian_metric atlas h /\ riemannian_metric atlas g /\
                 (!i y. i < n0 /\ y IN ks i
                        ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                                   (metric_local atlas (cs i) g y)) <= K1 /\
                            (!w. norm w pow 2 <= K1 * (w dot (metric_local atlas (cs i) g y ** w))) /\
                            pde_jetn (l DIV 2 + 1)
                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               metric_local atlas (cs i) g) y <= MG /\
                            pde_jetn (l + 3)
                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               metric_local atlas (cs i) h) y <= BH /\
                            norm((vectorize:real^N^N->real^(N,N)finite_prod)
                                   (matrix_inv(metric_local atlas (cs i) h y))) <= LH)
                 ==> sum {i | i < n0}
                       (\i. drop(integral (ks i)
                              (\y. lift(rdt_cjet l
                                  (\y. transp(matrix_inv(metric_local atlas (cs i) g y)))
                                  (\y c. pde_mlbb (metric_local atlas (cs i) g)
                                                  (metric_local atlas (cs i) h) y c)
                                  (\y. pde_mlcc (metric_local atlas (cs i) g)
                                                (metric_local atlas (cs i) h) y) y pow 2))))
                     <= CQ * (&1 + pde_mnorm2 atlas n0 cs psi l g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `l:num`; `l:num`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  MP_TAC(SPECL [`l:num`; `K1:real`; `MG:real`; `BH:real`; `LH:real`] RDT_COEF_CJET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c2"))) THEN
  SUBGOAL_THEN
   `!i. i < n0
        ==> &0 <= &2 * C2 pow 2 *
                  (drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) +
                   &(CARD(pde_index_lists l (:N))) * (DD:num->real) i) /\
            &0 <= (DD:num->real) i /\
            &0 <= drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPEC `(ks:num->real^N->bool) i` RDT_INTK_ONE_POS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN RDT_NN_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `sum {i | i < n0}
                (\i. &2 * C2 pow 2 *
                     (drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) +
                      &(CARD(pde_index_lists l (:N))) * (DD:num->real) i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N^N`; `g:A->real^N^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tensor_smooth atlas (g:A->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pde_mnorm2 atlas n0 cs psi l (g:A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `U = IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) /\
    metric_field U (metric_local atlas (cs i) (h:A->real^N^N))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(TH:num->A->real) i`;
                 `(KT:num->real^N->bool) i`; `g:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                   (g:A->real^N^N))` THEN
    SIMP_TAC[metric_field];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                     (g:A->real^N^N)`;
                 `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)`]
    RDT_COEF_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * C2 pow 2 *
              (drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) +
               &(CARD(pde_index_lists l (:N))) *
               rdt_hs U l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 ((TH:num->A->real) i
                                    (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                                  metric_local atlas (cs i) (g:A->real^N^N) z)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_TOPJET THEN EXISTS_TAC `(KT:num->real^N->bool) i` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^N`] o check (fun th ->
        is_forall(concl th) && rdt_has_const "matrix_inv" th &&
        not(rdt_has_const "rdt_cjet" th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
      REWRITE_TAC[RDT_CJET_POS] THEN
      SUBGOAL_THEN
       `pde_jetn l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((TH:num->A->real) i
                             (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                           metric_local atlas (cs i) (g:A->real^N^N) z)) y =
        pde_jetn l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas (cs i) g) y`
      SUBST1_TAC THENL
       [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `(OO:num->real^N->bool) i` THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[o_THM; MATRIX_CMUL_LID];
        ALL_TAC] THEN
      USE_THEN "c2" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  SUBGOAL_THEN
   `rdt_hs U l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((TH:num->A->real) i
                         (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                       metric_local atlas (cs i) (g:A->real^N^N) z)) <=
    (DD:num->real) i * pde_mnorm2 atlas n0 cs psi l g`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `pde_tensor_smooth:(((A->bool)#(A->real^N))->bool)->(A->real^N^N)->bool`))
          (concl th) && is_forall (concl th) &&
      can (find_term ((=) `rdt_hs:(real^N->bool)->num->(real^N->real^(N,N)finite_prod)->real`))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) /\
                &0 <= (DD:num->real) i`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `E = pde_mnorm2 atlas n0 cs psi l (g:A->real^N^N)` THEN
  ABBREV_TAC `H = rdt_hs U l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((TH:num->A->real) i
                         (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                       metric_local atlas (cs i) (g:A->real^N^N) z))` THEN
  ABBREV_TAC `I1 = drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1)))` THEN
  ABBREV_TAC `CL = &(CARD(pde_index_lists l (:N)))` THEN
  SUBGOAL_THEN `&0 <= CL` ASSUME_TAC THENL
   [EXPAND_TAC "CL" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `CL * H <= CL * ((DD:num->real) i * E) /\ &0 <= CL * (DD:num->real) i * E /\
                &0 <= I1 * E /\ &0 <= CL * (DD:num->real) i`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tame bound of the forcing P_h(g) - tr_g Hess_h g at                   *)
(* level l - 1 by C (1 + |g|_l^2) (RDT_BALL_FORCING with the ball replaced   *)
(* by pointwise bounds of low jets).                                         *)
(* ------------------------------------------------------------------------- *)

let RDT_FORCING_T = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi l K1 MG BH LH.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     1 <= l /\ &0 <= MG
     ==> ?CF. &0 <= CF /\
           !h g. riemannian_metric atlas h /\ riemannian_metric atlas g /\
                 (!i y. i < n0 /\ y IN ks i
                        ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                                   (metric_local atlas (cs i) g y)) <= K1 /\
                            (!w. norm w pow 2 <= K1 * (w dot (metric_local atlas (cs i) g y ** w))) /\
                            pde_jetn ((l - 1) DIV 2 + 2)
                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               metric_local atlas (cs i) g) y <= MG /\
                            pde_jetn ((l - 1) + 3)
                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               metric_local atlas (cs i) h) y <= BH /\
                            norm((vectorize:real^N^N->real^(N,N)finite_prod)
                                   (matrix_inv(metric_local atlas (cs i) h y))) <= LH)
                 ==> pde_mnorm2 atlas n0 cs psi (l - 1)
                       (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x)
                     <= CF * (&1 + pde_mnorm2 atlas n0 cs psi l g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `l:num`; `l - 1`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  SUBGOAL_THEN `(l - 1) + 1 = l` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l - 1`; `K1:real`; `MG:real`; `BH:real`; `LH:real`] RDT_REM_JETN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cr"))) THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> &0 <= (AP:num->real) i /\ &0 <= (DD:num->real) i /\
                   &0 <= drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_ONE] THEN MATCH_MP_TAC RDT_INTK_ONE_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `APS = sum {i | i < n0} (AP:num->real)` THEN
  ABBREV_TAC `DS = sum {i | i < n0} (DD:num->real)` THEN
  ABBREV_TAC `IS = sum {i | i < n0}
                     (\i. drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2))))` THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> (AP:num->real) i <= APS /\ (DD:num->real) i <= DS /\
                   drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2))) <= IS`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["APS"; "DS"; "IS"] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`AP:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM);
      MP_TAC(ISPECL [`DD:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM);
      MP_TAC(ISPECL [`\i. drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))`;
                     `n0:num`; `i:num`] RDT_TERM_LE_SUM)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= APS /\ &0 <= DS /\ &0 <= IS` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["APS"; "DS"; "IS"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `c1 = &(CARD(pde_index_lists (l - 1) (:N))) *
                   (&2 pow (l - 1) * &1 * &l * APS) * CR` THEN
  SUBGOAL_THEN `&0 <= c1` ASSUME_TAC THENL [EXPAND_TAC "c1" THEN RDT_NN_TAC; ALL_TAC] THEN
  ABBREV_TAC `F0 = &(CARD(pde_index_lists (l - 1) (:N))) * &2 * c1 pow 2` THEN
  SUBGOAL_THEN `&0 <= F0` ASSUME_TAC THENL [EXPAND_TAC "F0" THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `&n0 * F0 * (&(CARD(pde_index_lists l (:N))) * DS + IS)` THEN CONJ_TAC THENL
   [RDT_NN_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N^N`; `g:A->real^N^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tensor_smooth atlas (g:A->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pde_mnorm2 atlas n0 cs psi l (g:A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E = pde_mnorm2 atlas n0 cs psi l (g:A->real^N^N)` THEN
  ABBREV_TAC `FC = F0 * (&(CARD(pde_index_lists l (:N))) * (DS * E) + IS)` THEN
  SUBGOAL_THEN `&n0 * FC <= (&n0 * F0 * (&(CARD(pde_index_lists l (:N))) * DS + IS)) * (&1 + E)`
  MP_TAC THENL
   [EXPAND_TAC "FC" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= &(CARD(pde_index_lists l (:N))) * DS * E /\ &0 <= IS * E /\
                  &0 <= &(CARD(pde_index_lists l (:N))) * DS`
    MP_TAC THENL [REPEAT CONJ_TAC THEN RDT_NN_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= z ==> x <= z`) THEN
  REWRITE_TAC[pde_mnorm2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {i | i < n0} (\i:num. FC)` THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ABBREV_TAC `U = IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  ABBREV_TAC `Fg = \x. pde_rdt_rhs atlas (h:A->real^N^N) g x - pde_trhess atlas g h g x` THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `h:A->real^N^N`; `g:A->real^N^N`]
    RDT_FORCING_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) /\
    metric_field U (metric_local atlas (cs i) (h:A->real^N^N))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(TH:num->A->real) i`;
                 `(KT:num->real^N->bool) i`; `g:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                   (g:A->real^N^N))` THEN
    SIMP_TAC[metric_field];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`; `Fg:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[o_DEF]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `rdt_hs U (l - 1)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
              metric_local atlas (cs i) (Fg:A->real^N^N) z)) <= FC`
  MP_TAC THENL [ALL_TAC; REWRITE_TAC[rdt_hs; rdt_int]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&(CARD(pde_index_lists (l - 1) (:N))) *
    (&2 * c1 pow 2 *
     (&1 pow 2 * &(CARD(pde_index_lists l (:N))) *
      rdt_hs U l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                         metric_local atlas (cs i) (g:A->real^N^N) z)) +
      &1 pow 2 * drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `(DD:num->real) i <= DS /\
                  drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2))) <= IS`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `rdt_hs U l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                         metric_local atlas (cs i) (g:A->real^N^N) z)) <= (DD:num->real) i * E`
    ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `pde_tensor_smooth:(((A->bool)#(A->real^N))->bool)->(A->real^N^N)->bool`))
            (concl th) && is_forall (concl th) &&
        can (find_term ((=) `rdt_hs:(real^N->bool)->num->(real^N->real^(N,N)finite_prod)->real`))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `HW = rdt_hs U l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                         metric_local atlas (cs i) (g:A->real^N^N) z))` THEN
    ABBREV_TAC `I1 = drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))` THEN
    EXPAND_TAC "FC" THEN EXPAND_TAC "F0" THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(DD:num->real) i * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC RDT_HS_FROM_POINTWISE THEN
  MAP_EVERY EXISTS_TAC [`(ks:num->real^N->bool) i`; `(KT:num->real^N->bool) i`;
                        `\y:real^N. &1`] THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; REAL_LE_REFL; REAL_POS] THEN
  MAP_EVERY X_GEN_TAC [`l':num list`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^N`] o check (fun th ->
    is_forall(concl th) && rdt_has_const "matrix_inv" th &&
    not(rdt_has_const "rdt_cjet" th) && not(rdt_has_const "rdt_kf" th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn (l - 1)
                (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                        metric_local atlas (cs i) (Fg:A->real^N^N) z)) y` THEN
  CONJ_TAC THENL [MATCH_MP_TAC PDE_ME_TERM_LE_JETN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(x:real^1) (v:real^(N,N)finite_prod). drop x % v`; `&1`; `l - 1`;
                 `U:real^N->bool`;
                 `\z. lift((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z))`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (Fg:A->real^N^N) z)`;
                 `y:real^N`; `(AP:num->real) i`] RDT_JETN_BILINEAR_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INST_TYPE [`:N`,`:Q`] RDT_BB_E2; REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; GSYM VECTORIZE_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN
   `pde_jetn (l - 1)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (Fg:A->real^N^N) z)) y =
    pde_jetn (l - 1)
      (\z. rdt_psi (rdt_kf (metric_local atlas (cs i) (g:A->real^N^N))
                           (metric_local atlas (cs i) (h:A->real^N^N)) z)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                       metric_local atlas (cs i) (g:A->real^N^N) z)) y =
    pde_jetn l ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) g) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `(OO:num->real^N->bool) i` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM; MATRIX_CMUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn (l - 1)
      (\z. rdt_psi (rdt_kf (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                         (g:A->real^N^N))
                           (metric_local atlas (cs i) (h:A->real^N^N)) z)) y <=
    CR * (&1 + pde_jetn l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                           metric_local atlas (cs i) g) y)`
  ASSUME_TAC THENL
   [USE_THEN "cr" (MP_TAC o SPECL
     [`U:real^N->bool`;
      `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)`;
      `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)`;
      `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `J = pde_jetn l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                              metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                           (g:A->real^N^N)) y` THEN
  SUBGOAL_THEN `&0 <= J /\ &0 <= CR /\ (AP:num->real) i <= APS /\ &0 <= AP i` STRIP_ASSUME_TAC
  THENL [EXPAND_TAC "J" THEN ASM_SIMP_TAC[PDE_JETN_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "c1" THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(pde_index_lists (l - 1) (:N))) *
              (&2 pow (l - 1) * &1 * &l * (AP:num->real) i) *
              (CR * (&1 + J))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RDT_NN_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 * J + &1 * &1 = &1 + J`; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Picard iteration of integral inequalities.  If                            *)
(*   X_(k+1)(t) <= A + C int_a^t X_k,  X_0 <= A0,                            *)
(* then X_k(t) <= (A + A0) exp(C (t - a)) for every k; with Gronwall, a      *)
(* sequence with X_(k+1)' <= C X_(k+1) + C1 (1 + X_k) and X_(k+1)(a) = X0 is *)
(* bounded on [a,b) uniformly in k.                                          *)
(* ------------------------------------------------------------------------- *)

let RDT_EXP_SHIFT_DERIV = prove
 (`!C a r. ((\r. exp(C * (r - a))) has_real_derivative (C * exp(C * (r - a)))) (atreal r)`,
  REPEAT GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

let RDT_EXP_SHIFT_CONT = prove
 (`!C a s. (\r. exp(C * (r - a))) real_continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\r. exp(C * (r - a))) = exp o (\r. C * (r - a))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID;
           REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_EXP]);;

let RDT_EXP_INT = prove
 (`!C a t. a <= t
           ==> C * real_integral (real_interval[a,t]) (\r. exp(C * (r - a))) =
               exp(C * (t - a)) - &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\r. exp(C * (r - a))) real_integrable_on real_interval[a,t]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[RDT_EXP_SHIFT_CONT]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(BETA_RULE(MATCH_MP REAL_INTEGRAL_LMUL th))]) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`\r. exp(C * (r - a))`; `\r. C * exp(C * (r - a))`; `a:real`; `t:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REWRITE_TAC[RDT_EXP_SHIFT_DERIV]);;

let RDT_PICARD = prove
 (`!(X:num->real->real) A A0 C a b.
     &0 <= A /\ &0 <= A0 /\ &0 <= C /\
     (!k t. a <= t /\ t < b ==> (X k) real_integrable_on real_interval[a,t]) /\
     (!t. a <= t /\ t < b ==> X 0 t <= A0) /\
     (!k t. a <= t /\ t < b
            ==> X (SUC k) t <= A + C * real_integral (real_interval[a,t]) (X k))
     ==> !k t. a <= t /\ t < b ==> X k t <= (A + A0) * exp(C * (t - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. a <= t ==> &1 <= exp(C * (t - a))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A0:real` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(A + A0) * &1` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\r. exp(C * (r - a))) real_integrable_on real_interval[a,t]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[RDT_EXP_SHIFT_CONT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `A + C * real_integral (real_interval[a,t]) (\r. (A + A0) * exp(C * (r - a)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `A + C * real_integral (real_interval[a,t]) ((X:num->real->real) k)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && rdt_has_const "exp" th &&
        can (find_term ((=) `k:num`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,t]) (\r. (A + A0) * exp(C * (r - a))) =
    (A + A0) * real_integral (real_interval[a,t]) (\r. exp(C * (r - a)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `a:real`; `t:real`] RDT_EXP_INT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Ie = real_integral (real_interval[a,t]) (\r. exp(C * (r - a)))` THEN
  ABBREV_TAC `e = exp(C * (t - a))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `C * ((A + A0) * Ie) = (A + A0) * (C * Ie)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RDT_PICARD_ODE = prove
 (`!(X:num->real->real) D X0 A0 C C1 a b.
     &0 <= X0 /\ &0 <= A0 /\ &0 <= C /\ &0 <= C1 /\ a < b /\
     (!k Tm. a <= Tm /\ Tm < b ==> (X k) real_continuous_on real_interval[a,Tm]) /\
     (!k t. a <= t /\ t < b ==> &0 <= X k t) /\
     (!t. a <= t /\ t < b ==> X 0 t <= A0) /\
     (!k. X (SUC k) a = X0) /\
     (!k t. a < t /\ t < b
            ==> (X (SUC k) has_real_derivative D k t) (atreal t) /\
                D k t <= C * X (SUC k) t + C1 * (&1 + X k t))
     ==> ?M. !k t. a <= t /\ t < b ==> X k t <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `E = exp(C * (b - a))` THEN
  SUBGOAL_THEN `&1 <= E /\ !t. a <= t /\ t <= b ==> exp(C * (t - a)) <= E` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "E" THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A = X0 + E * (C * X0 + C1) * (b - a)` THEN
  ABBREV_TAC `C2 = E * C1` THEN
  SUBGOAL_THEN `&0 <= A /\ &0 <= C2 /\ X0 <= A` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "C2"] THEN
    SUBGOAL_THEN `&0 <= E * (C * X0 + C1) * (b - a)` MP_TAC THENL
     [RDT_NN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= E * C1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k t. a <= t /\ t < b ==> (X:num->real->real) k real_integrable_on real_interval[a,t]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:num->real->real`; `A:real`; `A0:real`; `C2:real`; `a:real`; `b:real`]
    RDT_PICARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= real_integral (real_interval[a,t]) ((X:num->real->real) k)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_SIMP_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `t = a:real` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= C2 * real_integral (real_interval[a,a]) ((X:num->real->real) k)`
      MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `a < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`\r. (X:num->real->real) (SUC k) r - X0`; `\r:real. &0`;
                   `\r. C * X0 + C1 * (&1 + (X:num->real->real) k r)`;
                   `(D:num->real->real) k`; `a:real`; `t:real`; `&0`; `C:real`]
      RDT_GRONWALL_DISS) THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_NEG_0; REAL_ADD_LID] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL; REAL_SUB_REFL] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; ETA_AX] THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `&0 <= (X:num->real->real) k r` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= C * X0` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN `&0 <= C1 * (&1 + (X:num->real->real) k r)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `r:real`] o check (fun th ->
          is_forall(concl th) && rdt_has_const "has_real_derivative" th)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_SUB_RZERO] THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
          ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; ETA_AX];
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_integral (real_interval[a,t]) (\r. C * X0 + C1 * (&1 + (X:num->real->real) k r)) =
      (C * X0 + C1) * (t - a) + C1 * real_integral (real_interval[a,t]) (X k)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `(\r. C * X0 + C1 * (&1 + (X:num->real->real) k r)) =
                    (\r. (C * X0 + C1) + C1 * X k r)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(X:num->real->real) k real_integrable_on real_interval[a,t]` ASSUME_TAC
      THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_ADD o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE; REAL_INTEGRAL_LMUL; ETA_AX];
      ALL_TAC] THEN
    ABBREV_TAC `Ik = real_integral (real_interval[a,t]) ((X:num->real->real) k)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `exp(C * (t - a)) <= E /\ &0 <= exp(C * (t - a))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                      REWRITE_TAC[REAL_EXP_POS_LE]];
      ALL_TAC] THEN
    ABBREV_TAC `et = exp(C * (t - a))` THEN
    SUBGOAL_THEN `&0 <= (C * X0 + C1) * (t - a) + C1 * Ik /\
                  (C * X0 + C1) * (t - a) <= (C * X0 + C1) * (b - a)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL]; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `et * ((C * X0 + C1) * (t - a) + C1 * Ik) <=
                  E * ((C * X0 + C1) * (b - a) + C1 * Ik)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["A"; "C2"] THEN
    UNDISCH_TAC `(X:num->real->real) (SUC k) t - X0 <= et * ((C * X0 + C1) * (t - a) + C1 * Ik)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(A + A0) * exp(C2 * (b - a))` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(A + A0) * exp(C2 * (t - a))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One level up.  If the frozen-coefficient iterates stay in                 *)
(* the ball and are bounded at level l >= s0 uniformly in the iteration,     *)
(* they are bounded at level l + 1 on the same interval (tame energy,        *)
(* Sobolev for the low jets, RDT_PICARD_ODE).                                *)
(* ------------------------------------------------------------------------- *)

let RDT_BG_JETS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks (h:A->real^N^N) n.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     riemannian_metric atlas h
     ==> ?BH. &0 <= BH /\
              !i y. i < n0 /\ y IN ks i
                    ==> pde_jetn n ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                    metric_local atlas (cs i) h) y <= BH`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. ?C. i < n0
            ==> &0 <= C /\
                !y. y IN (ks:num->real^N->bool) i
                    ==> pde_jetn n ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                                 (h:A->real^N^N)) y <= C`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                   (metric_local atlas (cs i) (h:A->real^N^N))`
    MP_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (h:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(cs:num->(A->bool)#(A->real^N)) i`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
    MATCH_MP_TAC RDT_JETS_BOUNDED_COMPACT THEN
    EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `C:num->real`) THEN
  EXISTS_TAC `sum {i | i < n0} (C:num->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C:num->real) i` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC RDT_TERM_LE_SUM THEN ASM_SIMP_TAC[]]);;

let RDT_LEVEL_ARITH = prove
 (`!l. 2 * dimindex(:N) + 4 <= l
       ==> (l + 1) DIV 2 + 1 <= l - dimindex(:N) /\
           ((l + 1) DIV 2 + 1) DIV 2 + 1 <= l - dimindex(:N) /\
           (l + 1) DIV 2 + 2 <= l - dimindex(:N) /\
           l DIV 2 + 2 <= l - dimindex(:N) /\
           ((l + 1) DIV 2 + 1) + 3 <= l + 4 /\
           (l + 1) - 1 = l /\ 1 <= l + 1 /\ l + 3 <= l + 4 /\
           2 * dimindex(:N) + 4 <= l + 1 /\ dimindex(:N) <= l`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `l:num` RDT_DIV2) THEN MP_TAC(SPEC `l + 1` RDT_DIV2) THEN
  MP_TAC(SPEC `(l + 1) DIV 2 + 1` RDT_DIV2) THEN ASM_ARITH_TAC);;

let RDT_ITER_LEVEL_STEP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s0 B K a tau
    (g0:A->real^N^N) (g:num->real->A->real^N^N) l M.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s0 /\ s0 <= l /\ &0 <= B /\ &0 < K /\ &0 < tau /\
     riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks (s0 + 3) B g0 /\
     (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s0 K a tau g0 (g k)) /\
     (!k. pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k))) /\
     g 0 = (\t. g0) /\
     (!k t. a <= t /\ t < a + tau ==> pde_mnorm2 atlas n0 cs psi l (g k t) <= M)
     ==> ?M'. !k t. a <= t /\ t < a + tau
                    ==> pde_mnorm2 atlas n0 cs psi (l + 1) (g k t) <= M'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 * dimindex(:N) + 4 <= l` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RDT_LEVEL_ARITH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  (* facts from the ball *)
  SUBGOAL_THEN
   `!k t. a <= t /\ t < a + tau
          ==> riemannian_metric atlas ((g:num->real->A->real^N^N) k t) /\
              pde_cbound atlas n0 cs ks 0 K (g k t) /\
              pde_tensor_smooth atlas (g k t) /\
              &0 <= pde_mnorm2 atlas n0 cs psi (l + 1) (g k t)`
  (LABEL_TAC "bf") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
    REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_cbound" th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pde_tensor_smooth atlas ((g:num->real->A->real^N^N) k t)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_mnorm2 atlas n0 cs psi l ((g:num->real->A->real^N^N) 0 a)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* low jets of the iterates by Sobolev *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `l - dimindex(:N)`] RDT_SOB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `l - dimindex(:N) + dimindex(:N) = l` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CJ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  ABBREV_TAC `MJ = CJ * (&1 + M)` THEN
  SUBGOAL_THEN `&0 <= MJ` ASSUME_TAC THENL
   [EXPAND_TAC "MJ" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the background *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `g0:A->real^N^N`;
                 `l + 4`] RDT_BG_JETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `BH:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bh"))) THEN
  ABBREV_TAC `LH = &(dimindex(:N) * dimindex(:N)) * B` THEN
  (* the pointwise data in the charts *)
  SUBGOAL_THEN
   `!k t i y. a <= t /\ t < a + tau /\ i < n0 /\ y IN ks i
              ==> metric_field (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                               (metric_local atlas (cs i) ((g:num->real->A->real^N^N) k t)) /\
                  metric_field (IMAGE (SND(cs i)) (FST(cs i)))
                               (metric_local atlas (cs i) (g0:A->real^N^N)) /\
                  y IN IMAGE (SND(cs i)) (FST(cs i)) /\
                  norm((vectorize:real^N^N->real^(N,N)finite_prod)
                         (metric_local atlas (cs i) (g k t) y)) <= K /\
                  (!w. norm w pow 2 <= K * (w dot (metric_local atlas (cs i) (g k t) y ** w))) /\
                  pde_jetn (l - dimindex(:N))
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas (cs i) (g k t)) y <= MJ /\
                  pde_jetn (l + 4)
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas (cs i) g0) y <= BH /\
                  norm((vectorize:real^N^N->real^(N,N)finite_prod)
                         (matrix_inv(metric_local atlas (cs i) g0 y))) <= LH`
  (LABEL_TAC "pt") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "bf" (MP_TAC o SPECL [`k:num`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `0`; `K:real`;
                   `(g:num->real->A->real^N^N) k t`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `s0 + 3`; `B:real`;
                   `g0:A->real^N^N`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric];
      ASM_MESON_TAC[riemannian_metric];
      ASM SET_TAC[];
      USE_THEN "sob" (MP_TAC o SPECL [`(g:num->real->A->real^N^N) k t`; `M:real`; `i:num`;
                                      `y:real^N`]) THEN
      EXPAND_TAC "MJ" THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "bh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "LH" THEN MATCH_MP_TAC RDT_INV_BOUND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the constants *)
  MP_TAC(SPECL [`(l + 1) DIV 2 + 1`; `K:real`; `MJ:real`; `BH:real`; `LH:real`]
    RDT_COEF_CJET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))) THEN
  ABBREV_TAC `Mc = C1c * (&1 + MJ)` THEN
  SUBGOAL_THEN `&0 <= Mc` ASSUME_TAC THENL
   [EXPAND_TAC "Mc" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(K pow 3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `l + 1`; `inv(K pow 3)`; `Mc:real`] RDT_MENERGY_T) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CE:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "me"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `l + 1`; `K:real`; `MJ:real`; `BH:real`; `LH:real`] RDT_FORCING_T) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fo"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `l + 1`; `K:real`; `MJ:real`; `BH:real`; `LH:real`] RDT_COEF_INT_T) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CQ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cq"))) THEN
  (* the derivative bound for each step *)
  SUBGOAL_THEN
   `!k t. ?D. a < t /\ t < a + tau
              ==> ((\r. pde_mnorm2 atlas n0 cs psi (l + 1) ((g:num->real->A->real^N^N) (SUC k) r))
                   has_real_derivative D) (atreal t) /\
                  D <= CE * pde_mnorm2 atlas n0 cs psi (l + 1) (g (SUC k) t) +
                       (CE * (CF + MJ pow 2 * CQ)) *
                       (&1 + pde_mnorm2 atlas n0 cs psi (l + 1) (g k t))`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN
    ASM_CASES_TAC `a < t /\ t < a + tau` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> concl th = `a < t /\ t < a + tau`)) THEN
    SUBGOAL_THEN `a <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `pde_rdt_ball (top,atlas) n0 cs ks psi s0 K a tau g0 ((g:num->real->A->real^N^N) k) /\
      pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k))`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[pde_rdt_ball; pde_rdt_step] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `pde_tfam_from atlas a (a + tau)
        (\t x. pde_rdt_rhs atlas g0 ((g:num->real->A->real^N^N) k t) x -
               pde_trhess atlas (g k t) g0 (g k t) x)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PDE_RDT_REMAINDER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "me" (MP_TAC o SPECL
     [`a:real`; `a + tau:real`; `(g:num->real->A->real^N^N) k`; `g0:A->real^N^N`;
      `\t x. pde_rdt_rhs atlas g0 ((g:num->real->A->real^N^N) k t) x -
             pde_trhess atlas (g k t) g0 (g k t) x`;
      `g0:A->real^N^N`; `(g:num->real->A->real^N^N) (SUC k)`; `t:real`; `MJ:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        USE_THEN "bf" (MP_TAC o SPECL [`k:num`; `r:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`; `w:real^N`] THEN STRIP_TAC THEN
        USE_THEN "pt" (MP_TAC o SPECL [`k:num`; `t:real`; `i:num`; `y:real^N`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        REWRITE_TAC[RDT_MLCOEF_EQ] THEN
        MP_TAC(ISPECL [`K:real`; `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                    ((g:num->real->A->real^N^N) k t) y`] RDT_INV_LOWER) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
        USE_THEN "pt" (MP_TAC o SPECL [`k:num`; `t:real`; `i:num`; `y:real^N`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        REWRITE_TAC[RDT_MLCOEF_EQ] THEN EXPAND_TAC "Mc" THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `C1c * (&1 + pde_jetn ((l + 1) DIV 2 + 1)
                             ((vectorize:real^N^N->real^(N,N)finite_prod) o
                              metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                ((g:num->real->A->real^N^N) k t)) y)` THEN
        CONJ_TAC THENL
         [USE_THEN "c1" MATCH_MP_TAC THEN
          EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
           [EXISTS_TAC `pde_jetn (l - dimindex(:N))
                          ((vectorize:real^N^N->real^(N,N)finite_prod) o
                           metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                             ((g:num->real->A->real^N^N) k t)) y`;
            EXISTS_TAC `pde_jetn (l + 4)
                          ((vectorize:real^N^N->real^(N,N)finite_prod) o
                           metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                             (g0:A->real^N^N)) y`] THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `pde_jetn (l - dimindex(:N))
                        ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                           ((g:num->real->A->real^N^N) k t)) y` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
        MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
        USE_THEN "pt" (MP_TAC o SPECL [`SUC k`; `t:real`; `i:num`; `y:real^N`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (l - dimindex(:N))
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                         ((g:num->real->A->real^N^N) (SUC k) t)) y` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> rdt_has_const "rdt_cjet" th &&
                                            not(is_forall(concl th)))) THEN
    REWRITE_TAC[RDT_MLCOEF_EQ] THEN ASM_REWRITE_TAC[] THEN
    (* the tame bounds *)
    USE_THEN "fo" (MP_TAC o SPECL [`g0:A->real^N^N`; `(g:num->real->A->real^N^N) k t`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "bf" (MP_TAC o SPECL [`k:num`; `t:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "pt" (MP_TAC o SPECL [`k:num`; `t:real`; `i:num`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `pde_jetn (l - dimindex(:N))
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                         ((g:num->real->A->real^N^N) k t)) y`;
        EXISTS_TAC `pde_jetn (l + 4)
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                         (g0:A->real^N^N)) y`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(l + 1) - 1 = l`] THEN
    USE_THEN "cq" (MP_TAC o SPECL [`g0:A->real^N^N`; `(g:num->real->A->real^N^N) k t`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "bf" (MP_TAC o SPECL [`k:num`; `t:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "pt" (MP_TAC o SPECL [`k:num`; `t:real`; `i:num`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `pde_jetn (l - dimindex(:N))
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                         ((g:num->real->A->real^N^N) k t)) y`;
        EXISTS_TAC `pde_jetn (l + 4)
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                         (g0:A->real^N^N)) y`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `X1 = pde_mnorm2 atlas n0 cs psi (l + 1) ((g:num->real->A->real^N^N) (SUC k) t)` THEN
    ABBREV_TAC `X0 = pde_mnorm2 atlas n0 cs psi (l + 1) ((g:num->real->A->real^N^N) k t)` THEN
    ABBREV_TAC `Fk = pde_mnorm2 atlas n0 cs psi l
                       (\x. pde_rdt_rhs atlas g0 ((g:num->real->A->real^N^N) k t) x -
                            pde_trhess atlas (g k t) g0 (g k t) x)` THEN
    ABBREV_TAC `Qk = sum {i | i < n0}
                       (\i. drop(integral ((ks:num->real^N->bool) i)
                          (\y. lift(rdt_cjet (l + 1)
                             (\y. transp(matrix_inv(metric_local atlas
                                    ((cs:num->(A->bool)#(A->real^N)) i)
                                    ((g:num->real->A->real^N^N) k t) y)))
                             (\y c. pde_mlbb (metric_local atlas (cs i) (g k t))
                                             (metric_local atlas (cs i) (g0:A->real^N^N)) y c)
                             (\y. pde_mlcc (metric_local atlas (cs i) (g k t))
                                           (metric_local atlas (cs i) g0) y) y pow 2))))` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `CE * Fk <= CE * (CF * (&1 + X0)) /\
                  CE * (MJ pow 2 * Qk) <= CE * (MJ pow 2 * (CQ * (&1 + X0)))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CE * (X1 + Fk + MJ pow 2 * Qk)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`CE * Fk <= CE * (CF * (&1 + X0))`;
                           `CE * (MJ pow 2 * Qk) <= CE * (MJ pow 2 * (CQ * (&1 + X0)))`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `D:num->real->real`) THEN
  MP_TAC(ISPECL
   [`\k t. pde_mnorm2 atlas n0 cs psi (l + 1) ((g:num->real->A->real^N^N) k t)`;
    `D:num->real->real`; `pde_mnorm2 atlas n0 cs psi (l + 1) (g0:A->real^N^N)`;
    `pde_mnorm2 atlas n0 cs psi (l + 1) (g0:A->real^N^N)`; `CE:real`;
    `CE * (CF + MJ pow 2 * CQ)`; `a:real`; `a + tau:real`] RDT_PICARD_ODE) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN(X_CHOOSE_TAC `M':real`) THEN EXISTS_TAC `M':real` THEN ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `&0 <= pde_mnorm2 atlas n0 cs psi (l + 1) (g0:A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
    ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`k:num`; `Tm:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC RDT_MNORM2_CONT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`; `a + tau:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
    SIMP_TAC[pde_rdt_ball; ETA_AX];
    MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "bf" (MP_TAC o SPECL [`k:num`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `k:num` THEN MATCH_MP_TAC RDT_MNORM2_CONG THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC k` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
    SIMP_TAC[pde_rdt_ball; ETA_AX]]);;

(* All levels, by induction from the ball level s0. *)

let RDT_ITER_ALL_LEVELS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s0 B K a tau
    (g0:A->real^N^N) (g:num->real->A->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s0 /\ &0 <= B /\ &0 < K /\ &0 < tau /\
     riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks (s0 + 3) B g0 /\
     (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s0 K a tau g0 (g k)) /\
     (!k. pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k))) /\
     g 0 = (\t. g0)
     ==> !l. ?M. !k t. a <= t /\ t < a + tau
                       ==> pde_mnorm2 atlas n0 cs psi l (g k t) <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. ?M. !k t. a <= t /\ t < a + tau
                  ==> pde_mnorm2 atlas n0 cs psi (s0 + d) ((g:num->real->A->real^N^N) k t) <= M`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [EXISTS_TAC `K:real` THEN REWRITE_TAC[ADD_CLAUSES] THEN
      MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
      REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_cbound" th)) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_TAC `M:real`) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                     `psi:num->A->real`; `s0:num`; `B:real`; `K:real`; `a:real`; `tau:real`;
                     `g0:A->real^N^N`; `g:num->real->A->real^N^N`; `(s0:num) + d`; `M:real`]
        RDT_ITER_LEVEL_STEP) THEN
      ASM_REWRITE_TAC[LE_ADD; ARITH_RULE `s0 + SUC d = (s0 + d) + 1`]];
    ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `M:real` o SPEC `l:num`) THEN EXISTS_TAC `M:real` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_mnorm2 atlas n0 cs psi (s0 + l) ((g:num->real->A->real^N^N) k t)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC RDT_MNORM2_MONO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(l:num) <= s0 + l`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
  REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_cbound" th)) THEN
  ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH]);;

