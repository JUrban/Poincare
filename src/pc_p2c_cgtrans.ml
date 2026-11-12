(* ========================================================================= *)
(* Unit pc_p2c_cgtrans (Part 2C, used in the pc_p2c_cg route): uniform jet   *)
(* bounds for compositions (a uniform form of PDM_COMPOSE_JET_BOUND: the     *)
(* constant depends only on bounds of the derivatives of the inner map and   *)
(* of the coefficients at the point), the Leibniz bound for bilinear         *)
(* products, and C^(m+1) bounds for isometries between C^m-controlled        *)
(* metrics on Euclidean domains (the transition maps between normal charts), *)
(* from the second-derivative identity D^2 T = DT . Gamma(G) -               *)
(* Gamma(H)(T)(DT,DT).                                                       *)
(* ========================================================================= *)

needs "src/pc_pde_mnorm.ml";;
needs "src/pc_lrg.ml";;
needs "src/pc_rf_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Leibniz bounds for bilinear products of smooth maps on an                *)
(* open set, list by list and for the jet sums pde_jetn.                     *)
(* ------------------------------------------------------------------------- *)

let P2CT_PARTIAL_BILINEAR_OPEN = prove
 (`!(bb:real^P->real^Q->real^K) s (f:real^N->real^P) g i y.
     bilinear bb /\ open s /\ smooth_map_on s f /\ smooth_map_on s g /\ y IN s
     ==> partial_derivative i (\y. bb (f y) (g y)) y =
         bb (partial_derivative i f y) (g y) + bb (f y) (partial_derivative i g y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_PARTIAL_BILINEAR THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P2CT_JETN_0 = prove
 (`!(f:real^N->real^P) y. pde_jetn 0 f y = norm(f y)`,
  REWRITE_TAC[pde_jetn; PDE_INDEX_LISTS_0; SUM_SING; iterated_partial]);;

let P2CT_LIST_SPLIT_LAST = prove
 (`!l:num list n. LENGTH l = SUC n ==> ?l0 i. l = APPEND l0 [i] /\ LENGTH l0 = n`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`BUTLAST(l:num list)`; `LAST(l:num list)`] THEN
  SUBGOAL_THEN `~(l:num list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `LENGTH(l:num list) = SUC n` THEN
    ASM_REWRITE_TAC[LENGTH; NOT_SUC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC APPEND_BUTLAST_LAST THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `LENGTH(APPEND (BUTLAST l) [LAST l]) = LENGTH(l:num list)` MP_TAC THENL
     [ASM_SIMP_TAC[APPEND_BUTLAST_LAST]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC]);;

let P2CT_BILINEAR_JET = prove
 (`!(bb:real^P->real^Q->real^K) Bb s.
     bilinear bb /\ &0 <= Bb /\ open s /\ (!u v. norm(bb u v) <= Bb * norm u * norm v)
     ==> !n l (f:real^N->real^P) g y.
           smooth_map_on s f /\ smooth_map_on s g /\ y IN s /\ LENGTH l = n /\
           ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
           ==> norm(iterated_partial l (\y. bb (f y) (g y)) y)
               <= &2 pow n * Bb * pde_jetn n f y * pde_jetn n g y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[iterated_partial; P2CT_JETN_0; real_pow; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l:num list`; `f:real^N->real^P`; `g:real^N->real^Q`; `y:real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`l:num list`; `n:num`] P2CT_LIST_SPLIT_LAST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num list` (X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC o
    check (fun th -> can (term_match [] `ALL P (l0:num list) /\ Q`) (concl th))) THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  SUBGOAL_THEN
   `iterated_partial l0 (partial_derivative i (\y. (bb:real^P->real^Q->real^K) (f y) (g y))) y =
    iterated_partial l0 (\y. bb (partial_derivative i (f:real^N->real^P) y) (g y)) y +
    iterated_partial l0 (\y. bb (f y) (partial_derivative i (g:real^N->real^Q) y)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `iterated_partial l0
                  (\y. (bb:real^P->real^Q->real^K) (partial_derivative i (f:real^N->real^P) y) (g y) +
                       bb (f y) (partial_derivative i (g:real^N->real^Q) y)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2CT_PARTIAL_BILINEAR_OPEN THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`l0:num list`; `s:real^N->bool`;
                     `\y. (bb:real^P->real^Q->real^K) (partial_derivative i (f:real^N->real^P) y) (g y)`;
                     `\y. (bb:real^P->real^Q->real^K) (f y) (partial_derivative i (g:real^N->real^Q) y)`]
                    PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
        DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`l0:num list`; `partial_derivative i (f:real^N->real^P)`;
                  `g:real^N->real^Q`; `y:real^N`] th) THEN
    MP_TAC(SPECL [`l0:num list`; `f:real^N->real^P`;
                  `partial_derivative i (g:real^N->real^Q)`; `y:real^N`] th)) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `i:num`; `f:real^N->real^P`; `y:real^N`] PDE_JETN_PARTIAL) THEN
  MP_TAC(ISPECL [`n:num`; `i:num`; `g:real^N->real^Q`; `y:real^N`] PDE_JETN_PARTIAL) THEN
  MP_TAC(ISPECL [`n:num`; `SUC n`; `f:real^N->real^P`; `y:real^N`] PDE_JETN_MONO) THEN
  MP_TAC(ISPECL [`n:num`; `SUC n`; `g:real^N->real^Q`; `y:real^N`] PDE_JETN_MONO) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= SUC n`] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `f:real^N->real^P`; `y:real^N`] PDE_JETN_POS) THEN
  MP_TAC(ISPECL [`n:num`; `g:real^N->real^Q`; `y:real^N`] PDE_JETN_POS) THEN
  MP_TAC(ISPECL [`n:num`; `partial_derivative i (f:real^N->real^P)`; `y:real^N`] PDE_JETN_POS) THEN
  MP_TAC(ISPECL [`n:num`; `partial_derivative i (g:real^N->real^Q)`; `y:real^N`] PDE_JETN_POS) THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `a1 = pde_jetn n (partial_derivative i (f:real^N->real^P)) y` THEN
  ABBREV_TAC `a2 = pde_jetn n (partial_derivative i (g:real^N->real^Q)) y` THEN
  ABBREV_TAC `b1 = pde_jetn n (f:real^N->real^P) y` THEN
  ABBREV_TAC `b2 = pde_jetn n (g:real^N->real^Q) y` THEN
  ABBREV_TAC `c1 = pde_jetn (SUC n) (f:real^N->real^P) y` THEN
  ABBREV_TAC `c2 = pde_jetn (SUC n) (g:real^N->real^Q) y` THEN
  ABBREV_TAC `p = &2 pow n` THEN
  SUBGOAL_THEN `&0 <= p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p * Bb * a1 * b2 <= p * Bb * c1 * c2 /\ p * Bb * b1 * a2 <= p * Bb * c1 * c2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(iterated_partial l0
           (\y. (bb:real^P->real^Q->real^K) (partial_derivative i (f:real^N->real^P) y) (g y)) y) +
    norm(iterated_partial l0
           (\y. (bb:real^P->real^Q->real^K) (f y) (partial_derivative i (g:real^N->real^Q) y)) y)` THEN
  REWRITE_TAC[NORM_TRIANGLE] THEN ASM_REAL_ARITH_TAC);;

let P2CT_BILINEAR_JETN = prove
 (`!(bb:real^P->real^Q->real^K) Bb s n (f:real^N->real^P) g y.
     bilinear bb /\ &0 <= Bb /\ open s /\ (!u v. norm(bb u v) <= Bb * norm u * norm v) /\
     smooth_map_on s f /\ smooth_map_on s g /\ y IN s
     ==> pde_jetn n (\y. bb (f y) (g y)) y <=
         &(CARD(pde_index_lists n (:N))) * &2 pow n * Bb * pde_jetn n f y * pde_jetn n g y`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [pde_jetn] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow (LENGTH(l:num list)) * Bb *
              pde_jetn (LENGTH l) (f:real^N->real^P) y * pde_jetn (LENGTH l) (g:real^N->real^Q) y` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `Bb:real`; `s:real^N->bool`]
                  P2CT_BILINEAR_JET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_MUL; PDE_JETN_POS] THEN
  ASM_SIMP_TAC[REAL_POW_MONO; REAL_OF_NUM_LE; ARITH_RULE `1 <= 2`] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PDE_JETN_POS; PDE_JETN_MONO]);;

(* ------------------------------------------------------------------------- *)
(* The uniform jet bound for forms                                           *)
(*   sum_q (g o tau)_q c_q  (Faa di Bruno in jet form),                      *)
(* with a constant depending only on the order and on bounds of the jets of *)
(* the coefficients c_q and of the first derivatives of tau at the point.   *)
(* The induction follows PDM_COMPOSE_JET_BOUND (the innermost derivative is *)
(* split off by PDM_FORM_PARTIAL_ITERATED); the coefficient bounds of the  *)
(* new forms come from P2CT_BILINEAR_JETN.                                   *)
(* ------------------------------------------------------------------------- *)

let P2CT_COMPONENT_MUL_BILINEAR = prove
 (`!j. bilinear (\(u:real^M) (v:real^Q). u$j % v)`,
  GEN_TAC THEN REWRITE_TAC[bilinear; linear] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let P2CT_COMPONENT_MUL_BOUND = prove
 (`!j (u:real^M) (v:real^Q). 1 <= j /\ j <= dimindex(:M)
     ==> norm(u$j % v) <= &1 * norm u * norm v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[COMPONENT_LE_NORM; NORM_POS_LE]);;

let P2CT_FORM_JET_UNIFORM = prove
 (`!n B. ?C. &0 <= C /\
     !s0 t0 (tau:real^N->real^M) (c:num->real^N->real^Q) (g:real^M->real^P) y.
       open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
       (!q. smooth_map_on s0 (c q)) /\ smooth_map_on t0 g /\ y IN s0 /\
       (!q. 1 <= q /\ q <= dimindex(:P) ==> pde_jetn n (c q) y <= B) /\
       (!i. 1 <= i /\ i <= dimindex(:N) ==> pde_jetn n (partial_derivative i tau) y <= B)
       ==> !l. LENGTH l = n /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
               ==> norm(iterated_partial l
                          (\y. vsum(1..dimindex(:P)) (\q. (g(tau y))$q % c q y)) y)
                   <= C * pde_jetn n g (tau y)`,
  INDUCT_TAC THENL
   [X_GEN_TAC `B:real` THEN EXISTS_TAC `&(dimindex(:P)) * abs B` THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_ABS_POS] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LENGTH_EQ_NIL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[iterated_partial; P2CT_JETN_0] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:P))
                  (\q. norm((g:real^M->real^P)((tau:real^N->real^M) y)) * abs B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; COMPONENT_LE_NORM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      UNDISCH_TAC `!q. 1 <= q /\ q <= dimindex(:P)
                       ==> pde_jetn 0 ((c:num->real^N->real^Q) q) y <= B` THEN
      DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[P2CT_JETN_0];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `B:real` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1")) o
              SPEC `B:real`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c2")) o
              SPEC `max B (&(CARD(pde_index_lists n (:N))) * &2 pow n * &1 * B * B)`) THEN
  EXISTS_TAC `C1 + &(dimindex(:M)) * C2` THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS] THEN
  MAP_EVERY X_GEN_TAC [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
                       `c:num->real^N->real^Q`; `g:real^M->real^P`; `y:real^N`] THEN
  STRIP_TAC THEN X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:num list`; `n:num`] P2CT_LIST_SPLIT_LAST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num list` (X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC o
    check (fun th -> can (term_match [] `ALL P (l0:num list) /\ Q`) (concl th))) THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
                 `c:num->real^N->real^Q`; `g:real^M->real^P`; `i:num`; `l0:num list`;
                 `y:real^N`] PDM_FORM_PARTIAL_ITERATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  (* the first form *)
  SUBGOAL_THEN
   `norm(iterated_partial l0
           (\y. vsum(1..dimindex(:P))
                  (\q. ((g:real^M->real^P)((tau:real^N->real^M) y))$q %
                       partial_derivative i ((c:num->real^N->real^Q) q) y)) y)
    <= C1 * pde_jetn n g (tau y)`
  ASSUME_TAC THENL
   [REMOVE_THEN "c1" (MP_TAC o SPECL
      [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
       `\q. partial_derivative i ((c:num->real^N->real^Q) q)`; `g:real^M->real^P`;
       `y:real^N`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN CONJ_TAC THEN
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `pde_jetn (SUC n) ((c:num->real^N->real^Q) q) y` THEN
        ASM_SIMP_TAC[PDE_JETN_PARTIAL];
        EXISTS_TAC `pde_jetn (SUC n) (partial_derivative q (tau:real^N->real^M)) y` THEN
        ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `n <= SUC n`]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the second forms *)
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:M)
        ==> norm(iterated_partial l0
                   (\y. vsum(1..dimindex(:P))
                          (\q. (partial_derivative j (g:real^M->real^P)
                                  ((tau:real^N->real^M) y))$q %
                               ((partial_derivative i tau y)$j %
                                (c:num->real^N->real^Q) q y))) y)
            <= C2 * pde_jetn n (partial_derivative j g) (tau y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REMOVE_THEN "c2" (MP_TAC o SPECL
      [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
       `\q y. (partial_derivative i (tau:real^N->real^M) y)$j %
              (c:num->real^N->real^Q) q y`;
       `partial_derivative j (g:real^M->real^P)`; `y:real^N`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; PDM_COEFF2_SMOOTH; ETA_AX] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`\(u:real^M) (v:real^Q). u$j % v`; `&1`; `s0:real^N->bool`; `n:num`;
                       `partial_derivative i (tau:real^N->real^M)`;
                       `(c:num->real^N->real^Q) q`; `y:real^N`] P2CT_BILINEAR_JETN) THEN
        ASM_SIMP_TAC[P2CT_COMPONENT_MUL_BILINEAR; P2CT_COMPONENT_MUL_BOUND; REAL_POS;
                     SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
        MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= max B z`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PDE_JETN_POS] THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
         [EXISTS_TAC `pde_jetn (SUC n) (partial_derivative i (tau:real^N->real^M)) y` THEN
          ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `n <= SUC n`];
          EXISTS_TAC `pde_jetn (SUC n) ((c:num->real^N->real^Q) q) y` THEN
          ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `n <= SUC n`]];
        X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B z`) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (SUC n) (partial_derivative q (tau:real^N->real^M)) y` THEN
        ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `n <= SUC n`]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * pde_jetn n (g:real^M->real^P) ((tau:real^N->real^M) y) +
              sum(1..dimindex(:M)) (\j. C2 * pde_jetn n (partial_derivative j g) (tau y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^Q) <= x /\ norm(b:real^Q) <= y ==> norm(a + b) <= x + y`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `n <= SUC n`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M))
                (\j. C2 * pde_jetn (SUC n) (g:real^M->real^P) ((tau:real^N->real^M) y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

(* Iterated partials of a constant (the statement of RFA_ITERATED_PARTIAL_ *)
(* CONST of pc_rfa_r1, which is not in this closure).                       *)

let P2CT_ITERATED_PARTIAL_CONST = prove
 (`!l (c:real^P).
     iterated_partial l (\z:real^M. c) = if l = [] then (\z. c) else (\z. vec 0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_ALT; FRECHET_DERIVATIVE_CONST_AT]);;

(* Plain compositions g o tau, as the forms with constant coefficients.     *)

let P2CT_COMPOSE_JET_UNIFORM = prove
 (`!n B. ?C. &0 <= C /\
     !s0 t0 (tau:real^N->real^M) (g:real^M->real^P) y.
       open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
       smooth_map_on t0 g /\ y IN s0 /\
       (!i. 1 <= i /\ i <= dimindex(:N) ==> pde_jetn n (partial_derivative i tau) y <= B)
       ==> !l. LENGTH l = n /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
               ==> norm(iterated_partial l (\y. g(tau y)) y) <= C * pde_jetn n g (tau y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `max B (&1)`] (INST_TYPE [`:P`,`:Q`] P2CT_FORM_JET_UNIFORM)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REMOVE_THEN "f" (MP_TAC o SPECL
    [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
     `\q:num y:real^N. basis q:real^P`; `g:real^M->real^P`; `y:real^N`]) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `q:num` THEN STRIP_TAC THENL
     [REWRITE_TAC[pde_jetn; P2CT_ITERATED_PARTIAL_CONST; COND_RATOR; COND_RAND] THEN
      ASM_SIMP_TAC[NORM_BASIS; NORM_0; SUM_DELTA] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> x <= max B (&1)`) THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B (&1)`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `l:num list` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= z ==> y <= z`) THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM BASIS_EXPANSION] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Jet bookkeeping (a term of a jet sum, the jet of order n+1               *)
(* through the first partials), entries and products of matrices, the jets *)
(* of inverse matrices and of Christoffel symbols.                          *)
(* ------------------------------------------------------------------------- *)

let P2CT_JETN_TERM_LE = prove
 (`!n l (f:real^N->real^Q) y.
     LENGTH l <= n /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l f y) <= pde_jetn n f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MP_TAC(ISPECL [`{l:num list}`; `pde_index_lists n (:N)`;
                 `\l. norm(iterated_partial l (f:real^N->real^Q) y)`] SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; PDE_INDEX_LISTS_FINITE; NORM_POS_LE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SING_SUBSET; pde_index_lists; IN_ELIM_THM]);;

let P2CT_JETN_SUC_BOUND = prove
 (`!n (f:real^N->real^Q) y.
     pde_jetn (SUC n) f y <=
     norm(f y) + &(CARD(pde_index_lists (SUC n) (:N))) *
                 sum(1..dimindex(:N)) (\i. pde_jetn n (partial_derivative i f) y)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `S = sum(1..dimindex(:N)) (\i. pde_jetn n (partial_derivative i (f:real^N->real^Q)) y)` THEN
  SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[PDE_JETN_POS];
    ALL_TAC] THEN
  REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(pde_index_lists (SUC n) (:N))
                (\l. (if l = [] then norm((f:real^N->real^Q) y) else &0) + S)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[iterated_partial] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_LID] THEN
    SUBGOAL_THEN `?m. LENGTH(l:num list) = SUC m` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `LENGTH(l:num list) - 1` THEN
      UNDISCH_TAC `~(l:num list = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`l:num list`; `m:num`] P2CT_LIST_SPLIT_LAST) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:num list` (X_CHOOSE_THEN `i:num`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL; LENGTH_APPEND; LENGTH]) THEN
    REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn n (partial_derivative i (f:real^N->real^Q)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CT_JETN_TERM_LE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      EXPAND_TAC "S" THEN
      MP_TAC(ISPECL [`{i:num}`; `1..dimindex(:N)`;
                     `\i. pde_jetn n (partial_derivative i (f:real^N->real^Q)) y`]
                    SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG; PDE_JETN_POS] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_NUMSEG]];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; PDE_INDEX_LISTS_FINITE; SUM_DELTA; SUM_CONST] THEN
  SUBGOAL_THEN `([]:num list) IN pde_index_lists (SUC n) (:N)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0]; REAL_ARITH_TAC]);;

(* Jets of linear images, of functions agreeing near the point, of sums.    *)

let P2CT_JETN_LINEAR = prove
 (`!n (L:real^P->real^Q) BL s (w:real^N->real^P) y.
     linear L /\ (!x. norm(L x) <= BL * norm x) /\ open s /\ smooth_map_on s w /\ y IN s
     ==> pde_jetn n (\z. L(w z)) y <= BL * pde_jetn n w y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `L:real^P->real^Q`; `w:real^N->real^P`; `s:real^N->bool`;
                 `y:real^N`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let P2CT_JETN_LOCAL = prove
 (`!n s (f:real^N->real^Q) g y.
     open s /\ y IN s /\ (!z. z IN s ==> f z = g z)
     ==> pde_jetn n f y = pde_jetn n g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2CT_JETN_ADD = prove
 (`!n s (f:real^N->real^Q) g y.
     open s /\ smooth_map_on s f /\ smooth_map_on s g /\ y IN s
     ==> pde_jetn n (\z. f z + g z) y <= pde_jetn n f y + pde_jetn n g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  SIMP_TAC[GSYM SUM_ADD; PDE_INDEX_LISTS_FINITE] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `s:real^N->bool`; `f:real^N->real^Q`; `g:real^N->real^Q`]
                PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_TRIANGLE]);;

(* Inverse matrices: the first partials and the jets.                       *)

let P2CT_MATMUL_BILINEAR_BOUND = prove
 (`!(M1:real^(N,N)finite_prod) M2.
     norm((vectorize:real^N^N->real^(N,N)finite_prod) (matrify M1 ** matrify M2))
     <= &1 * norm M1 * norm M2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  MP_TAC(ISPECL [`matrify(M1:real^(N,N)finite_prod):real^N^N`;
                 `matrify(M2:real^(N,N)finite_prod):real^N^N`] NORM_VECTORIZE_MUL_LE) THEN
  REWRITE_TAC[VECTORIZE_MATRIFY]);;

let P2CT_GINV_PARTIAL = prove
 (`!s (A:real^N->real^M^M) y i.
     open s /\ smooth_map_on s (vectorize o A) /\ (!z. z IN s ==> ~(det(A z) = &0)) /\
     y IN s
     ==> partial_derivative i (vectorize o (\z. matrix_inv(A z))) y =
         vectorize(--(matrix_inv(A y) ** matrify(partial_derivative i (vectorize o A) y) **
                      matrix_inv(A y)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN
  MP_TAC(ISPECL [`A:real^N->real^M^M`; `s:real^N->bool`; `y:real^N`]
                LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[]);;

let P2CT_VECTORIZE_NEG = prove
 (`!A:real^N^M. vectorize(--A) = --(vectorize A)`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_FINITE_PROD; VECTOR_NEG_COMPONENT] THEN
  SIMP_TAC[VECTORIZE_COMPONENT; MATRIX_NEG_COMPONENT]);;

let P2CT_JETN_NEG = prove
 (`!n s (f:real^N->real^Q) y.
     open s /\ smooth_map_on s f /\ y IN s ==> pde_jetn n (\z. --(f z)) y <= pde_jetn n f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `\x:real^Q. --x`; `&1`; `s:real^N->bool`; `f:real^N->real^Q`;
                 `y:real^N`] P2CT_JETN_LINEAR) THEN
  ASM_REWRITE_TAC[NORM_NEG; REAL_MUL_LID; REAL_LE_REFL] THEN
  REWRITE_TAC[linear] THEN ANTS_TAC THENL [VECTOR_ARITH_TAC; REWRITE_TAC[]]);;

let P2CT_GINV_JET = prove
 (`!n B L. ?C. &0 <= C /\
     !s (A:real^N->real^M^M) y.
       open s /\ smooth_map_on s (vectorize o A) /\ (!z. z IN s ==> ~(det(A z) = &0)) /\
       y IN s /\ pde_jetn n (vectorize o A) y <= B /\
       norm(vectorize(matrix_inv(A y))) <= L
       ==> pde_jetn n (vectorize o (\z. matrix_inv(A z))) y <= C`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN EXISTS_TAC `abs L` THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[P2CT_JETN_0; o_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih")) o
                SPECL [`B:real`; `L:real`]) THEN
  ABBREV_TAC `K1 = &(CARD(pde_index_lists n (:N)))` THEN
  ABBREV_TAC `K2 = &2 pow n` THEN
  SUBGOAL_THEN `&0 <= K1 /\ &0 <= K2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K1"; "K2"] THEN SIMP_TAC[REAL_POS; REAL_POW_LE]; ALL_TAC] THEN
  EXISTS_TAC `abs L + &(CARD(pde_index_lists (SUC n) (:N))) *
                      sum(1..dimindex(:N))
                        (\i. &1 * K1 * K2 * &1 * C0 * (K1 * K2 * &1 * abs B * C0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_ABS_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `A:real^N->real^M^M`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (vectorize o (\z. matrix_inv((A:real^N->real^M^M) z)))`
  ASSUME_TAC THENL [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_jetn n (vectorize o (\z. matrix_inv((A:real^N->real^M^M) z))) y <= C0`
  ASSUME_TAC THENL
   [REMOVE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC n) (vectorize o (A:real^N->real^M^M)) y` THEN
    ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `n <= SUC n`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm((vectorize o (\z. matrix_inv((A:real^N->real^M^M) z))) y) +
    &(CARD(pde_index_lists (SUC n) (:N))) *
    sum(1..dimindex(:N))
      (\i. pde_jetn n (partial_derivative i (vectorize o (\z. matrix_inv(A z)))) y)` THEN
  REWRITE_TAC[P2CT_JETN_SUC_BOUND] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `ai = vectorize o (\z. matrix_inv((A:real^N->real^M^M) z))` THEN
  ABBREV_TAC `di = partial_derivative i (vectorize o (A:real^N->real^M^M))` THEN
  SUBGOAL_THEN `smooth_map_on s (di:real^N->real^(M,M)finite_prod)` ASSUME_TAC THENL
   [EXPAND_TAC "di" THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_jetn n (di:real^N->real^(M,M)finite_prod) y <= abs B` ASSUME_TAC THENL
   [EXPAND_TAC "di" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC n) (vectorize o (A:real^N->real^M^M)) y` THEN
    ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `bb = \(M1:real^(M,M)finite_prod) (M2:real^(M,M)finite_prod).
                     (vectorize:real^M^M->real^(M,M)finite_prod) (matrify M1 ** matrify M2)` THEN
  SUBGOAL_THEN
   `bilinear (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod) /\
    !u v. norm(bb u v) <= &1 * norm u * norm v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN REWRITE_TAC[LRG_BILINEAR_MATRIX_MUL; P2CT_MATMUL_BILINEAR_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn n (partial_derivative i (ai:real^N->real^(M,M)finite_prod)) y =
    pde_jetn n (\z. --((bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod)
                        (ai z) (bb ((di:real^N->real^(M,M)finite_prod) z) (ai z)))) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["ai"; "di"; "bb"] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `A:real^N->real^M^M`; `z:real^N`; `i:num`]
                  P2CT_GINV_PARTIAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; P2CT_VECTORIZE_NEG; MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s
      (\z. (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod)
             ((di:real^N->real^(M,M)finite_prod) z) (ai z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_jetn n (\z. (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod)
                      (ai z) (bb ((di:real^N->real^(M,M)finite_prod) z) (ai z))) y` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `s:real^N->bool`;
                   `\z. (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod)
                          (ai z) (bb ((di:real^N->real^(M,M)finite_prod) z) (ai z))`;
                   `y:real^N`] P2CT_JETN_NEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
      `bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod`;
      `ai:real^N->real^(M,M)finite_prod`;
      `\z. (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod)
             ((di:real^N->real^(M,M)finite_prod) z) (ai z)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod`;
                 `&1`; `s:real^N->bool`; `n:num`; `ai:real^N->real^(M,M)finite_prod`;
                 `\z. (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod)
                        ((di:real^N->real^(M,M)finite_prod) z) (ai z)`;
                 `y:real^N`] P2CT_BILINEAR_JETN) THEN
  MP_TAC(ISPECL [`bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod`;
                 `&1`; `s:real^N->bool`; `n:num`; `di:real^N->real^(M,M)finite_prod`;
                 `ai:real^N->real^(M,M)finite_prod`; `y:real^N`] P2CT_BILINEAR_JETN) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `di:real^N->real^(M,M)finite_prod`; `y:real^N`] PDE_JETN_POS) THEN
  MP_TAC(ISPECL [`n:num`; `ai:real^N->real^(M,M)finite_prod`; `y:real^N`] PDE_JETN_POS) THEN
  MP_TAC(ISPECL [`n:num`;
                 `\z. (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->real^(M,M)finite_prod)
                        ((di:real^N->real^(M,M)finite_prod) z) (ai z)`;
                 `y:real^N`] PDE_JETN_POS) THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `ja = pde_jetn n (ai:real^N->real^(M,M)finite_prod) y` THEN
  ABBREV_TAC `jd = pde_jetn n (di:real^N->real^(M,M)finite_prod) y` THEN
  ABBREV_TAC `jg = pde_jetn n (\z. (bb:real^(M,M)finite_prod->real^(M,M)finite_prod->
                                       real^(M,M)finite_prod)
                                    ((di:real^N->real^(M,M)finite_prod) z) (ai z)) y` THEN
  SUBGOAL_THEN `jg <= K1 * K2 * &1 * abs B * C0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1 * K2 * &1 * jd * ja` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[REAL_POS]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1 * K2 * &1 * ja * jg` THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LID]) THEN REWRITE_TAC[REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Jets of finite sums and of Christoffel symbols: in the                    *)
(* coordinate basis, christoffel G z (e_a) (e_b) = G^-1 w_ab with w_ab built *)
(* linearly from the first partials of G, so its jet of order n is bounded  *)
(* by the jet of order n+1 of G and the norm of G^-1 at the point.          *)
(* ------------------------------------------------------------------------- *)

let P2CT_JETN_VSUM = prove
 (`!n s ss (f:A->real^N->real^Q) y.
     open s /\ FINITE ss /\ (!k. k IN ss ==> smooth_map_on s (f k)) /\ y IN s
     ==> pde_jetn n (\z. vsum ss (\k. f k z)) y <= sum ss (\k. pde_jetn n (f k) y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [`\l:num list k:A. norm(iterated_partial l ((f:A->real^N->real^Q) k) y)`;
                                  `pde_index_lists n (:N)`; `ss:A->bool`] SUM_SWAP)) THEN
  ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:num list`; `s:real^N->bool`; `f:A->real^N->real^Q`; `ss:A->bool`]
                PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let P2CT_SUM_DELTA_DEP = prove
 (`!s a (f:num->real). sum s (\x. if a = x then f x else &0) = if a IN s then f a else &0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\x:num. if x = a then (f:num->real) a else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:num = a` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUM_DELTA]]);;

let P2CT_CHRISTOFFEL_BASIS = prove
 (`!(G:real^N->real^N^N) z a b.
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> christoffel G z (basis a) (basis b) =
         matrix_inv(G z) **
         (inv(&2) % (matrify(partial_derivative a (vectorize o G) z) ** basis b +
                     matrify(partial_derivative b (vectorize o G) z) ** basis a -
                     vsum(1..dimindex(:N))
                       (\k. ((partial_derivative k (vectorize o G) z)$
                               ((a - 1) * dimindex(:N) + b)) % basis k)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[christoffel; mderiv; PARTIAL_DERIVATIVE_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT;
               VECTOR_SUB_COMPONENT; VSUM_COMPONENT; BASIS_COMPONENT] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[COND_RAND; REAL_MUL_RZERO; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[P2CT_SUM_DELTA_DEP; IN_NUMSEG; DOT_BASIS; MATRIX_VECTOR_MUL_BASIS] THEN
  ASM_SIMP_TAC[column; LAMBDA_BETA; MATRIFY_COMPONENT]);;

let P2CT_MATRIFY_MUL_LINEAR = prove
 (`!x:real^N. linear (\v:real^(N,N)finite_prod. matrify v ** x)`,
  GEN_TAC THEN REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL]);;

let P2CT_MATRIFY_MUL_BILINEAR = prove
 (`bilinear (\(v:real^(N,N)finite_prod) (x:real^N). matrify v ** x)`,
  REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
              MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL]);;

let P2CT_COMPONENT_BASIS_LINEAR = prove
 (`!i k. linear (\v:real^M. (v$i) % (basis k:real^N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let P2CT_W_JET = prove
 (`!n s (G:real^N->real^N^N) y a b B.
     open s /\ smooth_map_on s (vectorize o G) /\ y IN s /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     pde_jetn (SUC n) (vectorize o G) y <= B
     ==> smooth_map_on s
           (\z. inv(&2) % (matrify(partial_derivative a (vectorize o G) z) ** basis b +
                           matrify(partial_derivative b (vectorize o G) z) ** basis a -
                           vsum(1..dimindex(:N))
                             (\k. ((partial_derivative k (vectorize o G) z)$
                                     ((a - 1) * dimindex(:N) + b)) % basis k))) /\
         pde_jetn n
           (\z. inv(&2) % (matrify(partial_derivative a (vectorize o G) z) ** basis b +
                           matrify(partial_derivative b (vectorize o G) z) ** basis a -
                           vsum(1..dimindex(:N))
                             (\k. ((partial_derivative k (vectorize o G) z)$
                                     ((a - 1) * dimindex(:N) + b)) % basis k))) y
         <= inv(&2) * (B + B + &(dimindex(:N)) * B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = \m. partial_derivative m (vectorize o (G:real^N->real^N^N))` THEN
  SUBGOAL_THEN `!m. smooth_map_on s ((d:num->real^N->real^(N,N)finite_prod) m)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. 1 <= m /\ m <= dimindex(:N)
                    ==> pde_jetn n ((d:num->real^N->real^(N,N)finite_prod) m) y <= B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC n) (vectorize o (G:real^N->real^N^N)) y` THEN
    ASM_SIMP_TAC[PDE_JETN_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. partial_derivative m (vectorize o (G:real^N->real^N^N)) =
        (d:num->real^N->real^(N,N)finite_prod) m`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "d" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `idx = (a - 1) * dimindex(:N) + b` THEN
  SUBGOAL_THEN `1 <= idx /\ idx <= dimindex(:(N,N)finite_prod)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "idx" THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(a - 1) * dimindex(:N) + dimindex(:N)` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(a - 1) * dimindex(:N) + dimindex(:N) = a * dimindex(:N)` SUBST1_TAC THENL
     [SUBGOAL_THEN `a = (a - 1) + 1`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THENL
       [ASM_ARITH_TAC; REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES]];
      ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
    ALL_TAC] THEN
  (* the three pieces *)
  ABBREV_TAC `X = \z. matrify((d:num->real^N->real^(N,N)finite_prod) a z) ** (basis b:real^N)` THEN
  ABBREV_TAC `Y = \z. matrify((d:num->real^N->real^(N,N)finite_prod) b z) ** (basis a:real^N)` THEN
  ABBREV_TAC `Z = \z. vsum(1..dimindex(:N))
                       (\k. (((d:num->real^N->real^(N,N)finite_prod) k z)$idx) % (basis k:real^N))` THEN
  SUBGOAL_THEN
   `smooth_map_on s (X:real^N->real^N) /\ smooth_map_on s (Y:real^N->real^N) /\
    smooth_map_on s (Z:real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"; "Z"] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `\v:real^(N,N)finite_prod x:real^N. matrify v ** x`;
                     `(d:num->real^N->real^(N,N)finite_prod) a`; `\z:real^N. basis b:real^N`]
                    SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[P2CT_MATRIFY_MUL_BILINEAR; SMOOTH_MAP_ON_CONST];
      MP_TAC(ISPECL [`s:real^N->bool`; `\v:real^(N,N)finite_prod x:real^N. matrify v ** x`;
                     `(d:num->real^N->real^(N,N)finite_prod) b`; `\z:real^N. basis a:real^N`]
                    SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[P2CT_MATRIFY_MUL_BILINEAR; SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(d:num->real^N->real^(N,N)finite_prod) k`;
                     `\v:real^(N,N)finite_prod. (v$idx) % (basis k:real^N)`]
                    SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[P2CT_COMPONENT_BASIS_LINEAR; o_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. inv(&2) % (matrify((d:num->real^N->real^(N,N)finite_prod) a z) ** (basis b:real^N) +
                    matrify(d b z) ** basis a -
                    vsum(1..dimindex(:N)) (\k. (d k z$idx) % basis k))) =
    (\z. inv(&2) % (((X:real^N->real^N) z + (Y:real^N->real^N) z) + --((Z:real^N->real^N) z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"; "Z"] THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s (\z. ((X:real^N->real^N) z + (Y:real^N->real^N) z)) /\
    smooth_map_on s (\z. --((Z:real^N->real^N) z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN; MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the jets of the pieces *)
  SUBGOAL_THEN `pde_jetn n (X:real^N->real^N) y <= B /\ pde_jetn n (Y:real^N->real^N) y <= B`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * pde_jetn n ((d:num->real^N->real^(N,N)finite_prod) a) y` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "X" THEN
        MP_TAC(ISPECL [`n:num`; `\v:real^(N,N)finite_prod. matrify v ** (basis b:real^N)`; `&1`;
                       `s:real^N->bool`; `(d:num->real^N->real^(N,N)finite_prod) a`; `y:real^N`]
                      P2CT_JETN_LINEAR) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[P2CT_MATRIFY_MUL_LINEAR; REAL_MUL_LID] THEN GEN_TAC THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH lhand COMPATIBLE_NORM_VECTORIZE (lhand w))) THEN
        ASM_SIMP_TAC[VECTORIZE_MATRIFY; NORM_BASIS; REAL_MUL_RID];
        ASM_SIMP_TAC[REAL_MUL_LID]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * pde_jetn n ((d:num->real^N->real^(N,N)finite_prod) b) y` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Y" THEN
        MP_TAC(ISPECL [`n:num`; `\v:real^(N,N)finite_prod. matrify v ** (basis a:real^N)`; `&1`;
                       `s:real^N->bool`; `(d:num->real^N->real^(N,N)finite_prod) b`; `y:real^N`]
                      P2CT_JETN_LINEAR) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[P2CT_MATRIFY_MUL_LINEAR; REAL_MUL_LID] THEN GEN_TAC THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH lhand COMPATIBLE_NORM_VECTORIZE (lhand w))) THEN
        ASM_SIMP_TAC[VECTORIZE_MATRIFY; NORM_BASIS; REAL_MUL_RID];
        ASM_SIMP_TAC[REAL_MUL_LID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_jetn n (Z:real^N->real^N) y <= &(dimindex(:N)) * B` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                  (\k. pde_jetn n (\z. (((d:num->real^N->real^(N,N)finite_prod) k z)$idx) %
                                        (basis k:real^N)) y)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`n:num`; `s:real^N->bool`; `1..dimindex(:N)`;
                     `\k z. (((d:num->real^N->real^(N,N)finite_prod) k z)$idx) % (basis k:real^N)`;
                     `y:real^N`] P2CT_JETN_VSUM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(d:num->real^N->real^(N,N)finite_prod) k`;
                     `\v:real^(N,N)finite_prod. (v$idx) % (basis k:real^N)`]
                    SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[P2CT_COMPONENT_BASIS_LINEAR; o_DEF];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\k. B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * pde_jetn n ((d:num->real^N->real^(N,N)finite_prod) k) y` THEN
      ASM_SIMP_TAC[REAL_MUL_LID] THEN
      MP_TAC(ISPECL [`n:num`; `\v:real^(N,N)finite_prod. (v$idx) % (basis k:real^N)`; `&1`;
                     `s:real^N->bool`; `(d:num->real^N->real^(N,N)finite_prod) k`; `y:real^N`]
                    P2CT_JETN_LINEAR) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[P2CT_COMPONENT_BASIS_LINEAR] THEN GEN_TAC THEN
      ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; REAL_MUL_RID; REAL_MUL_LID; COMPONENT_LE_NORM];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&2) * pde_jetn n (\z. ((X:real^N->real^N) z + (Y:real^N->real^N) z) +
                                       --((Z:real^N->real^N) z)) y` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `\v:real^N. inv(&2) % v`; `inv(&2)`; `s:real^N->bool`;
                   `\z. ((X:real^N->real^N) z + (Y:real^N->real^N) z) + --((Z:real^N->real^N) z)`;
                   `y:real^N`] P2CT_JETN_LINEAR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NUM; REAL_LE_REFL];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn n (\z. (X:real^N->real^N) z + (Y:real^N->real^N) z) y +
              pde_jetn n (\z. --((Z:real^N->real^N) z)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_ADD THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= x + y /\ b <= z ==> a + b <= x + y + z`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn n (X:real^N->real^N) y + pde_jetn n (Y:real^N->real^N) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CT_JETN_ADD THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn n (Z:real^N->real^N) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CT_JETN_NEG THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let P2CT_CHRISTOFFEL_JET = prove
 (`!n B L. ?C. &0 <= C /\
     !s (G:real^N->real^N^N) y a b.
       open s /\ smooth_map_on s (vectorize o G) /\ (!z. z IN s ==> ~(det(G z) = &0)) /\
       y IN s /\ 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
       pde_jetn (SUC n) (vectorize o G) y <= B /\
       norm(vectorize(matrix_inv(G y))) <= L
       ==> smooth_map_on s (\z. christoffel G z (basis a) (basis b)) /\
           pde_jetn n (\z. christoffel G z (basis a) (basis b)) y <= C`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `B:real`; `L:real`] (INST_TYPE [`:N`,`:M`] P2CT_GINV_JET)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gi"))) THEN
  EXISTS_TAC `&(CARD(pde_index_lists n (:N))) * &2 pow n * &1 * C1 *
              (inv(&2) * (abs B + abs B + &(dimindex(:N)) * abs B))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_INV_EQ; REAL_LE_ADD; REAL_ABS_POS;
                 REAL_LE_MUL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:num`; `b:num`; `B:real`] P2CT_W_JET) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `W = \z. inv(&2) % (matrify(partial_derivative a (vectorize o (G:real^N->real^N^N)) z) **
                        basis b +
                        matrify(partial_derivative b (vectorize o G) z) ** basis a -
                        vsum(1..dimindex(:N))
                          (\k. ((partial_derivative k (vectorize o G) z)$
                                  ((a - 1) * dimindex(:N) + b)) % basis k))` THEN
  STRIP_TAC THEN
  ABBREV_TAC `ai = vectorize o (\z. matrix_inv((G:real^N->real^N^N) z))` THEN
  SUBGOAL_THEN `smooth_map_on s (ai:real^N->real^(N,N)finite_prod)` ASSUME_TAC THENL
   [EXPAND_TAC "ai" THEN MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN s
        ==> christoffel (G:real^N->real^N^N) z (basis a) (basis b) =
            (\(M:real^(N,N)finite_prod) (v:real^N). matrify M ** v)
            ((ai:real^N->real^(N,N)finite_prod) z) ((W:real^N->real^N) z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["ai"; "W"] THEN
    ASM_SIMP_TAC[P2CT_CHRISTOFFEL_BASIS; o_THM; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s (\z. (\(M:real^(N,N)finite_prod) (v:real^N). matrify M ** v)
                           ((ai:real^N->real^(N,N)finite_prod) z) ((W:real^N->real^N) z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `\(M:real^(N,N)finite_prod) (v:real^N). matrify M ** v`;
                   `ai:real^N->real^(N,N)finite_prod`; `W:real^N->real^N`]
                  SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_REWRITE_TAC[P2CT_MATRIFY_MUL_BILINEAR];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. (\(M:real^(N,N)finite_prod) (v:real^N). matrify M ** v)
                     ((ai:real^N->real^(N,N)finite_prod) z) ((W:real^N->real^N) z)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_jetn n (\z. (\(M:real^(N,N)finite_prod) (v:real^N). matrify M ** v)
                     ((ai:real^N->real^(N,N)finite_prod) z) ((W:real^N->real^N) z)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2CT_JETN_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(M:real^(N,N)finite_prod) (v:real^N). matrify M ** v`; `&1`;
                 `s:real^N->bool`; `n:num`; `ai:real^N->real^(N,N)finite_prod`;
                 `W:real^N->real^N`; `y:real^N`] P2CT_BILINEAR_JETN) THEN
  ASM_REWRITE_TAC[P2CT_MATRIFY_MUL_BILINEAR; REAL_POS] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH lhand COMPATIBLE_NORM_VECTORIZE (lhand w))) THEN
    REWRITE_TAC[VECTORIZE_MATRIFY];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [SIMP_TAC[REAL_POS; REAL_POW_LE]; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THENL
   [EXPAND_TAC "ai" THEN REMOVE_THEN "gi" MATCH_MP_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC n) (vectorize o (G:real^N->real^N^N)) y` THEN
    ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `n <= SUC n`];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2) * (B + B + &(dimindex(:N)) * B)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= abs x /\ &0 <= n * (abs x - x)
                             ==> x + x + n * x <= abs x + abs x + n * abs x`) THEN
    REWRITE_TAC[REAL_ABS_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The jet-sum form of the uniform composition bound.                       *)
(* ------------------------------------------------------------------------- *)

let P2CT_FORM_JETN_UNIFORM = prove
 (`!m B. ?C. &0 <= C /\
     !s0 t0 (tau:real^N->real^M) (c:num->real^N->real^Q) (g:real^M->real^P) y.
       open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
       (!q. smooth_map_on s0 (c q)) /\ smooth_map_on t0 g /\ y IN s0 /\
       (!q. 1 <= q /\ q <= dimindex(:P) ==> pde_jetn m (c q) y <= B) /\
       (!i. 1 <= i /\ i <= dimindex(:N) ==> pde_jetn m (partial_derivative i tau) y <= B)
       ==> pde_jetn m (\y. vsum(1..dimindex(:P)) (\q. (g(tau y))$q % c q y)) y
           <= C * pde_jetn m g (tau y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(GEN `n:num` (SPECL [`n:num`; `B:real`]
    (INST_TYPE [`:N`,`:N`; `:M`,`:M`; `:P`,`:P`; `:Q`,`:Q`] P2CT_FORM_JET_UNIFORM))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cf:num->real` (LABEL_TAC "cf")) THEN
  EXISTS_TAC `&(CARD(pde_index_lists m (:N))) * sum(0..m) (\n. (Cf:num->real) n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [pde_jetn] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC SUM_BOUND THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN
  REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Cf:num->real) (LENGTH(l:num list)) *
              pde_jetn (LENGTH l) (g:real^M->real^P) ((tau:real^N->real^M) y)` THEN
  CONJ_TAC THENL
   [REMOVE_THEN "cf" (MP_TAC o SPEC `LENGTH(l:num list)`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
                               `c:num->real^N->real^Q`; `g:real^M->real^P`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `pde_jetn m ((c:num->real^N->real^Q) q) y`;
        EXISTS_TAC `pde_jetn m (partial_derivative q (tau:real^N->real^M)) y`] THEN
      ASM_SIMP_TAC[PDE_JETN_MONO];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PDE_JETN_POS; PDE_JETN_MONO] THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  MP_TAC(ISPECL [`{LENGTH(l:num list)}`; `0..m`; `\n. (Cf:num->real) n`] SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SING_SUBSET; IN_NUMSEG; LE_0] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The second-derivative identity of an isometry T from (U',G) to (U,H)     *)
(* (G the pullback of H by T on U'), from LCHRISTOFFEL_PULLBACK:             *)
(*   d_i d_j T = sum_k Gamma(G)_ij^k d_k T                                   *)
(*               - sum_b sum_c (d_i T)_b (d_j T)_c Gamma(H)(T)(e_b,e_c).     *)
(* ------------------------------------------------------------------------- *)

let P2CT_LINEAR_BASIS_EXPAND = prove
 (`!(L:real^N->real^M) x.
     linear L ==> L x = vsum(1..dimindex(:N)) (\k. x$k % L(basis k))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]);;

let P2CT_BILINEAR_BASIS_EXPAND = prove
 (`!(bb:real^N->real^N->real^P) x y.
     bilinear bb
     ==> bb x y = vsum(1..dimindex(:N)) (\b. vsum(1..dimindex(:N)) (\c.
                    (x$b * y$c) % bb (basis b) (basis c)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM BASIS_EXPANSION] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[BILINEAR_LSUM; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[BILINEAR_RSUM; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[BILINEAR_LMUL; BILINEAR_RMUL] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `c:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let P2CT_ISOM_HESSIAN = prove
 (`!U' U (Tm:real^N->real^N) Ti G H y i j.
     diffeomorphism_on U' U Tm Ti /\ metric_field U H /\
     (!z. z IN U' ==> G z = mpullback Tm H z) /\ y IN U'
     ==> partial_derivative i (partial_derivative j Tm) y =
         vsum(1..dimindex(:N)) (\k. (christoffel G y (basis i) (basis j))$k %
                                    partial_derivative k Tm y) -
         vsum(1..dimindex(:N)) (\b. vsum(1..dimindex(:N)) (\c.
           ((partial_derivative i Tm y)$b * (partial_derivative j Tm y)$c) %
           christoffel H (Tm y) (basis b) (basis c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(Tm:real^N->real^N) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Tm:real^N->real^N) y IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `Tm:real^N->real^N`;
                 `Ti:real^N->real^N`; `H:real^N->real^N^N`; `y:real^N`;
                 `basis i:real^N`; `basis j:real^N`] LCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `christoffel (mpullback (Tm:real^N->real^N) H) y (basis i) (basis j) =
                christoffel (G:real^N->real^N^N) y (basis i) (basis j)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[dd2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (VECTOR_ARITH `(a:real^N) = b + c ==> c = a - b`)) THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC P2CT_LINEAR_BASIS_EXPAND THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CT_BILINEAR_BASIS_EXPAND THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The two terms of the second-derivative identity, and the                 *)
(* bootstrap: the jets of order m of the first partials of an isometry are  *)
(* bounded by the jets of order m+1 of both metrics, the norms of their     *)
(* inverses and a bound on the first partials (P2CT_ISOM_JET).              *)
(* ------------------------------------------------------------------------- *)

let P2CT_JETN_LIFT_COMPONENT = prove
 (`!n s (f:real^N->real^Q) k y.
     open s /\ smooth_map_on s f /\ y IN s /\ 1 <= k /\ k <= dimindex(:Q)
     ==> pde_jetn n (\z. lift(f z$k)) y <= pde_jetn n f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `\v:real^Q. lift(v$k)`; `&1`; `s:real^N->bool`;
                 `f:real^N->real^Q`; `y:real^N`] P2CT_JETN_LINEAR) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
    ASM_SIMP_TAC[NORM_LIFT; COMPONENT_LE_NORM]]);;

let P2CT_JETN_DROP_MUL = prove
 (`!n s (a:real^N->real^1) (v:real^N->real^Q) y.
     open s /\ smooth_map_on s a /\ smooth_map_on s v /\ y IN s
     ==> pde_jetn n (\z. drop(a z) % v z) y <=
         &(CARD(pde_index_lists n (:N))) * &2 pow n * &1 * pde_jetn n a y * pde_jetn n v y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(x:real^1) (w:real^Q). drop x % w`; `&1`; `s:real^N->bool`; `n:num`;
                 `a:real^N->real^1`; `v:real^N->real^Q`; `y:real^N`] P2CT_BILINEAR_JETN) THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL; REAL_POS] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[NORM_MUL; GSYM NORM_1; REAL_MUL_LID; REAL_LE_REFL]);;

let P2CT_JETN_LIFT_MUL = prove
 (`!n s (a:real^N->real^1) (b:real^N->real^1) y.
     open s /\ smooth_map_on s a /\ smooth_map_on s b /\ y IN s
     ==> pde_jetn n (\z. lift(drop(a z) * drop(b z))) y <=
         &(CARD(pde_index_lists n (:N))) * &2 pow n * &1 * pde_jetn n a y * pde_jetn n b y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(x:real^1) (w:real^1). lift(drop x * drop w)`; `&1`; `s:real^N->bool`;
                 `n:num`; `a:real^N->real^1`; `b:real^N->real^1`; `y:real^N`]
                P2CT_BILINEAR_JETN) THEN
  ASM_REWRITE_TAC[BILINEAR_LIFT_MUL; REAL_POS] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[NORM_LIFT; REAL_ABS_MUL; GSYM NORM_1; REAL_MUL_LID; REAL_LE_REFL]);;

let P2CT_JETN_CONST_BASIS = prove
 (`!n q (y:real^N). 1 <= q /\ q <= dimindex(:Q)
     ==> pde_jetn n (\z:real^N. basis q:real^Q) y <= &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_jetn; P2CT_ITERATED_PARTIAL_CONST; COND_RATOR; COND_RAND] THEN
  ASM_SIMP_TAC[NORM_BASIS; NORM_0; SUM_DELTA] THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let P2CT_HESS_FIRST_JET = prove
 (`!n s (Gam:real^N->real^N) (D:num->real^N->real^N) y CG CT.
     open s /\ smooth_map_on s Gam /\ (!k. smooth_map_on s (D k)) /\ y IN s /\
     pde_jetn n Gam y <= CG /\
     (!k. 1 <= k /\ k <= dimindex(:N) ==> pde_jetn n (D k) y <= CT)
     ==> pde_jetn n (\z. vsum(1..dimindex(:N)) (\k. Gam z$k % D k z)) y <=
         &(dimindex(:N)) * (&(CARD(pde_index_lists n (:N))) * &2 pow n * &1 * CG * CT)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. smooth_map_on s (\z. lift((Gam:real^N->real^N) z$k))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. smooth_map_on s (\z. (Gam:real^N->real^N) z$k % (D:num->real^N->real^N) k z)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\(x:real^1) (w:real^N). drop x % w`;
                   `\z. lift((Gam:real^N->real^N) z$k)`; `(D:num->real^N->real^N) k`]
                  SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\k. pde_jetn n (\z. (Gam:real^N->real^N) z$k % (D:num->real^N->real^N) k z) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `s:real^N->bool`; `1..dimindex(:N)`;
                   `\k z. (Gam:real^N->real^N) z$k % (D:num->real^N->real^N) k z`;
                   `y:real^N`] P2CT_JETN_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\k. &(CARD(pde_index_lists n (:N))) * &2 pow n * &1 * CG * CT)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`n:num`; `s:real^N->bool`; `\z. lift((Gam:real^N->real^N) z$k)`;
                   `(D:num->real^N->real^N) k`; `y:real^N`] P2CT_JETN_DROP_MUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PDE_JETN_POS] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn n (Gam:real^N->real^N) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CT_JETN_LIFT_COMPONENT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);;

let P2CT_HESS_SECOND_JET = prove
 (`!n B'. ?C. &0 <= C /\
     !s0 t0 (Tm:real^N->real^N) (g:real^N->real^N) (p:real^N->real^1) y.
       open s0 /\ open t0 /\ smooth_map_on s0 Tm /\ IMAGE Tm s0 SUBSET t0 /\
       smooth_map_on t0 g /\ smooth_map_on s0 p /\ y IN s0 /\
       pde_jetn n p y <= B' /\
       (!i. 1 <= i /\ i <= dimindex(:N) ==> pde_jetn n (partial_derivative i Tm) y <= B')
       ==> pde_jetn n (\z. drop(p z) % g(Tm z)) y <= C * pde_jetn n g (Tm y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `max B' (&(CARD(pde_index_lists n (:N))) * &2 pow n * &1 * B' * &1)`]
    (INST_TYPE [`:N`,`:M`; `:N`,`:P`; `:N`,`:Q`] P2CT_FORM_JETN_UNIFORM)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fb")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. drop((p:real^N->real^1) z) % (g:real^N->real^N)((Tm:real^N->real^N) z)) =
    (\z. vsum(1..dimindex(:N)) (\q. (g(Tm z))$q % (\q z. drop(p z) % basis q) q z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    REWRITE_TAC[GSYM VSUM_LMUL] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "fb" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`s0:real^N->bool`; `t0:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `q:num` THEN
    MP_TAC(ISPECL [`s0:real^N->bool`; `\(x:real^1) (w:real^N). drop x % w`;
                   `p:real^N->real^1`; `\z:real^N. basis q:real^N`]
                  SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_REWRITE_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_CONST];
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= z ==> x <= max B' z`) THEN
    MP_TAC(ISPECL [`n:num`; `s0:real^N->bool`; `p:real^N->real^1`;
                   `\z:real^N. basis q:real^N`; `y:real^N`] P2CT_JETN_DROP_MUL) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PDE_JETN_POS; P2CT_JETN_CONST_BASIS];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= B' ==> x <= max B' z`) THEN ASM_SIMP_TAC[]]);;

let P2CT_ISOM_STEP = prove
 (`!m U' U (Tm:real^N->real^N) Ti G H y i j C0 Cc C2.
     diffeomorphism_on U' U Tm Ti /\ metric_field U H /\
     (!z. z IN U' ==> G z = mpullback Tm H z) /\ y IN U' /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
     (!k. 1 <= k /\ k <= dimindex(:N) ==> pde_jetn m (partial_derivative k Tm) y <= C0) /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on U' (\z. christoffel G z (basis a) (basis b)) /\
                pde_jetn m (\z. christoffel G z (basis a) (basis b)) y <= Cc /\
                smooth_map_on U (\x. christoffel H x (basis a) (basis b)) /\
                pde_jetn m (\x. christoffel H x (basis a) (basis b)) (Tm y) <= Cc) /\
     (!(p:real^N->real^1) (g:real^N->real^N).
          smooth_map_on U g /\ smooth_map_on U' p /\
          pde_jetn m p y <= max C0 (&(CARD(pde_index_lists m (:N))) * &2 pow m * &1 * C0 * C0)
          ==> pde_jetn m (\z. drop(p z) % g(Tm z)) y <= C2 * pde_jetn m g (Tm y)) /\
     &0 <= C2
     ==> pde_jetn m (partial_derivative j (partial_derivative i Tm)) y <=
         &(dimindex(:N)) * (&(CARD(pde_index_lists m (:N))) * &2 pow m * &1 * Cc * C0) +
         &(dimindex(:N)) * (&(dimindex(:N)) * (C2 * Cc))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "c0") (CONJUNCTS_THEN2 (LABEL_TAC "cc")
   (CONJUNCTS_THEN2 (LABEL_TAC "c2") ASSUME_TAC))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!k. smooth_map_on U' (partial_derivative k (Tm:real^N->real^N))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the identity on U' *)
  ABBREV_TAC `A = \z. vsum(1..dimindex(:N))
                        (\k. (christoffel (G:real^N->real^N^N) z (basis j) (basis i))$k %
                             partial_derivative k (Tm:real^N->real^N) z)` THEN
  ABBREV_TAC `Bt = \z. vsum(1..dimindex(:N)) (\b. vsum(1..dimindex(:N)) (\c.
                         ((partial_derivative j (Tm:real^N->real^N) z)$b *
                          (partial_derivative i Tm z)$c) %
                         christoffel (H:real^N->real^N^N) (Tm z) (basis b) (basis c)))` THEN
  SUBGOAL_THEN
   `pde_jetn m (partial_derivative j (partial_derivative i (Tm:real^N->real^N))) y =
    pde_jetn m (\z. (A:real^N->real^N) z + --((Bt:real^N->real^N) z)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["A"; "Bt"] THEN
    MP_TAC(ISPECL [`U':real^N->bool`; `U:real^N->bool`; `Tm:real^N->real^N`;
                   `Ti:real^N->real^N`; `G:real^N->real^N^N`; `H:real^N->real^N^N`;
                   `z:real^N`; `j:num`; `i:num`] P2CT_ISOM_HESSIAN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_SUB];
    ALL_TAC] THEN
  (* smoothness of the pieces *)
  SUBGOAL_THEN
   `!b c. 1 <= b /\ b <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
          ==> smooth_map_on U'
                (\z. lift((partial_derivative j (Tm:real^N->real^N) z)$b *
                          (partial_derivative i Tm z)$c)) /\
              smooth_map_on U'
                (\z. ((partial_derivative j (Tm:real^N->real^N) z)$b *
                      (partial_derivative i Tm z)$c) %
                     christoffel (H:real^N->real^N^N) (Tm z) (basis b) (basis c))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `smooth_map_on U'
        (\z. lift((partial_derivative j (Tm:real^N->real^N) z)$b *
                  (partial_derivative i Tm z)$c))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`U':real^N->bool`;
                     `\z. lift((partial_derivative j (Tm:real^N->real^N) z)$b)`;
                     `\z. lift((partial_derivative i (Tm:real^N->real^N) z)$c)`]
                    SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; LIFT_DROP; ETA_AX];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U':real^N->bool`; `\(x:real^1) (w:real^N). drop x % w`;
                   `\z. lift((partial_derivative j (Tm:real^N->real^N) z)$b *
                             (partial_derivative i Tm z)$c)`;
                   `(\x. christoffel (H:real^N->real^N^N) x (basis b) (basis c)) o
                    (Tm:real^N->real^N)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[SUBSET_REFL] THEN USE_THEN "cc" (MP_TAC o SPECL [`b:num`; `c:num`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U' (A:real^N->real^N) /\ smooth_map_on U' (Bt:real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "Bt"] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THENL
     [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U':real^N->bool`; `\(x:real^1) (w:real^N). drop x % w`;
                     `\z. lift((christoffel (G:real^N->real^N^N) z (basis j) (basis i))$k)`;
                     `partial_derivative k (Tm:real^N->real^N)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[ETA_AX] THEN
      USE_THEN "cc" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `b:num` THEN STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn m (A:real^N->real^N) y + pde_jetn m (\z. --((Bt:real^N->real^N) z)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_ADD THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_NEG_OPEN; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [EXPAND_TAC "A" THEN
    MP_TAC(ISPECL [`m:num`; `U':real^N->bool`;
                   `\z. christoffel (G:real^N->real^N^N) z (basis j) (basis i)`;
                   `\k. partial_derivative k (Tm:real^N->real^N)`; `y:real^N`;
                   `Cc:real`; `C0:real`] P2CT_HESS_FIRST_JET) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cc" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "c0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn m (Bt:real^N->real^N) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_NEG THEN EXISTS_TAC `U':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "Bt" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\b. pde_jetn m (\z. vsum(1..dimindex(:N)) (\c.
      ((partial_derivative j (Tm:real^N->real^N) z)$b * (partial_derivative i Tm z)$c) %
      christoffel (H:real^N->real^N^N) (Tm z) (basis b) (basis c))) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `U':real^N->bool`; `1..dimindex(:N)`;
                   `\b z. vsum(1..dimindex(:N)) (\c.
                      ((partial_derivative j (Tm:real^N->real^N) z)$b *
                       (partial_derivative i Tm z)$c) %
                      christoffel (H:real^N->real^N^N) (Tm z) (basis b) (basis c))`;
                   `y:real^N`] P2CT_JETN_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\b:num. &(dimindex(:N)) * (C2 * Cc))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\c. pde_jetn m (\z.
      ((partial_derivative j (Tm:real^N->real^N) z)$b * (partial_derivative i Tm z)$c) %
      christoffel (H:real^N->real^N^N) (Tm z) (basis b) (basis c)) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `U':real^N->bool`; `1..dimindex(:N)`;
                   `\c z. ((partial_derivative j (Tm:real^N->real^N) z)$b *
                           (partial_derivative i Tm z)$c) %
                          christoffel (H:real^N->real^N^N) (Tm z) (basis b) (basis c)`;
                   `y:real^N`] P2CT_JETN_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\c:num. C2 * Cc)` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "c2" (MP_TAC o SPECL
    [`\z. lift((partial_derivative j (Tm:real^N->real^N) z)$b * (partial_derivative i Tm z)$c)`;
     `\x. christoffel (H:real^N->real^N^N) x (basis b) (basis c)`]) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "cc" (MP_TAC o SPECL [`b:num`; `c:num`]) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= z ==> x <= max B z`) THEN
    MP_TAC(ISPECL [`m:num`; `U':real^N->bool`;
                   `\z. lift((partial_derivative j (Tm:real^N->real^N) z)$b)`;
                   `\z. lift((partial_derivative i (Tm:real^N->real^N) z)$c)`; `y:real^N`]
                  P2CT_JETN_LIFT_MUL) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `pde_jetn m (partial_derivative j (Tm:real^N->real^N)) y`;
      EXISTS_TAC `pde_jetn m (partial_derivative i (Tm:real^N->real^N)) y`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC P2CT_JETN_LIFT_COMPONENT THEN EXISTS_TAC `U':real^N->bool` THEN
       ASM_REWRITE_TAC[];
       ASM_SIMP_TAC[]]);
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "cc" (MP_TAC o SPECL [`b:num`; `c:num`]) THEN ASM_SIMP_TAC[]);;

let P2CT_ISOM_JET = prove
 (`!m B L Lam. ?C. &0 <= C /\
     !U' U (Tm:real^N->real^N) Ti G H y.
       diffeomorphism_on U' U Tm Ti /\ metric_field U H /\ metric_field U' G /\
       (!z. z IN U' ==> G z = mpullback Tm H z) /\ y IN U' /\
       pde_jetn (SUC m) (vectorize o G) y <= B /\ norm(vectorize(matrix_inv(G y))) <= L /\
       pde_jetn (SUC m) (vectorize o H) (Tm y) <= B /\
       norm(vectorize(matrix_inv(H (Tm y)))) <= L /\
       (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(partial_derivative i Tm y) <= Lam)
       ==> !i. 1 <= i /\ i <= dimindex(:N) ==> pde_jetn m (partial_derivative i Tm) y <= C`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN EXISTS_TAC `abs Lam` THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[P2CT_JETN_0] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= l ==> x <= abs l`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih")) o
                SPECL [`B:real`; `L:real`; `Lam:real`]) THEN
  MP_TAC(ISPECL [`m:num`; `B:real`; `L:real`] P2CT_CHRISTOFFEL_JET) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cj"))) THEN
  MP_TAC(ISPECL [`m:num`;
                 `max C0 (&(CARD(pde_index_lists m (:N))) * &2 pow m * &1 * C0 * C0)`]
                P2CT_HESS_SECOND_JET) THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c2"))) THEN
  EXISTS_TAC `abs Lam + &(CARD(pde_index_lists (SUC m) (:N))) *
              sum(1..dimindex(:N))
                (\j. &(dimindex(:N)) *
                     (&(CARD(pde_index_lists m (:N))) * &2 pow m * &1 * Cc * C0) +
                     &(dimindex(:N)) * (&(dimindex(:N)) * (C2 * Cc)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U':real^N->bool`; `U:real^N->bool`; `Tm:real^N->real^N`;
                       `Ti:real^N->real^N`; `G:real^N->real^N^N`; `H:real^N->real^N^N`;
                       `y:real^N`] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(Tm:real^N->real^N) y IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U' (vectorize o (G:real^N->real^N^N)) /\
    (!z. z IN U' ==> ~(det(G z) = &0)) /\
    smooth_map_on U (vectorize o (H:real^N->real^N^N)) /\
    (!z. z IN U ==> ~(det(H z) = &0))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
      ASM_MESON_TAC[metric_field]; ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> pde_jetn m (partial_derivative k (Tm:real^N->real^N)) y <= C0`
  ASSUME_TAC THENL
   [REMOVE_THEN "ih" (MP_TAC o SPECL
      [`U':real^N->bool`; `U:real^N->bool`; `Tm:real^N->real^N`; `Ti:real^N->real^N`;
       `G:real^N->real^N^N`; `H:real^N->real^N^N`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `pde_jetn (SUC(SUC m)) (vectorize o (G:real^N->real^N^N)) y`;
      EXISTS_TAC `pde_jetn (SUC(SUC m)) (vectorize o (H:real^N->real^N^N))
                            ((Tm:real^N->real^N) y)`] THEN
    ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `SUC m <= SUC(SUC m)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn (SUC m) (vectorize o (G:real^N->real^N^N)) y <= B /\
    pde_jetn (SUC m) (vectorize o (H:real^N->real^N^N)) ((Tm:real^N->real^N) y) <= B`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `pde_jetn (SUC(SUC m)) (vectorize o (G:real^N->real^N^N)) y`;
      EXISTS_TAC `pde_jetn (SUC(SUC m)) (vectorize o (H:real^N->real^N^N))
                            ((Tm:real^N->real^N) y)`] THEN
    ASM_SIMP_TAC[PDE_JETN_MONO; ARITH_RULE `SUC m <= SUC(SUC m)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> smooth_map_on U' (\z. christoffel (G:real^N->real^N^N) z (basis a) (basis b)) /\
              pde_jetn m (\z. christoffel G z (basis a) (basis b)) y <= Cc /\
              smooth_map_on U (\x. christoffel (H:real^N->real^N^N) x (basis a) (basis b)) /\
              pde_jetn m (\x. christoffel H x (basis a) (basis b))
                       ((Tm:real^N->real^N) y) <= Cc`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REMOVE_THEN "cj" (fun th ->
      MP_TAC(SPECL [`U':real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:num`; `b:num`] th) THEN
      MP_TAC(SPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `(Tm:real^N->real^N) y`;
                    `a:num`; `b:num`] th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(p:real^N->real^1) (g:real^N->real^N).
       smooth_map_on U g /\ smooth_map_on U' p /\
       pde_jetn m p y <= max C0 (&(CARD(pde_index_lists m (:N))) * &2 pow m * &1 * C0 * C0)
       ==> pde_jetn m (\z. drop(p z) % g((Tm:real^N->real^N) z)) y <=
           C2 * pde_jetn m g (Tm y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REMOVE_THEN "c2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`U':real^N->bool`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(partial_derivative i (Tm:real^N->real^N) y) +
              &(CARD(pde_index_lists (SUC m) (:N))) *
              sum(1..dimindex(:N))
                (\j. pde_jetn m (partial_derivative j (partial_derivative i Tm)) y)` THEN
  REWRITE_TAC[P2CT_JETN_SUC_BOUND] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= l ==> x <= abs l`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CT_ISOM_STEP THEN
    MAP_EVERY EXISTS_TAC [`U':real^N->bool`; `U:real^N->bool`; `Ti:real^N->real^N`;
                          `G:real^N->real^N^N`; `H:real^N->real^N^N`] THEN
    ASM_REWRITE_TAC[]]);;

