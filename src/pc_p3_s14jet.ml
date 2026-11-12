(* ========================================================================= *)
(* Unit pc_p3_s14jet (Part 3 proofs; MT Lemma 14.11 support):               *)
(* the jet hypothesis of PDE_GLUE at a surgery event.  Covariant C^m        *)
(* closeness in one chart implies convergence of the coordinate jets        *)
(* (P3S_LCK_JET_CONV, via RFA_COORD_JET and a normalized sequence), lck     *)
(* distances transfer between charts of two atlases that the identity makes *)
(* diffeomorphic (P3S_LCK_TRANSFER), and at an event the chart jets of the  *)
(* glued family converge on compacts (P3S_EVENT_JETS).                      *)
(* ========================================================================= *)

needs "src/pc_p3_s14ftr.ml";;
needs "src/pc_rfa_r1.ml";;
needs "src/pc_rf_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* From covariant C^m closeness to convergence of coordinate                *)
(* jets in one chart.  A fixed smooth function has bounded jets on a        *)
(* compact set; uniform entry jet bounds of a smooth matrix family bound    *)
(* the vectorized iterated partials; and P3S_LCK_JET_CONV: if lck_dist2 m   *)
(* G0 (G t) tends to 0 uniformly on a compact K as t -> ts-, then every     *)
(* iterated partial of order m of the chart matrices converges uniformly on *)
(* K (by contradiction: a normalized sequence of differences has bounded    *)
(* covariant jets, hence bounded coordinate jets by RFA_COORD_JET).         *)
(* ------------------------------------------------------------------------- *)

let P3S_JB_FIXED = prove
 (`!(Js:real->bool) V K m (f:real^N->real).
     open V /\ compact K /\ K SUBSET V /\ smooth_map_on V (\z. lift(f z))
     ==> rfa_jb Js V K m (\t z. f z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_jb] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!l. ?C. !y. y IN K
                ==> abs(drop(iterated_partial l (\z. lift((f:real^N->real) z)) y)) <= C`
  MP_TAC THENL
   [X_GEN_TAC `l:num list` THEN
    MP_TAC(ISPECL [`iterated_partial l (\z. lift((f:real^N->real) z))`; `K:real^N->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; GSYM NORM_1] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `Cl:num list->real`) THEN
  EXISTS_TAC `sum (pde_index_lists m (:N)) (\l. abs((Cl:num list->real) l))` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Cl:num list->real) l)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= abs c`) THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`\l. abs((Cl:num list->real) l)`;
                   `sum (pde_index_lists m (:N)) (\l. abs((Cl:num list->real) l))`;
                   `pde_index_lists m (:N)`] SUM_POS_BOUND) THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE; REAL_ABS_POS; REAL_LE_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* RFA_JB_VEC_NORM of pc_rfa_r1 for smooth matrix families (not only metric *)
(* fields); the proof is that of RFA_JB_VEC_NORM.                           *)

let P3S_JB_VEC_NORM = prove
 (`!Js V K m (Gc:real->real^N->real^N^N).
     open V /\ K SUBSET V /\
     (!t. t IN Js
          ==> smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o Gc t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K m (\t z. Gc t z$p$q))
     ==> ?C. !t l y. t IN Js /\ l IN pde_index_lists m (:N) /\ y IN K
                     ==> norm(iterated_partial l
                                ((vectorize:real^N^N->real^(N,N)finite_prod) o Gc t) y) <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (LABEL_TAC "jb")))) THEN
  SUBGOAL_THEN
   `!p q. ?C. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> !t l y. t IN Js /\ l IN pde_index_lists m (:N) /\ y IN K
                          ==> abs(drop(iterated_partial l
                                   (\z. lift((Gc:real->real^N->real^N^N) t z$p$q)) y)) <= C`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `rfa_jb Js V K m (\t z. (Gc:real->real^N->real^N^N) t z$p$q)` MP_TAC THENL
     [USE_THEN "jb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfa_jb] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cp:num->num->real` (LABEL_TAC "cp")) THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                (\k. (Cp:num->num->real) (1 + (k - 1) DIV dimindex(:N))
                                         (1 + (k - 1) MOD dimindex(:N)))` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET (V:real^N->bool)` THEN UNDISCH_TAC `(y:real^N) IN K` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                 (Gc:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                (\k. abs((iterated_partial l
                         ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          (Gc:real->real^N->real^N^N) t) y)$k))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `1 <= 1 + (k - 1) DIV dimindex(:N) /\ 1 + (k - 1) DIV dimindex(:N) <= dimindex(:N) /\
    1 <= 1 + (k - 1) MOD dimindex(:N) /\ 1 + (k - 1) MOD dimindex(:N) <= dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= 1 + a`] THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `a < b ==> 1 + a <= b`) THEN
    SIMP_TAC[DIVISION; LE_1; DIMINDEX_GE_1; RDIV_LT_EQ] THEN
    UNDISCH_TAC `k <= dimindex(:(N,N)finite_prod)` THEN
    UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (Gc:real->real^N->real^N^N) t`;
                 `k:num`; `y:real^N`] RFA_ITERATED_PARTIAL_LIFT_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(\z. lift((((vectorize:real^N^N->real^(N,N)finite_prod) o
                (Gc:real->real^N->real^N^N) t) z)$k)) =
    (\z. lift(Gc t z$(1 + (k - 1) DIV dimindex(:N))$(1 + (k - 1) MOD dimindex(:N))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VECTORIZE_COMPONENT THEN
    UNDISCH_TAC `k <= dimindex(:(N,N)finite_prod)` THEN
    UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "cp" (MP_TAC o SPECL [`1 + (k - 1) DIV dimindex(:N)`;
                                 `1 + (k - 1) MOD dimindex(:N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3S_LMETRIC2_BASIS = prove
 (`!(G:real^N->real^N^N) z p q.
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> lmetric2 G z (\r. basis(if r = 1 then p else if r = 2 then q else 0)) =
         G z$p$q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lmetric2; ARITH_RULE `~(2 = 1)`] THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let P3S_PAIR_INDEX_TUPLE = prove
 (`!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
         ==> (\r. if r = 1 then p else if r = 2 then q else 0) IN index_tuples 2 (:N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `r = 1 \/ r = 2` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[ARITH_RULE `~(2 = 1)`];
      ASM_REWRITE_TAC[ARITH_RULE `~(2 = 1)`]];
    SUBGOAL_THEN `~(r = 1) /\ ~(r = 2)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;


let P3S_NORMALIZED_JET = prove
 (`!V K (G0:real^N->real^N^N) (H:num->real^N->real^N^N) m.
     metric_field V G0 /\ compact K /\ K SUBSET V /\
     (!n. metric_field V (H n)) /\
     (!n y. y IN K ==> lck_dist2 m G0 (H n) y < inv(&n + &1) pow 2)
     ==> ?C. !n l y. l IN pde_index_lists m (:N) /\ y IN K
                     ==> norm(iterated_partial l
                                ((vectorize:real^N^N->real^(N,N)finite_prod) o H n) y -
                              iterated_partial l (vectorize o G0) y) <= C * inv(&n + &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "MF") (LABEL_TAC "LCK"))))) THEN
  SUBGOAL_THEN `open (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?L. &0 <= L /\ !y p. y IN K /\ 1 <= p /\ p <= dimindex(:N)
                         ==> (G0:real^N->real^N^N) y$p$p <= L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!p. ?C. 1 <= p /\ p <= dimindex(:N)
              ==> !y. y IN K ==> (G0:real^N->real^N^N) y$p$p <= C`
    MP_TAC THENL
     [X_GEN_TAC `p:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`{&0}`; `V:real^N->bool`; `K:real^N->bool`; `0`;
                     `\z. (G0:real^N->real^N^N) z$p$p`] P3S_JB_FIXED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`V:real^N->bool`; `G0:real^N->real^N^N`] LRG_SMOOTH_VECTORIZE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[rfa_jb] THEN
      DISCH_THEN(X_CHOOSE_TAC `C:real` o CONJUNCT2) THEN EXISTS_TAC `C:real` THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `[]:num list`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[IN_SING; pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0;
                      iterated_partial; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `Cp:num->real`) THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\p. abs((Cp:num->real) p))` THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_ABS_POS] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `p:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Cp:num->real) p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= abs c`) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`\p. abs((Cp:num->real) p)`;
                     `sum(1..dimindex(:N)) (\p. abs((Cp:num->real) p))`;
                     `1..dimindex(:N)`] SUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS; REAL_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]];
    ALL_TAC] THEN
  ABBREV_TAC `Js = IMAGE (\n. inv(&n + &1)) (:num)` THEN
  ABBREV_TAC `nx = \x:real. @n. x = inv(&n + &1)` THEN
  SUBGOAL_THEN `!n. (nx:real->num) (inv(&n + &1)) = n` (LABEL_TAC "NX") THENL
   [GEN_TAC THEN EXPAND_TAC "nx" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC[REAL_EQ_INV2; REAL_EQ_ADD_RCANCEL; REAL_OF_NUM_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = \n:num. \z:real^N. \u:num->real^N.
          lmetric2 ((H:num->real^N->real^N^N) n) z u - lmetric2 (G0:real^N->real^N^N) z u` THEN
  ABBREV_TAC
   `Tf = \x:real. \z:real^N. \u:num->real^N.
           (&((nx:real->num) x) + &1) * (D:num->real^N->(num->real^N)->real) (nx x) z u` THEN
  SUBGOAL_THEN
   `!n. ltensor_field 2 V ((D:num->real^N->(num->real^N)->real) n) /\
        (!u. smooth_map_on V (\z. lift(D n z u)))`
  (LABEL_TAC "DF") THENL
   [GEN_TAC THEN EXPAND_TAC "D" THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `G0:real^N->real^N^N`;
                   `(H:num->real^N->real^N^N) n`] LRG_LMETRIC2_DIFF_FIELD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ltensor_field 2 V ((Tf:real->real^N->(num->real^N)->real) x) /\
        (!u. smooth_map_on V (\z. lift(Tf x z u)))`
  (LABEL_TAC "TFF") THENL
   [GEN_TAC THEN EXPAND_TAC "Tf" THEN REWRITE_TAC[] THEN
    USE_THEN "DF" (STRIP_ASSUME_TAC o SPEC `(nx:real->num) x`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`2`; `V:real^N->bool`;
                     `(D:num->real^N->(num->real^N)->real) ((nx:real->num) x)`;
                     `&((nx:real->num) x) + &1`] LRG_TENSOR_FIELD_CMUL) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[LIFT_CMUL] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n j z u. z IN V
              ==> lnabla_iter 2 j (G0:real^N->real^N^N)
                    ((Tf:real->real^N->(num->real^N)->real) (inv(&n + &1))) z u =
                  (&n + &1) * lnabla_iter 2 j G0
                                ((D:num->real^N->(num->real^N)->real) n) z u`
  (LABEL_TAC "LIN") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(Tf:real->real^N->(num->real^N)->real) (inv(&n + &1)) =
      (\z u. (&n + &1) * (D:num->real^N->(num->real^N)->real) n z u + &0 * D n z u)`
    SUBST1_TAC THENL
     [EXPAND_TAC "Tf" THEN USE_THEN "NX" (fun th -> REWRITE_TAC[th; FUN_EQ_THM]) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "DF" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`2`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                   `(D:num->real^N->(num->real^N)->real) n`;
                   `(D:num->real^N->(num->real^N)->real) n`;
                   `&n + &1`; `&0`] LRG_LNABLA_ITER_LINCOMB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`j:num`; `z:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n j y. j <= m /\ y IN K
            ==> ltnorm2 (2 + j) (G0:real^N->real^N^N)
                  (lnabla_iter 2 j G0 ((Tf:real->real^N->(num->real^N)->real) (inv(&n + &1)))) y
                <= &1`
  (LABEL_TAC "NB") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `ltnorm2 (2 + j) (G0:real^N->real^N^N)
        (\z u. (&n + &1) * lnabla_iter 2 j G0 ((D:num->real^N->(num->real^N)->real) n) z u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LRG_LTNORM2_CMUL] THEN
    TRANS_TAC REAL_LE_TRANS
     `(&n + &1) pow 2 * lck_dist2 m (G0:real^N->real^N^N) ((H:num->real^N->real^N^N) n) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      EXPAND_TAC "D" THEN BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC LRG_LCK_DIST2_TERM_LE THEN
      EXISTS_TAC `V:real^N->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `lck_dist2 m (G0:real^N->real^N^N) ((H:num->real^N->real^N^N) n) y <
      inv(&n + &1) pow 2`
    ASSUME_TAC THENL
     [USE_THEN "LCK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    TRANS_TAC REAL_LTE_TRANS `(&n + &1) pow 2 * inv(&n + &1) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_MUL] THEN
      SIMP_TAC[REAL_MUL_RINV; REAL_ARITH `~(&n + &1 = &0)`] THEN
      REWRITE_TAC[REAL_POW_ONE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `2`; `\x:real. (G0:real^N->real^N^N)`;
                 `Tf:real->real^N->(num->real^N)->real`; `Js:real->bool`;
                 `V:real^N->bool`; `K:real^N->bool`] RFA_COORD_JET) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`j:num`; `al:num->num`] THEN STRIP_TAC THEN
        REWRITE_TAC[RFA_JB_ZERO] THEN CONJ_TAC THENL
         [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
          USE_THEN "TFF" (STRIP_ASSUME_TAC o SPEC `x:real`) THEN
          MP_TAC(ISPECL [`2`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                         `(Tf:real->real^N->(num->real^N)->real) x`] LRG_LNABLA_ITER_FIELD) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `&1 * L pow (2 + j) + &1` THEN
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real^N`] THEN
        EXPAND_TAC "Js" THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` SUBST1_TAC) ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        USE_THEN "TFF" (STRIP_ASSUME_TAC o SPEC `inv(&n + &1)`) THEN
        MP_TAC(ISPECL [`2`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                       `(Tf:real->real^N->(num->real^N)->real) (inv(&n + &1))`]
                      LRG_LNABLA_ITER_FIELD) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(STRIP_ASSUME_TAC o SPEC `j:num`)] THEN
        BETA_TAC THEN MATCH_MP_TAC RFA_COMP_BOUND THEN
        MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `G0:real^N->real^N^N`] THEN
        ASM_SIMP_TAC[];
        DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `s:num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC P3S_JB_FIXED THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC PDE_SMOOTH_CHR_ENTRY THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "CJ")] THEN
  ABBREV_TAC
   `DD = \x:real. \z:real^N.
           (&((nx:real->num) x) + &1) %%
           ((H:num->real^N->real^N^N) (nx x) z - (G0:real^N->real^N^N) z)` THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> rfa_jb Js V K m (\t z. (DD:real->real^N->real^N^N) t z$p$q)`
  (LABEL_TAC "DJ") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
    EXISTS_TAC
     `\t z. (Tf:real->real^N->(num->real^N)->real) t z
              (\r. basis(if r = 1 then p else if r = 2 then q else 0))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      MAP_EVERY EXPAND_TAC ["Tf"; "DD"; "D"] THEN
      ASM_SIMP_TAC[P3S_LMETRIC2_BASIS; MATRIX_CMUL_COMPONENT; MATRIX_SUB_COMPONENT];
      USE_THEN "CJ" (MP_TAC o SPEC
        `\r. if r = 1 then (p:num) else if r = 2 then q else 0`) THEN
      ASM_SIMP_TAC[P3S_PAIR_INDEX_TUPLE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`; `m:num`;
                 `DD:real->real^N->real^N^N`] P3S_JB_VEC_NORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    EXPAND_TAC "DD" THEN
    REWRITE_TAC[o_DEF; VECTORIZE_CMUL; VECTORIZE_SUB] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "MF" (MP_TAC o SPEC `(nx:real->num) x`);
      UNDISCH_TAC `metric_field V (G0:real^N->real^N^N)`] THEN
    SIMP_TAC[metric_field; o_DEF];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "VN")) THEN EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "VN" (MP_TAC o SPECL [`inv(&n + &1)`; `l:num list`; `y:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Js" THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o (DD:real->real^N->real^N^N) (inv(&n + &1)) =
    (\z. (&n + &1) % ((vectorize o (H:num->real^N->real^N^N) n) z -
                      (vectorize o (G0:real^N->real^N^N)) z))`
  SUBST1_TAC THENL
   [EXPAND_TAC "DD" THEN USE_THEN "NX" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL; VECTORIZE_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o (H:num->real^N->real^N^N) n) /\
    smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o (G0:real^N->real^N^N))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "MF" (MP_TAC o SPEC `n:num`);
      UNDISCH_TAC `metric_field V (G0:real^N->real^N^N)`] THEN
    SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `\v:real^(N,N)finite_prod. (&n + &1) % v`;
                 `\z. ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       (H:num->real^N->real^N^N) n) z -
                      (vectorize o (G0:real^N->real^N^N)) z`;
                 `V:real^N->bool`; `y:real^N`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LINEAR_SCALING] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (H:num->real^N->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (G0:real^N->real^N^N)`]
                TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_MUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(&n + &1) = &n + &1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

let P3S_LCK_JET_CONV = prove
 (`!V K (G0:real^N->real^N^N) (G:real->real^N->real^N^N) ts d0 l.
     metric_field V G0 /\ compact K /\ K SUBSET V /\ &0 < d0 /\
     (!t. ts - d0 < t /\ t < ts ==> metric_field V (G t)) /\
     (!e. &0 < e
          ==> ?d. &0 < d /\
                  !t y. ts - d < t /\ t < ts /\ y IN K
                        ==> lck_dist2 (LENGTH l) G0 (G t) y < e) /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t y. ts - d < t /\ t < ts /\ y IN K
                           ==> norm(iterated_partial l
                                      ((vectorize:real^N^N->real^(N,N)finite_prod) o G t) y -
                                    iterated_partial l (vectorize o G0) y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "MF") (CONJUNCTS_THEN2 (LABEL_TAC "LCK") ASSUME_TAC)))))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "LCK" (MP_TAC o GEN `n:num` o SPEC `inv(&n + &1) pow 2`) THEN
  SIMP_TAC[REAL_POW_LT; REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:num->real` (LABEL_TAC "DL")) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "NEG" o
    REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT]) THEN
  SUBGOAL_THEN
   `!n. ?t y. ts - min ((dl:num->real) n) d0 < t /\ t < ts /\ y IN K /\
              e <= norm(iterated_partial l
                     ((vectorize:real^N^N->real^(N,N)finite_prod) o
                      (G:real->real^N->real^N^N) t) y -
                   iterated_partial l (vectorize o G0) y)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "DL" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "NEG" (MP_TAC o SPEC `min ((dl:num->real) n) d0`) THEN
    SUBGOAL_THEN `~(min ((dl:num->real) n) d0 <= &0)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_NOT_LE; REAL_LT_MIN] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM CONJ_ASSOC]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:num->real` (X_CHOOSE_THEN `yy:num->real^N`
    (LABEL_TAC "SEQ"))) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `K:real^N->bool`; `G0:real^N->real^N^N`;
                 `\n. (G:real->real^N->real^N^N) ((tt:num->real) n)`;
                 `LENGTH (l:num list)`] P3S_NORMALIZED_JET) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "MF" MATCH_MP_TAC THEN
      USE_THEN "SEQ" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN DISCH_TAC THEN
      USE_THEN "DL" (MP_TAC o SPEC `n:num`) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "SEQ" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "CB")) THEN
  MP_TAC(SPEC `abs C / e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  USE_THEN "SEQ" (STRIP_ASSUME_TAC o SPEC `N:num`) THEN
  SUBGOAL_THEN
   `norm(iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                            (G:real->real^N->real^N^N) ((tt:num->real) N))
                         ((yy:num->real^N) N) -
         iterated_partial l (vectorize o G0) (yy N)) <= C * inv(&N + &1)`
  ASSUME_TAC THENL
   [USE_THEN "CB" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `e <= C * inv(&N + &1)` MP_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE; GSYM real_div] THEN
  SUBGOAL_THEN `&0 < &N + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  UNDISCH_TAC `abs C / e <= &N` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> abs C <= &N * e ==> C < e * (&N + &1)`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transfer of covariant C^m distances between charts of two                *)
(* atlases that the identity makes diffeomorphic on W.  Inverting a local   *)
(* pullback relation along a diffeomorphism, metric fields on open subsets, *)
(* and P3S_LCK_TRANSFER: if the first metric of the Y-chart is the pullback *)
(* of the X-chart one in the X-to-Y direction (as rfs_same_metric_on gives) *)
(* and the second in the Y-to-X direction (as the transported flow gives),  *)
(* the lck_dist2 values at the point agree.                                 *)
(* ------------------------------------------------------------------------- *)

let P3S_MPULLBACK_INVERT = prove
 (`!s s' (h:real^N->real^N) h' (A:real^N->real^N^N) B y.
     diffeomorphism_on s s' h h' /\
     (!z. z IN s ==> A z = mpullback h B z) /\ y IN s'
     ==> B y = mpullback h' A y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(h':real^N->real^N) y IN s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `mpullback (h':real^N->real^N) (mpullback h (B:real^N->real^N^N)) y` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P2A_MPULLBACK_PT THEN ASM_SIMP_TAC[]] THEN
  TRANS_TAC EQ_TRANS `mpullback ((h:real^N->real^N) o h') (B:real^N->real^N^N) y` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CF_MPULLBACK_LOCAL_ID THEN
    EXISTS_TAC `s':real^N->bool` THEN ASM_SIMP_TAC[o_THM];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_MPULLBACK_COMPOSE THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `s':real^N->bool`; EXISTS_TAC `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let P3S_METRIC_FIELD_SUBSET = prove
 (`!U U' (G:real^N->real^N^N).
     metric_field U G /\ open U' /\ U' SUBSET U ==> metric_field U' G`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let P3S_LCK_TRANSFER = prove
 (`!topY atlasY topX atlasX W (gY0:A->real^N^N) gY gX0 gX U phi V psi x k.
     smooth_manifold_atlas topY atlasY /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo topY atlasY W topX atlasX W (\x. x) (\x. x) /\
     (U,phi) IN atlasY /\ (V,psi) IN atlasX /\ x IN U /\ x IN V /\ x IN W /\
     metric_field (IMAGE psi (V INTER W)) (metric_local atlasX (V,psi) gX0) /\
     metric_field (IMAGE psi (V INTER W)) (metric_local atlasX (V,psi) gX) /\
     (!z. z IN V INTER W /\ z IN U
          ==> metric_local atlasX (V,psi) gX0 (psi z) =
              mpullback (phi o chart_inv (V,psi)) (metric_local atlasY (U,phi) gY0)
                        (psi z)) /\
     (!z. z IN U INTER W /\ z IN V
          ==> metric_local atlasY (U,phi) gY (phi z) =
              mpullback (psi o chart_inv (U,phi)) (metric_local atlasX (V,psi) gX)
                        (phi z))
     ==> lck_dist2 k (metric_local atlasY (U,phi) gY0) (metric_local atlasY (U,phi) gY)
                     (phi x) =
         lck_dist2 k (metric_local atlasX (V,psi) gX0) (metric_local atlasX (V,psi) gX)
                     (psi x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "R0") (LABEL_TAC "R1")))))))))))) THEN
  ABBREV_TAC `s = IMAGE (phi:A->real^N) {z | z IN U INTER W /\ z IN V}` THEN
  ABBREV_TAC `s' = IMAGE (psi:A->real^N) {z | z IN V INTER W /\ z IN U}` THEN
  SUBGOAL_THEN `(phi:A->real^N) x IN s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':real^N->bool) SUBSET IMAGE psi (V INTER W:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN s
        ==> metric_local atlasY (U,phi) (gY:A->real^N^N) z =
            mpullback ((psi:A->real^N) o chart_inv (U:A->bool,phi:A->real^N))
                      (metric_local atlasX (V,psi) (gX:A->real^N^N)) z`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN USE_THEN "R1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `diffeomorphism_on s s' ((psi:A->real^N) o chart_inv (U:A->bool,phi:A->real^N))
                           ((phi:A->real^N) o chart_inv (V,psi))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `\x:A. x`; `\x:A. x`; `U:A->bool`; `phi:A->real^N`;
                   `V:A->bool`; `psi:A->real^N`] MFDR_DIFFEO_CHART_REP) THEN
    SUBGOAL_THEN `!f:real^N->A. (psi:A->real^N) o (\x:A. x) o f = psi o f /\
                                (phi:A->real^N) o (\x:A. x) o f = phi o f`
      ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN s
        ==> metric_local atlasY (U,phi) (gY0:A->real^N^N) z =
            mpullback ((psi:A->real^N) o chart_inv (U:A->bool,phi:A->real^N))
                      (metric_local atlasX (V,psi) (gX0:A->real^N^N)) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_MPULLBACK_INVERT THEN
    MAP_EVERY EXISTS_TAC
     [`s':real^N->bool`; `s:real^N->bool`;
      `(phi:A->real^N) o chart_inv (V:A->bool,psi:A->real^N)`] THEN
    ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM] THEN
    EXPAND_TAC "s'" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; ETA_AX] THEN
    REPEAT STRIP_TAC THEN USE_THEN "R0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `((psi:A->real^N) o chart_inv (U:A->bool,phi:A->real^N)) (phi x) = psi x` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lck_dist2 k (mpullback ((psi:A->real^N) o chart_inv (U:A->bool,phi:A->real^N))
                           (metric_local atlasX (V,psi) (gX0:A->real^N^N)))
                (mpullback (psi o chart_inv (U:A->bool,phi:A->real^N))
                           (metric_local atlasX (V,psi) (gX:A->real^N^N)))
                ((phi:A->real^N) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`s':real^N->bool`; `s:real^N->bool`;
                        `(phi:A->real^N) o chart_inv (V:A->bool,psi:A->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC P3S_METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER W)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The jet hypothesis of PDE_GLUE at a surgery event.  On the               *)
(* retained region W, with the old-stage flow transported to the new atlas  *)
(* before the event time and the new-stage metric at the event time, the   *)
(* chart jets converge uniformly on compacts: rfs_limit_metric (preferred   *)
(* old charts) and rfs_same_metric_on give the lck_dist2 convergence in    *)
(* every restricted new chart (P3S_LCK_TRANSFER), and P3S_LCK_JET_CONV      *)
(* turns it into convergence of the iterated partials.                      *)
(* ------------------------------------------------------------------------- *)

let P3S_EVENT_JETS = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev W a (G:real->A->real^3^3).
     smooth_manifold_atlas topX atlasX /\
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     open_in topY W /\ W SUBSET topspace topX /\ a < ts /\
     (!t. a < t /\ t < ts ==> riemannian_metric atlasX (gX t)) /\
     (!t. a < t /\ t < ts ==> riemannian_metric (restrict_atlas atlasY W) (G t)) /\
     riemannian_metric (restrict_atlas atlasY W) (G ts) /\
     (!t x. a < t /\ t < ts /\ x IN W
            ==> G t x = restrict_metric atlasY W
                          (mfd_pullback_metric atlasY atlasX (\x. x) (gX t)) x) /\
     (!x. x IN W ==> G ts x = restrict_metric atlasY W (gY ts) x)
     ==> !cc K l e.
           cc IN restrict_atlas atlasY W /\ compact K /\
           K SUBSET IMAGE (SND cc) (FST cc) /\
           ALL (\i. 1 <= i /\ i <= dimindex(:3)) l /\ &0 < e
           ==> ?d. &0 < d /\
                   !t y. ts - d < t /\ t < ts /\ y IN K
                         ==> norm(iterated_partial l
                                    ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                     metric_local (restrict_atlas atlasY W) cc (G t)) y -
                                  iterated_partial l
                                    (vectorize o
                                     metric_local (restrict_atlas atlasY W) cc (G ts)) y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "RX")
    (CONJUNCTS_THEN2 (LABEL_TAC "RG") (CONJUNCTS_THEN2 (LABEL_TAC "RG0")
    (CONJUNCTS_THEN2 (LABEL_TAC "GM") (LABEL_TAC "GP")))))))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `W:A->bool`] P3S_EVENT_RETAINED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_event_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "LIM")
    (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
     CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "SAME")) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`Uc:A->bool`; `phi:A->real^3`; `K:real^3->bool`;
                       `l:num list`; `e:real`] THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^3) IN restrict_atlas atlasY W /\
                smooth_manifold_atlas (subtopology topY W) (restrict_atlas atlasY W) /\
                open_in topY (U:A->bool) /\ open (IMAGE (phi:A->real^3) (U INTER W)) /\
                topspace(subtopology topY W) = (W:A->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MFDM_CHART; FST];
      MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      MP_TAC(ISPECL [`topY:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s z. (s = ts \/ a < s /\ s < ts) /\ z IN IMAGE (phi:A->real^3) (U INTER W)
          ==> metric_local (restrict_atlas atlasY W) (U INTER W,phi) ((G:real->A->real^3^3) s) z =
              metric_local atlasY (U,phi)
                (if s = ts then (gY:real->A->real^3^3) ts
                 else mfd_pullback_metric atlasY atlasX (\x. x) (gX s)) z`
  (LABEL_TAC "ML") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `phi:A->real^3`; `W:A->bool`;
                   `if s = ts then (gY:real->A->real^3^3) ts
                    else mfd_pullback_metric atlasY atlasX (\x:A. x) (gX s)`;
                   `z:real^3`] P2CF_METRIC_LOCAL_RESTRICT_ON) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`subtopology topY (W:A->bool)`;
                   `restrict_atlas (atlasY:((A->bool)#(A->real^3))->bool) W`;
                   `(U INTER W:A->bool,phi:A->real^3)`; `(G:real->A->real^3^3) s`;
                   `restrict_metric (atlasY:((A->bool)#(A->real^3))->bool) W
                      (if s = ts then (gY:real->A->real^3^3) ts
                       else mfd_pullback_metric atlasY atlasX (\x:A. x) (gX s))`]
                  PDE_METRIC_LOCAL_CONG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      ASM_CASES_TAC `s:real = ts` THEN ASM_REWRITE_TAC[] THENL
       [USE_THEN "GP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "GM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `s:real = ts \/ a < s /\ s < ts` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER W)`; `K:real^3->bool`;
   `metric_local (restrict_atlas atlasY W) (U INTER W,phi) ((G:real->A->real^3^3) ts)`;
   `\t. metric_local (restrict_atlas (atlasY:((A->bool)#(A->real^3))->bool) W)
                     (U INTER W:A->bool,phi:A->real^3) ((G:real->A->real^3^3) t)`;
   `ts:real`; `ts - a`; `l:num list`] P3S_LCK_JET_CONV) THEN BETA_TAC THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "RG0" (MP_TAC o SPEC `(U INTER W:A->bool,phi:A->real^3)` o
                  GEN_REWRITE_RULE I [riemannian_metric]) THEN ASM_REWRITE_TAC[FST; SND];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "RG" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[riemannian_metric] THEN
  DISCH_THEN(MP_TAC o SPEC `(U INTER W:A->bool,phi:A->real^3)`) THEN
  ASM_REWRITE_TAC[FST; SND];
      X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  USE_THEN "LIM" (MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_limit_metric]) THEN
  DISCH_THEN(MP_TAC o SPECL [`IMAGE (chart_inv (U INTER W:A->bool,phi:A->real^3)) K`;
                             `LENGTH (l:num list)`; `e':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `compact_in (subtopology topY W)
                    (IMAGE (chart_inv (U INTER W:A->bool,phi:A->real^3)) K)`
    MP_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^3) (U INTER W))` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
        MP_TAC(ISPECL [`subtopology topY (W:A->bool)`;
                       `restrict_atlas (atlasY:((A->bool)#(A->real^3))->bool) W`;
                       `(U INTER W:A->bool,phi:A->real^3)`] MFDD_CHART_INV_CONTINUOUS) THEN
        ASM_REWRITE_TAC[FST; SND]];
      REWRITE_TAC[ASSUME `subtopology topY (W:A->bool) = subtopology topX W`] THEN
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DLIM"))) THEN
  EXISTS_TAC `min d (ts - a)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < t /\ ts - d < t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ts - min d (ts - a) < t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?x0:A. x0 IN U INTER W /\ (y:real^3) = (phi:A->real^3) x0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN K` THEN
    UNDISCH_TAC `K SUBSET IMAGE (phi:A->real^3) (U INTER W)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
      SUBGOAL_THEN `(x0:A) IN topspace topX /\ x0 IN U /\ x0 IN W` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:A) IN U INTER W` THEN UNDISCH_TAC `W SUBSET topspace (topX:A topology)` THEN
    SET_TAC[];
    ALL_TAC] THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `x0:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
   `lck_dist2 (LENGTH (l:num list))
      (metric_local (restrict_atlas atlasY W) (U INTER W,phi) ((G:real->A->real^3^3) ts))
      (metric_local (restrict_atlas atlasY W) (U INTER W,phi) (G t)) ((phi:A->real^3) x0) =
    lck_dist2 (LENGTH l)
      (metric_local atlasX (chart_at atlasX x0) (ev_limit (ev:(A)rfs_event)))
      (metric_local atlasX (chart_at atlasX x0) ((gX:real->A->real^3^3) t))
      (SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) x0) x0)`
  SUBST1_TAC THENL
   [ALL_TAC;
    USE_THEN "DLIM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(phi:A->real^3) x0` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `phi:A->real^3`; `W:A->bool`; `x0:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[IN_INTER]] THEN
      SUBGOAL_THEN
   `!z. z IN IMAGE (phi:A->real^3) (U INTER W)
        ==> metric_local (restrict_atlas atlasY W) (U INTER W,phi) ((G:real->A->real^3^3) ts) z =
            metric_local atlasY (U,phi) ((gY:real->A->real^3^3) ts) z /\
            metric_local (restrict_atlas atlasY W) (U INTER W,phi) (G t) z =
            metric_local atlasY (U,phi)
              (mfd_pullback_metric atlasY atlasX (\x:A. x) ((gX:real->A->real^3^3) t)) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "ML" (MP_TAC o SPECL [`ts:real`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
      USE_THEN "ML" (MP_TAC o SPECL [`t:real`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NE]];
    ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
   `lck_dist2 (LENGTH (l:num list))
      (metric_local atlasY (U,phi) ((gY:real->A->real^3^3) ts))
      (metric_local atlasY (U,phi)
         (mfd_pullback_metric atlasY atlasX (\x:A. x) ((gX:real->A->real^3^3) t)))
      ((phi:A->real^3) x0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
      MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                 `topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `(gY:real->A->real^3^3) ts`;
                 `mfd_pullback_metric atlasY atlasX (\x:A. x) ((gX:real->A->real^3^3) t)`;
                 `ev_limit (ev:(A)rfs_event)`; `(gX:real->A->real^3^3) t`;
                 `U:A->bool`; `phi:A->real^3`;
                 `FST(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A))`;
                 `SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A))`;
                 `x0:A`; `LENGTH (l:num list)`] P3S_LCK_TRANSFER) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THEN
      ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!f:real^3->A. (\x:A. x) o f = f` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE (SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A)))
               (FST(chart_at atlasX x0) INTER W))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3S_METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A)))
                      (FST(chart_at atlasX x0) INTER ev_omega (ev:(A)rfs_event))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "LIM" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_limit_metric]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]];
    MATCH_MP_TAC P3S_METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A)))
                      (FST(chart_at atlasX x0))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "RX" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; REWRITE_TAC[riemannian_metric]] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    USE_THEN "SAME" (MP_TAC o SPECL
      [`chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A)`;
       `(U:A->bool,phi:A->real^3)`;
       `SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A)) z`] o
      GEN_REWRITE_RULE I [rfs_same_metric_on]) THEN
    ASM_REWRITE_TAC[SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[FST; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `z IN FST (chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A)) INTER W` THEN
    MP_TAC(ISPECL [`topY:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `\x:A. x`; `\x:A. x`; `(gX:real->A->real^3^3) t`; `U:A->bool`;
                   `phi:A->real^3`;
                   `FST(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A))`;
                   `SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) (x0:A))`; `z:A`]
                  P2A_PULLBACK_METRIC_LOCAL_W) THEN
    REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[]]] THEN
      DISCH_THEN ACCEPT_TAC;
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[]]);;

