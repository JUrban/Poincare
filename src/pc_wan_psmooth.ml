(* ========================================================================= *)
(* pc_wan_psmooth: a compactly supported map whose weak derivatives of all   *)
(* orders (all directions) are in L^2 agrees a.e. with a smooth map. The     *)
(* Sobolev embedding is PDM_SOBOLEV_COMPACT of pc_pde_mnorm (cube transplant *)
(* of the torus embedding); the smooth limit uses HAS_DERIVATIVE_SEQUENCE    *)
(* and SMOOTH_MAP_ON_PARTIAL_FAMILY.                                         *)
(*   - uniform limits of smooth maps with uniformly Cauchy derivatives;      *)
(*   - derivatives of mollifications, uniform to L^2 convergence, the        *)
(*     smooth representative WAN_HD_ALL_SMOOTH;                              *)
(*   - a.e. identification and gluing of local smooth representatives.       *)
(* ========================================================================= *)

needs "src/pc_wan_ptime.ml";;
needs "src/pc_pde_mnorm.ml";;

prioritize_real();;
type_invention_error := true;;

let WAN_FINITE_EVENTUALLY = prove
 (`!(P:num->num->bool) n.
     (!i. 1 <= i /\ i <= n ==> ?N. !m. N <= m ==> P i m)
     ==> ?N. !i m. 1 <= i /\ i <= n /\ N <= m ==> P i m`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `0` THEN MESON_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `SUC n` (ASSUME
    `!i. 1 <= i /\ i <= SUC n ==> ?N. !m. N <= m ==> (P:num->num->bool) i m`)) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N2:num`)] THEN
  EXISTS_TAC `N1 + N2:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i = SUC n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN ASM_ARITH_TAC]);;

let WAN_SEQ_SMOOTH_LIMIT = prove
 (`!(f:num->real^M->real^K).
     (!n. smooth_map_on (:real^M) (f n)) /\
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
          ==> !e. &0 < e
                  ==> ?N. !m n x. N <= m /\ N <= n
                                  ==> norm(iterated_partial l (f m) x -
                                           iterated_partial l (f n) x) < e)
     ==> ?g. smooth_map_on (:real^M) g /\ !x. ((\n. f n x) --> g x) sequentially`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cau")) THEN
  SUBGOAL_THEN
   `?G. !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
            ==> !e. &0 < e
                    ==> ?N. !n x. N <= n
                                  ==> dist(iterated_partial l ((f:num->real^M->real^K) n) x,
                                           G l x) < e`
  (X_CHOOSE_THEN `G:(num)list->real^M->real^K` (LABEL_TAC "un")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:real^M. T`;
                   `\n. iterated_partial l ((f:num->real^M->real^K) n)`]
                  UNIFORMLY_CONVERGENT_EQ_CAUCHY) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[dist] THEN USE_THEN "cau" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
          ==> ((\n. iterated_partial l ((f:num->real^M->real^K) n) x) -->
               (G:(num)list->real^M->real^K) l x) sequentially`
  (LABEL_TAC "pt") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "un" (fun th -> MP_TAC(SPEC `e:real` (MP (SPEC `l:(num)list` th)
      (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:M)) l`)))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
          ==> ((G:(num)list->real^M->real^K) l has_derivative
               (\v. vsum(1..dimindex(:M)) (\i. v$i % G (CONS i l) x))) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`(:real^M)`; `\n. iterated_partial l ((f:num->real^M->real^K) n)`;
      `\n (x:real^M) (v:real^M). vsum(1..dimindex(:M))
                 (\i. v$i % iterated_partial (CONS i l) ((f:num->real^M->real^K) n) x)`;
      `\(x:real^M) (v:real^M). vsum(1..dimindex(:M))
               (\i. v$i % (G:(num)list->real^M->real^K) (CONS i l) x)`]
     HAS_DERIVATIVE_SEQUENCE) THEN
    REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC[iterated_partial] THEN
        MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
        MATCH_MP_TAC WAN_SMOOTH_DIFFERENTIABLE THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        MP_TAC(ISPECL
         [`\i m. !x:real^M. dist(iterated_partial (CONS i l) ((f:num->real^M->real^K) m) x,
                                 (G:(num)list->real^M->real^K) (CONS i l) x) <
                            e / (&(dimindex(:M)) + &1)`;
          `dimindex(:M)`] WAN_FINITE_EVENTUALLY) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:M)) (CONS i l)` ASSUME_TAC THENL
           [ASM_REWRITE_TAC[ALL]; ALL_TAC] THEN
          USE_THEN "un" (fun th -> MP_TAC(MP (SPEC `CONS (i:num) l` th)
            (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:M)) (CONS i l)`))) THEN
          DISCH_THEN(MP_TAC o SPEC `e / (&(dimindex(:M)) + &1)`) THEN
          ANTS_TAC THENL
           [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
            MESON_TAC[]];
          ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
        MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`; `h:real^M`] THEN
        REWRITE_TAC[GE] THEN DISCH_TAC THEN REWRITE_TAC[GSYM VSUM_SUB_NUMSEG] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
        TRANS_TAC REAL_LE_TRANS
         `sum(1..dimindex(:M)) (\i. norm(h:real^M) * (e / (&(dimindex(:M)) + &1)))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
          X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
          REWRITE_TAC[COMPONENT_LE_NORM] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o C MP
            (CONJ (ASSUME `1 <= i`) (CONJ (ASSUME `i <= dimindex(:M)`) (ASSUME `N:num <= n`))) o
            SPECL [`i:num`; `n:num`]) THEN
          REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
          REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
          SUBGOAL_THEN `&(dimindex(:M)) * (norm(h:real^M) * e / (&(dimindex(:M)) + &1)) =
                        (norm h * e) * (&(dimindex(:M)) / (&(dimindex(:M)) + &1))`
          SUBST1_TAC THENL
           [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
          GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `e * n = (n * e) * &1`] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LT_IMP_LE] THEN
          SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN REAL_ARITH_TAC];
        MAP_EVERY EXISTS_TAC [`vec 0:real^M`; `(G:(num)list->real^M->real^K) l (vec 0)`] THEN
        USE_THEN "pt" (fun th -> ACCEPT_TAC(MP (SPECL [`l:(num)list`; `vec 0:real^M`] th)
          (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:M)) l`)))];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gg:real^M->real^K` (LABEL_TAC "hd")) THEN
    SUBGOAL_THEN `(gg:real^M->real^K) = G (l:(num)list)` (SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\n. iterated_partial l ((f:num->real^M->real^K) n) y` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [USE_THEN "hd" (fun th -> REWRITE_TAC[SPEC `y:real^M` th]);
        USE_THEN "pt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "hd" (fun th -> REWRITE_TAC[SPEC `x:real^M` th])];
    ALL_TAC] THEN
  EXISTS_TAC `(G:(num)list->real^M->real^K) []` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^M)`; `G:(num)list->real^M->real^K`] SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(MP_TAC o SPEC `[]:(num)list`) THEN
    REWRITE_TAC[ALL];
    X_GEN_TAC `x:real^M` THEN
    USE_THEN "pt" (MP_TAC o SPECL [`[]:(num)list`; `x:real^M`]) THEN
    REWRITE_TAC[ALL; iterated_partial; ETA_AX]]);;

(* ========================================================================= *)
(* Iterated derivatives of mollifications, uniform                          *)
(* convergence on a compact set gives L^2 convergence.                       *)
(* ========================================================================= *)

let WAN_HD_MOLL_ITERATED = prove
 (`!l s (u:real^M->real^K) k0.
     compact k0 /\ (!x. ~(x IN k0) ==> u x = vec 0) /\
     ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\
     wan_hd (1..dimindex(:M)) (LENGTH l + s) u
     ==> ?w. wan_hd (1..dimindex(:M)) s w /\ (!x. ~(x IN k0) ==> w x = vec 0) /\
             !e x. &0 < e ==> iterated_partial l (wan_moll e u) x = wan_moll e w x`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; ADD_CLAUSES; iterated_partial] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `u:real^M->real^K` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH; ALL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SUC s`; `u:real^M->real^K`; `k0:real^M->bool`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `LENGTH(t:(num)list) + SUC s = SUC(LENGTH t) + s`] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^M->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`1..dimindex(:M)`; `s:num`; `w0:real^M->real^K`; `h:num`;
                 `k0:real^M->bool`] WAN_HD_SUPPORT_WITNESS) THEN
  ASM_REWRITE_TAC[IN_NUMSEG] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^M->real^K` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[iterated_partial] THEN
  SUBGOAL_THEN `iterated_partial t (wan_moll e (u:real^M->real^K)) = wan_moll e w0`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC WAN_MOLL_WPD THEN ASM_REWRITE_TAC[]);;

let WAN_UNIFORM_L2C = prove
 (`!(h:num->real^M->real^K) g k1.
     compact k1 /\ (!n x. ~(x IN k1) ==> h n x = vec 0) /\
     (!x. ~(x IN k1) ==> g x = vec 0) /\
     (!n. h n IN lspace (:real^M) (&2)) /\ g IN lspace (:real^M) (&2) /\
     (!e. &0 < e ==> ?N. !n x. N <= n ==> norm(h n x - g x) < e)
     ==> wan_l2c h g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[WAN_L2C_SQ] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  ABBREV_TAC `mk = measure(k1:real^M->bool)` THEN
  SUBGOAL_THEN `&0 <= mk` ASSUME_TAC THENL
   [EXPAND_TAC "mk" THEN MATCH_MP_TAC MEASURE_POS_LE THEN ASM_SIMP_TAC[MEASURABLE_COMPACT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) (eps / (mk + &1))`) THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = min (&1) (eps / (mk + &1))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 /\ d * (mk + &1) <= eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `(eps / (mk + &1)) * (mk + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ARITH `&0 <= m ==> ~(m + &1 = &0)`; REAL_LE_REFL]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x. (h:num->real^M->real^K) n x - g x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < e ==> abs x < e`) THEN
  ASM_SIMP_TAC[WAN_SQINT_POS] THEN
  TRANS_TAC REAL_LET_TRANS
   `drop(integral (:real^M) (\x. (d pow 2) % (indicator k1 x:real^1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      REWRITE_TAC[indicator; GSYM MEASURABLE_INTEGRABLE] THEN
      ASM_SIMP_TAC[MEASURABLE_COMPACT; ETA_AX];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[indicator; LIFT_DROP; DROP_CMUL] THEN COND_CASES_TAC THENL
       [REWRITE_TAC[DROP_VEC; REAL_MUL_RID] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0; DROP_VEC; REAL_MUL_RZERO] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(indicator k1:real^M->real^1) integrable_on (:real^M)` ASSUME_TAC THENL
   [REWRITE_TAC[indicator; GSYM MEASURABLE_INTEGRABLE] THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`indicator k1:real^M->real^1`; `d pow 2`; `(:real^M)`] INTEGRAL_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_CMUL] THEN
  SUBGOAL_THEN `integral (:real^M) (indicator k1:real^M->real^1) = lift mk` SUBST1_TAC THENL
   [EXPAND_TAC "mk" THEN MP_TAC(ISPECL [`k1:real^M->bool`; `(:real^M)`] INTEGRAL_INDICATOR) THEN
    ASM_SIMP_TAC[INTER_UNIV; MEASURABLE_COMPACT];
    REWRITE_TAC[LIFT_DROP]] THEN
  SUBGOAL_THEN `d pow 2 * mk <= d * mk` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let WAN_SOB_ARITH = prove
 (`!C n e x.
     &0 < C /\ &0 < e /\ &0 <= x /\ x <= &2 * min (&1) (e pow 2 / (&8 * C * (&n + &1)))
     ==> C * &n * x pow 2 < e pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = min (&1) (e pow 2 / (&8 * C * (&n + &1)))` THEN
  SUBGOAL_THEN `&0 < e pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &8 * C * (&n + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 /\ d * (&8 * C * (&n + &1)) <= e pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `(e pow 2 / (&8 * C * (&n + &1))) * (&8 * C * (&n + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 <= &4 * d` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&2 * d) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `d * d <= d * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * &n * x pow 2 <= C * &n * (&4 * d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * d` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &n * C * d` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `d * (&8 * C * (&n + &1)) <= e pow 2` THEN ASM_REAL_ARITH_TAC);;

let WAN_MOLL_SEQ_UCAUCHY = prove
 (`!(u:real^M->real^K) k0 l.
     compact k0 /\ (!x. ~(x IN k0) ==> u x = vec 0) /\
     (!s. wan_hd (1..dimindex(:M)) s u) /\ ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
     ==> !e. &0 < e
             ==> ?N. !m n x. N <= m /\ N <= n
                             ==> norm(iterated_partial l (wan_moll (inv(&m + &1)) u) x -
                                      iterated_partial l (wan_moll (inv(&n + &1)) u) x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `k1 = {x + y:real^M | x IN k0 /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact (k1:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN ASM_SIMP_TAC[WAN_CBALL_SUMS_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^M) (wan_moll (inv(&n + &1)) (u:real^M->real^K)) /\
        (!x. ~(x IN k1) ==> wan_moll (inv(&n + &1)) u x = vec 0)`
  (LABEL_TAC "V") THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN REWRITE_TAC[WAN_INV_N1_POS] THEN
      MATCH_MP_TAC WAN_L2_LLOC THEN MATCH_MP_TAC WAN_HD_LSPACE THEN
      MAP_EVERY EXISTS_TAC [`1..dimindex(:M)`; `0`] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "k1" THEN MATCH_MP_TAC WAN_MOLL_SUPPORT_CBALL THEN
      ASM_REWRITE_TAC[WAN_INV_N1_POS; WAN_INV_N1_LE1]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k1:real^M->bool` (INST_TYPE [`:M`,`:N`; `:K`,`:K`] PDM_SOBOLEV_COMPACT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  ABBREV_TAC `S = pde_index_lists (dimindex(:M) + LENGTH(l:(num)list)) (:M)` THEN
  SUBGOAL_THEN `FINITE(S:(num)list->bool) /\ ~(S = {})` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE; GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[PDE_INDEX_LISTS_NIL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l'. l' IN S
         ==> ?w. wan_l2c (\n. iterated_partial l' (wan_moll (inv(&n + &1)) (u:real^M->real^K))) w`
  MP_TAC THENL
   [X_GEN_TAC `l':(num)list` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`l':(num)list`; `0`; `u:real^M->real^K`; `k0:real^M->bool`]
                  WAN_HD_MOLL_ITERATED) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^M->real^K` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^M->real^K` THEN MATCH_MP_TAC WAN_L2C_EQ THEN
    MAP_EVERY EXISTS_TAC [`\n. wan_moll (inv(&n + &1)) (w:real^M->real^K)`;
                          `w:real^M->real^K`] THEN
    ASM_SIMP_TAC[WAN_INV_N1_POS] THEN MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN
    EXISTS_TAC `k0:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `wan_hd (1..dimindex(:M)) 0 (w:real^M->real^K)` THEN REWRITE_TAC[wan_hd];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(num)list->real^M->real^K` (LABEL_TAC "Wc") o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  ABBREV_TAC `d = min (&1) (e pow 2 / (&8 * C * (&(CARD(S:(num)list->bool)) + &1)))` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\l' n. lnorm (:real^M) (&2)
                           (\x. iterated_partial l' (wan_moll (inv(&n + &1)) (u:real^M->real^K)) x -
                                (W:(num)list->real^M->real^K) l' x) < d`;
                 `S:(num)list->bool`] EVENTUALLY_FORALL) THEN
  ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [X_GEN_TAC `l':(num)list` THEN DISCH_TAC THEN
    USE_THEN "Wc" (fun th -> MP_TAC(MP (SPEC `l':(num)list` th) (ASSUME `(l':(num)list) IN S`))) THEN
    REWRITE_TAC[wan_l2c; REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `d:real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_THEN(LABEL_TAC "N") THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:real^M`] THEN STRIP_TAC THEN
  USE_THEN "V" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
  USE_THEN "V" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN
   `!l' y. iterated_partial l'
             (\x. wan_moll (inv(&m + &1)) (u:real^M->real^K) x -
                  wan_moll (inv(&n + &1)) u x) y =
           iterated_partial l' (wan_moll (inv(&m + &1)) u) y -
           iterated_partial l' (wan_moll (inv(&n + &1)) u) y`
  (LABEL_TAC "sub") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`l':(num)list`; `(:real^M)`; `wan_moll (inv(&m + &1)) (u:real^M->real^K)`;
                   `wan_moll (inv(&n + &1)) (u:real^M->real^K)`] TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "sob" (MP_TAC o SPECL
   [`(:real^M)`;
    `\x. wan_moll (inv(&m + &1)) (u:real^M->real^K) x - wan_moll (inv(&n + &1)) u x`;
    `l:(num)list`; `x:real^M`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_SUB_REFL]];
    ALL_TAC] THEN
  USE_THEN "sub" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `sum S (\l'. drop(integral (:real^M)
                 (\y. lift(norm(iterated_partial l' (wan_moll (inv(&m + &1)) (u:real^M->real^K)) y -
                                iterated_partial l' (wan_moll (inv(&n + &1)) u) y) pow 2)))) <=
    &(CARD(S:(num)list->bool)) * (d + d) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:(num)list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\n. iterated_partial a (wan_moll (inv(&n + &1)) (u:real^M->real^K))`;
                   `(W:(num)list->real^M->real^K) a`; `m:num`; `n:num`; `d:real`; `d:real`]
                  WAN_L2C_PAIR_SQ_BOUND) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "Wc" (fun th -> REWRITE_TAC[MP (SPEC `a:(num)list` th) (ASSUME `(a:(num)list) IN S`)]) THEN
    USE_THEN "N" (fun th -> MP_TAC(MP (SPEC `m:num` th) (ASSUME `N:num <= m`)) THEN
                            MP_TAC(MP (SPEC `n:num` th) (ASSUME `N:num <= n`))) THEN
    DISCH_THEN(MP_TAC o SPEC `a:(num)list`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `a:(num)list`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  TRANS_TAC REAL_LET_TRANS `C * &(CARD(S:(num)list->bool)) * (d + d) pow 2` THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `C * sum S (\l'. drop(integral (:real^M)
                 (\y. lift(norm(iterated_partial l' (wan_moll (inv(&m + &1)) (u:real^M->real^K)) y -
                                iterated_partial l' (wan_moll (inv(&n + &1)) u) y) pow 2))))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC WAN_SOB_ARITH THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let WAN_HD_ALL_SMOOTH = prove
 (`!(u:real^M->real^K) k0.
     compact k0 /\ (!x. ~(x IN k0) ==> u x = vec 0) /\
     (!s. wan_hd (1..dimindex(:M)) s u)
     ==> ?w. smooth_map_on (:real^M) w /\ negligible {x | ~(u x = w x)}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k1 = {x + y:real^M | x IN k0 /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact (k1:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN ASM_SIMP_TAC[WAN_CBALL_SUMS_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^M->real^K) IN lspace (:real^M) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_HD_LSPACE THEN
    MAP_EVERY EXISTS_TAC [`1..dimindex(:M)`; `0`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^M) (wan_moll (inv(&n + &1)) (u:real^M->real^K)) /\
        (!x. ~(x IN k1) ==> wan_moll (inv(&n + &1)) u x = vec 0) /\
        wan_moll (inv(&n + &1)) u IN lspace (:real^M) (&2)`
  (LABEL_TAC "V") THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_SIMP_TAC[WAN_INV_N1_POS; WAN_L2_LLOC];
      EXPAND_TAC "k1" THEN MATCH_MP_TAC WAN_MOLL_SUPPORT_CBALL THEN
      ASM_REWRITE_TAC[WAN_INV_N1_POS; WAN_INV_N1_LE1];
      ASM_SIMP_TAC[WAN_MOLL_L2; WAN_INV_N1_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\n. wan_moll (inv(&n + &1)) (u:real^M->real^K)` WAN_SEQ_SMOOTH_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "V" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN MATCH_MP_TAC WAN_MOLL_SEQ_UCAUCHY THEN
      EXISTS_TAC `k0:real^M->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^K` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. ~(x IN k1) ==> (g:real^M->real^K) x = vec 0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. wan_moll (inv(&n + &1)) (u:real^M->real^K) x` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    USE_THEN "lim" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(\n. wan_moll (inv(&n + &1)) (u:real^M->real^K) x) = (\n. vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      USE_THEN "V" (fun th -> MP_TAC(SPEC `n:num` th)) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[LIM_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n x. N <= n
                      ==> norm(wan_moll (inv(&n + &1)) (u:real^M->real^K) x - g x) < e`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^M. T`; `\n. wan_moll (inv(&n + &1)) (u:real^M->real^K)`;
                   `g:real^M->real^K`] UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT) THEN
    REWRITE_TAC[dist] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^M->real^K`; `k0:real^M->bool`; `[]:(num)list`]
                    WAN_MOLL_SEQ_UCAUCHY) THEN
      ASM_REWRITE_TAC[ALL; iterated_partial];
      X_GEN_TAC `x:real^M` THEN
      USE_THEN "lim" (MP_TAC o SPEC `x:real^M`) THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2C_UNIQUE THEN
  EXISTS_TAC `\n. wan_moll (inv(&n + &1)) (u:real^M->real^K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN EXISTS_TAC `k0:real^M->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_UNIFORM_L2C THEN EXISTS_TAC `k1:real^M->bool` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN
    EXISTS_TAC `k1:real^M->bool` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON]]);;

(* ========================================================================= *)
(* Identification almost everywhere.  Continuous maps that agree a.e.       *)
(* on an open set agree on it; local smooth representatives glue to a      *)
(* smooth representative on the whole open set.                             *)
(* ========================================================================= *)

let WAN_CONT_AE_EQ_OPEN = prove
 (`!(s:real^M->bool) (f:real^M->real^K) g.
     open s /\ f continuous_on s /\ g continuous_on s /\
     negligible {x | x IN s /\ ~(f x = g x)}
     ==> !x. x IN s ==> f x = g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {x | x IN s /\ ~((f:real^M->real^K) x = g x)}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. (f:real^M->real^K) x - g x`; `s:real^M->bool`;
                   `(:real^K) DIFF {vec 0}`] CONTINUOUS_OPEN_PREIMAGE) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{x | x IN s /\ ~((f:real^M->real^K) x = g x)}` OPEN_NOT_NEGLIGIBLE) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let WAN_LOCAL_SMOOTH_AE = prove
 (`!(om:real^M->bool) (u:real^M->real^K).
     open om /\
     (!x. x IN om
          ==> ?t w. open t /\ x IN t /\ t SUBSET om /\ smooth_map_on t w /\
                    negligible {z | z IN t /\ ~(u z = w z)})
     ==> ?w. smooth_map_on om w /\ negligible {z | z IN om /\ ~(u z = w z)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->real^M->bool`
    (X_CHOOSE_THEN `w:real^M->real^M->real^K` (LABEL_TAC "tw"))) THEN
  SUBGOAL_THEN
   `!x z. x IN om /\ z IN (t:real^M->real^M->bool) x
          ==> (w:real^M->real^M->real^K) z z = w x z`
  (LABEL_TAC "agree") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "tw" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^M) IN om`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^M) IN om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "tw" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^M) IN om`))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`(t:real^M->real^M->bool) x INTER t z`;
                   `(w:real^M->real^M->real^K) z`; `(w:real^M->real^M->real^K) x`]
                  WAN_CONT_AE_EQ_OPEN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(t:real^M->real^M->bool) z` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; INTER_SUBSET];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(t:real^M->real^M->bool) x` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; INTER_SUBSET];
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `{y | y IN (t:real^M->real^M->bool) z /\
                         ~((u:real^M->real^K) y = (w:real^M->real^M->real^K) z y)} UNION
                    {y | y IN t x /\ ~(u y = w x y)}` THEN
        ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN SET_TAC[]];
      DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  EXISTS_TAC `\z. (w:real^M->real^M->real^K) z z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    USE_THEN "tw" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^M) IN om`))) THEN
    STRIP_TAC THEN
    EXISTS_TAC `(t:real^M->real^M->bool) x` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(w:real^M->real^M->real^K) x` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LOCALLY_NEGLIGIBLE_ALT] THEN
  X_GEN_TAC `y:real^M` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "tw" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^M) IN om`))) THEN
  STRIP_TAC THEN
  EXISTS_TAC `{z | z IN om /\ ~((u:real^M->real^K) z = (w:real^M->real^M->real^K) z z)}
              INTER (t:real^M->real^M->bool) y` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER; IN_ELIM_THM] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{z | z IN (t:real^M->real^M->bool) y /\
                   ~((u:real^M->real^K) z = (w:real^M->real^M->real^K) y z)}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(w:real^M->real^M->real^K) z z = w y z`
    (fun th -> ASM_MESON_TAC[th]) THEN
  USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

