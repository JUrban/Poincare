(* ========================================================================= *)
(* Unit pc_rfa_rmnorm: derivatives of squared norms: the derivative of a     *)
(* full contraction along a parameter, the action of a 2-tensor on one slot, *)
(* metric compatibility of ltinner, the Laplacian of a squared norm (Bochner *)
(* formula, local form) and the evolution of |Rm|^2 under a local Ricci      *)
(* flow.                                                                     *)
(* ========================================================================= *)

needs "src/pc_rfa_rmevol.ml";;
needs "src/pc_rfa_lalg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The product rule for finite products, and exchanging one                  *)
(* slot of an index tuple with a free index.                                 *)
(* ========================================================================= *)

let RFA_HAS_REAL_DERIVATIVE_PRODUCT = prove
 (`!(f:num->real->real) f' k t.
        (!m. 1 <= m /\ m <= k ==> ((f m) has_real_derivative (f' m)) (atreal t))
        ==> ((\s. product(1..k) (\j. f j s)) has_real_derivative
             sum(1..k) (\m. product(1..k) (\j. if j = m then f' j else f j t)))
            (atreal t)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `((f:num->real->real) (SUC k) has_real_derivative f' (SUC k)) (atreal t)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. product(1..k) (\j. (f:num->real->real) j s)`;
                 `sum(1..k) (\m. product(1..k) (\j. if j = m then (f':num->real) j
                                                  else (f:num->real->real) j t))`;
                 `\s. (f:num->real->real) (SUC k) s`;
                 `(f':num->real) (SUC k)`; `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net
                   ==> (f has_real_derivative y) net`) THEN
  SUBGOAL_THEN
   `sum(1..k) (\m. product(1..k) (\j. if j = m then (f':num->real) j
                                      else (f:num->real->real) j t) *
                   (if SUC k = m then f' (SUC k) else f (SUC k) t)) =
    sum(1..k) (\m. product(1..k) (\j. if j = m then f' j else f j t)) * f (SUC k) t`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(SUC k = i)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product(1..k) (\j. if j = SUC k then (f':num->real) j
                       else (f:num->real->real) j t) =
    product(1..k) (\j. f j t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(i = SUC k)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_TUPLE_SLOT_SWAP = prove
 (`!k m (Fn:(num->num)->num->real).
        1 <= m /\ m <= k
        ==> sum (index_tuples k (:N)) (\J. sum(1..dimindex(:N)) (\c. Fn J c)) =
            sum (index_tuples k (:N))
                (\J. sum(1..dimindex(:N))
                       (\c. Fn (\j. if j = m then c else J j) (J m)))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_SUM_PRODUCT; LRG_INDEX_TUPLES_FINITE; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL
   [`\(J:num->num,c:num). (Fn:(num->num)->num->real) J c`;
    `\(J:num->num,c:num). (\j. if j = m then c else J j),(J m:num)`;
    `{J,c | J IN index_tuples k (:N) /\ c IN 1..dimindex(:N)}`] SUM_BIJECTION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    SUBGOAL_THEN
     `!J c. J IN index_tuples k (:N) /\ c IN 1..dimindex(:N)
            ==> (\j. if j = m then c else J j) IN index_tuples k (:N) /\
                J m IN 1..dimindex(:N)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[index_tuples; IN_ELIM_THM; IN_NUMSEG] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`J:num->num`; `c:num`] THEN DISCH_TAC THEN
    REWRITE_TAC[EXISTS_UNIQUE; EXISTS_PAIR_THM; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
                PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`\j. if j = m then c else (J:num->num) j`; `(J:num->num) m`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
      ASM_CASES_TAC `j:num = m` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`J':num->num`; `c':num`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `j:num = m` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[] THEN
        MESON_TAC[]]];
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]]);;

(* ========================================================================= *)
(* Full contractions at a point (rfa_ltc), with one slot                     *)
(* weighted by another matrix (rfa_ltq); their derivative along a           *)
(* parameter; the weighted slot as the action of a bilinear form on that    *)
(* slot (rfa_qacte).                                                         *)
(* ========================================================================= *)

let rfa_ltc = new_definition
 `rfa_ltc k (gi:real^N^N) (A:(num->real^N)->real) (B:(num->real^N)->real) =
    sum (index_tuples k (:N))
     (\ip. sum (index_tuples k (:N))
           (\jq. A (\m. basis(ip m)) * B (\m. basis(jq m)) *
                product(1..k) (\j. gi$(ip j)$(jq j))))`;;

let rfa_ltq = new_definition
 `rfa_ltq k (gi:real^N^N) (X:real^N^N) m (A:(num->real^N)->real)
          (B:(num->real^N)->real) =
    sum (index_tuples k (:N))
     (\ip. sum (index_tuples k (:N))
           (\jq. A (\m. basis(ip m)) * B (\m. basis(jq m)) *
                product(1..k) (\j. if j = m then X$(ip j)$(jq j) else gi$(ip j)$(jq j))))`;;

let rfa_qacte = new_definition
 `rfa_qacte (gi:real^N^N) (Wm:real^N^N) m (B:(num->real^N)->real) (u:num->real^N) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      gi$a$b * (u m dot (Wm ** basis a)) * B (\j. if j = m then basis b else u j)))`;;

let RFA_LTINNER_LTC = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) tg y.
        ltinner k G tf tg y = rfa_ltc k (matrix_inv(G y)) (tf y) (tg y)`,
  REWRITE_TAC[ltinner; rfa_ltc]);;

let RFA_LTNORM2_LTC = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y.
        ltnorm2 k G tf y = rfa_ltc k (matrix_inv(G y)) (tf y) (tf y)`,
  REWRITE_TAC[ltnorm2; rfa_ltc]);;

(* The derivative of a full contraction along a parameter. *)

let RFA_LTC_DERIV = prove
 (`!k (gi:real->real^N^N) gi' (A:real->(num->real^N)->real) A' B B' t.
        (!a b. ((\s. gi s$a$b) has_real_derivative gi'$a$b) (atreal t)) /\
        (!ip. ip IN index_tuples k (:N)
             ==> ((\s. A s (\m. basis(ip m))) has_real_derivative A' ip) (atreal t) /\
                 ((\s. B s (\m. basis(ip m))) has_real_derivative B' ip) (atreal t))
        ==> ((\s. rfa_ltc k (gi s) (A s) (B s)) has_real_derivative
             sum (index_tuples k (:N))
              (\ip. sum (index_tuples k (:N))
                (\jq. (A' ip * B t (\m. basis(jq m)) + A t (\m. basis(ip m)) * B' jq) *
                     product(1..k) (\j. gi t$(ip j)$(jq j)))) +
             sum(1..k) (\m. rfa_ltq k (gi t) gi' m (A t) (B t))) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ltc; rfa_ltq] THEN
  SUBGOAL_THEN
   `sum(1..k) (\m. sum (index_tuples k (:N))
      (\ip. sum (index_tuples k (:N))
        (\jq. (A:real->(num->real^N)->real) t (\m. basis(ip m)) *
             (B:real->(num->real^N)->real) t (\m. basis(jq m)) *
             product(1..k) (\j. if j = m then (gi':real^N^N)$(ip j)$(jq j)
                                else (gi:real->real^N^N) t$(ip j)$(jq j))))) =
    sum (index_tuples k (:N))
      (\ip. sum (index_tuples k (:N))
        (\jq. A t (\m. basis(ip m)) * B t (\m. basis(jq m)) *
             sum(1..k) (\m. product(1..k) (\j. if j = m then gi'$(ip j)$(jq j)
                                               else gi t$(ip j)$(jq j)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    GEN_REWRITE_TAC LAND_CONV
     [MATCH_MP SUM_SWAP (CONJ (SPECL [`1`; `k:num`] FINITE_NUMSEG)
                              (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN
    GEN_REWRITE_TAC LAND_CONV
     [MATCH_MP SUM_SWAP (CONJ (SPECL [`1`; `k:num`] FINITE_NUMSEG)
                              (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(MATCH_MP SUM_ADD (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN X_GEN_TAC `ip:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN X_GEN_TAC `jq:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`\j s. (gi:real->real^N^N) s$((ip:num->num) j)$((jq:num->num) j)`;
                 `\j. (gi':real^N^N)$((ip:num->num) j)$((jq:num->num) j)`;
                 `k:num`; `t:real`] RFA_HAS_REAL_DERIVATIVE_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s. (A:real->(num->real^N)->real) s (\m. basis((ip:num->num) m))) has_real_derivative
     (A':(num->num)->real) ip) (atreal t) /\
    ((\s. (B:real->(num->real^N)->real) s (\m. basis((jq:num->num) m))) has_real_derivative
     (B':(num->num)->real) jq) (atreal t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. (B:real->(num->real^N)->real) s (\m. basis((jq:num->num) m))`;
    `(B':(num->num)->real) jq`;
    `\s. product(1..k) (\j. (gi:real->real^N^N) s$((ip:num->num) j)$((jq:num->num) j))`;
    `sum(1..k) (\m. product(1..k) (\j. if j = m
                                        then (gi':real^N^N)$((ip:num->num) j)$((jq:num->num) j)
                                        else (gi:real->real^N^N) t$(ip j)$(jq j)))`;
    `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\s. (A:real->(num->real^N)->real) s (\m. basis((ip:num->num) m))`;
    `(A':(num->num)->real) ip`;
    `\s. (B:real->(num->real^N)->real) s (\m. basis((jq:num->num) m)) *
         product(1..k) (\j. (gi:real->real^N^N) s$((ip:num->num) j)$((jq:num->num) j))`;
    `(B:real->(num->real^N)->real) t (\m. basis((jq:num->num) m)) *
     sum(1..k) (\m. product(1..k) (\j. if j = m
                                        then (gi':real^N^N)$((ip:num->num) j)$((jq:num->num) j)
                                        else (gi:real->real^N^N) t$(ip j)$(jq j))) +
     (B':(num->num)->real) jq * product(1..k) (\j. gi t$(ip j)$(jq j))`;
    `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net
                   ==> (f has_real_derivative y) net`) THEN
  CONV_TAC REAL_RING);;

(* ========================================================================= *)
(* A weighted slot (rfa_ltq) with weight gi Wm gi is the full                *)
(* contraction against the action of Wm on that slot (rfa_qacte).            *)
(* ========================================================================= *)

let RFA_PRODUCT_SLOT = prove
 (`!k m (f:num->real) g.
        1 <= m /\ m <= k
        ==> product(1..k) (\j. if j = m then g j else f j) =
            g m * product((1..k) DELETE m) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j. if j = m then (g:num->real) j else f j`; `1..k`; `m:num`]
         PRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  REWRITE_TAC[IN_DELETE] THEN SIMP_TAC[]);;

let RFA_PRODUCT_SPLIT = prove
 (`!k m (f:num->real).
        1 <= m /\ m <= k
        ==> product(1..k) f = f m * product((1..k) DELETE m) f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_DELETE THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG]);;

let RFA_LTQ_QACT_CORE = prove
 (`!k m (g:num->num->real) (w:num->num->real) (Bf:(num->num)->real)
    (PD:(num->num)->real) p.
        1 <= m /\ m <= k /\ (!J c. PD (\j. if j = m then c else J j) = PD J)
        ==> sum (index_tuples k (:N))
             (\J. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                    g a b * w (J m) a * Bf (\j. if j = m then b else J j))) *
                  (g p (J m) * PD J)) =
            sum (index_tuples k (:N))
             (\J. Bf J * sum(1..dimindex(:N)) (\c. g p c *
                    sum(1..dimindex(:N)) (\a. w c a * g a (J m))) * PD J)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!(J:num->num) c. (\j. if j = m then J m else if j = m then c else J j) = J`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `m:num`;
    `\J b. sum(1..dimindex(:N)) (\a. ((g:num->num->real) a b * (w:num->num->real) (J m) a *
             (Bf:(num->num)->real) (\j. if j = m then b else J j)) *
             (g p (J m) * (PD:(num->num)->real) J))`] RFA_TUPLE_SLOT_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (index_tuples k (:N))
     (\J. sum(1..dimindex(:N)) (\b. sum(1..dimindex(:N)) (\a.
            ((g:num->num->real) a b * (w:num->num->real) (J m) a *
             (Bf:(num->num)->real) (\j. if j = m then b else J j)) *
            (g p (J m) * (PD:(num->num)->real) J))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `J:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `J:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  CONV_TAC REAL_RING);;

let RFA_LTQ_QACT = prove
 (`!k m (gi:real^N^N) Wm (A:(num->real^N)->real) B.
        1 <= m /\ m <= k
        ==> rfa_ltq k gi (gi ** Wm ** gi) m A B =
            rfa_ltc k gi A (rfa_qacte gi Wm m B)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ltq; rfa_ltc] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (index_tuples k (:N))
     (\J. (B:(num->real^N)->real) (\j. basis(J j)) *
          sum(1..dimindex(:N)) (\c. (gi:real^N^N)$((ip:num->num) m)$c *
            sum(1..dimindex(:N)) (\a. (Wm:real^N^N)$c$a * gi$a$(J m))) *
          product((1..k) DELETE m) (\j. gi$(ip j)$(J j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `1 <= (ip:num->num) m /\ ip m <= dimindex(:N) /\
      1 <= (jq:num->num) m /\ jq m <= dimindex(:N)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((gi:real^N^N) ** (Wm:real^N^N) ** gi)$((ip:num->num) m)$((jq:num->num) m) =
      sum(1..dimindex(:N)) (\c. gi$(ip m)$c *
        sum(1..dimindex(:N)) (\a. Wm$c$a * gi$a$(jq m)))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RFA_PRODUCT_SLOT];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (index_tuples k (:N))
     (\J. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
            (gi:real^N^N)$a$b * (Wm:real^N^N)$(J m)$a *
            (B:(num->real^N)->real) (\j. basis(if j = m then b else J j)))) *
          (gi$((ip:num->num) m)$(J m) *
           product((1..k) DELETE m) (\j. gi$(ip j)$(J j))))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `\a b. (gi:real^N^N)$a$b`;
                   `\c a. (Wm:real^N^N)$c$a`;
                   `\J. (B:(num->real^N)->real) (\j. basis(J j))`;
                   `\J. product((1..k) DELETE m)
                          (\j. (gi:real^N^N)$((ip:num->num) j)$(J j))`;
                   `(ip:num->num) m`] RFA_LTQ_QACT_CORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
      REWRITE_TAC[IN_DELETE] THEN SIMP_TAC[];
      BETA_TAC THEN DISCH_THEN MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `J:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `1 <= (J:num->num) m /\ J m <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `m:num`;
                 `\j. (gi:real^N^N)$((ip:num->num) j)$((J:num->num) j)`]
         RFA_PRODUCT_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfa_qacte] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX; COND_RAND]);;

(* ========================================================================= *)
(* Algebra for metric compatibility.  The weighted slot is                   *)
(* linear in the weight; substituting M e_(i l) in slot l of either factor   *)
(* is a weighted slot; the derivative of the metric is expressed through the *)
(* Christoffel matrix.                                                       *)
(* ========================================================================= *)

let RFA_LTQ_ALT = prove
 (`!k m (gi:real^N^N) X (A:(num->real^N)->real) B.
        1 <= m /\ m <= k
        ==> rfa_ltq k gi X m A B =
            sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. A (\m. basis(ip m)) * B (\m. basis(jq m)) *
                     X$(ip m)$(jq m) *
                     product((1..k) DELETE m) (\j. gi$(ip j)$(jq j))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ltq] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[RFA_PRODUCT_SLOT]);;

let RFA_LTQ_CANCEL = prove
 (`!k m (gi:real^N^N) X Y Z (A:(num->real^N)->real) B.
        1 <= m /\ m <= k /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> X$i$j + Y$i$j + Z$i$j = &0)
        ==> rfa_ltq k gi X m A B + rfa_ltq k gi Y m A B + rfa_ltq k gi Z m A B = &0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RFA_LTQ_ALT] THEN
  REWRITE_TAC[GSYM(MATCH_MP SUM_ADD (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM(MATCH_MP SUM_ADD (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(X:real^N^N)$((ip:num->num) m)$((jq:num->num) m) +
    (Y:real^N^N)$(ip m)$(jq m) + (Z:real^N^N)$(ip m)$(jq m) = &0`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE];
    CONV_TAC REAL_RING]);;

(* Slot substitution in the first factor, abstract form. *)

let RFA_SLOT_CORE_A = prove
 (`!k l (Mf:num->num->real) (g:num->num->real) (Af:(num->num)->real)
    (Bf:(num->num)->real) (PD:(num->num)->(num->num)->real).
        1 <= l /\ l <= k /\
        (!ip jq c. PD (\j. if j = l then c else ip j) jq = PD ip jq)
        ==> sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. sum(1..dimindex(:N))
                       (\d. Mf d (ip l) * Af (\j. if j = l then d else ip j)) *
                     Bf jq * (g (ip l) (jq l) * PD ip jq))) =
            sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. Af ip * Bf jq *
                     sum(1..dimindex(:N)) (\d. Mf (ip l) d * g d (jq l)) *
                     PD ip jq))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!(J:num->num) c. (\j. if j = l then J l else if j = l then c else J j) = J`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `l:num`;
    `\ip d. sum (index_tuples k (:N))
              (\jq. ((Mf:num->num->real) d (ip l) *
                     (Af:(num->num)->real) (\j. if j = l then d else ip j)) *
                    ((Bf:(num->num)->real) jq *
                     ((g:num->num->real) (ip l) (jq l) *
                      (PD:(num->num)->(num->num)->real) ip jq)))`]
    RFA_TUPLE_SLOT_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (index_tuples k (:N))
     (\ip. sum(1..dimindex(:N))
       (\d. sum (index_tuples k (:N))
              (\jq. ((Mf:num->num->real) d (ip l) *
                     (Af:(num->num)->real) (\j. if j = l then d else ip j)) *
                    ((Bf:(num->num)->real) jq *
                     ((g:num->num->real) (ip l) (jq l) *
                      (PD:(num->num)->(num->num)->real) ip jq)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN
    GEN_REWRITE_TAC LAND_CONV
     [MATCH_MP SUM_SWAP (CONJ (SPEC `k:num` LRG_INDEX_TUPLES_FINITE)
                              (SPECL [`1`; `dimindex(:N)`] FINITE_NUMSEG))] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_SWAP (CONJ (SPECL [`1`; `dimindex(:N)`] FINITE_NUMSEG)
                            (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  CONV_TAC REAL_RING);;

(* Slot substitution in the second factor, abstract form. *)

let RFA_SLOT_CORE_B = prove
 (`!k l (Mf:num->num->real) (g:num->num->real) (Af:(num->num)->real)
    (Bf:(num->num)->real) (PD:(num->num)->(num->num)->real).
        1 <= l /\ l <= k /\
        (!ip jq c. PD ip (\j. if j = l then c else jq j) = PD ip jq)
        ==> sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. Af ip *
                     sum(1..dimindex(:N))
                       (\d. Mf d (jq l) * Bf (\j. if j = l then d else jq j)) *
                     (g (ip l) (jq l) * PD ip jq))) =
            sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. Af ip * Bf jq *
                     sum(1..dimindex(:N)) (\d. g (ip l) d * Mf (jq l) d) *
                     PD ip jq))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!(J:num->num) c. (\j. if j = l then J l else if j = l then c else J j) = J`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`k:num`; `l:num`;
    `\jq d. (Af:(num->num)->real) ip *
            (((Mf:num->num->real) d (jq l) *
              (Bf:(num->num)->real) (\j. if j = l then d else jq j)) *
             ((g:num->num->real) ((ip:num->num) l) (jq l) *
              (PD:(num->num)->(num->num)->real) ip jq))`]
    RFA_TUPLE_SLOT_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (index_tuples k (:N))
     (\jq. sum(1..dimindex(:N))
       (\d. (Af:(num->num)->real) ip *
            (((Mf:num->num->real) d (jq l) *
              (Bf:(num->num)->real) (\j. if j = l then d else jq j)) *
             ((g:num->num->real) ((ip:num->num) l) (jq l) *
              (PD:(num->num)->(num->num)->real) ip jq))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  CONV_TAC REAL_RING);;

let RFA_LTQ_SLOT_A = prove
 (`!k l (gi:real^N^N) (M:real^N^N) (A:(num->real^N)->real) B.
        1 <= l /\ l <= k /\
        (!u. linear (\v. lift(A (\j. if j = l then v else u j))))
        ==> sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. A (\j. if j = l then M ** basis(ip l) else basis(ip j)) *
                     B (\m. basis(jq m)) * product(1..k) (\j. gi$(ip j)$(jq j)))) =
            rfa_ltq k gi (M ** gi) l A B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RFA_LTQ_ALT] THEN
  MP_TAC(ISPECL [`k:num`; `l:num`; `\a b. (M:real^N^N)$a$b`; `\a b. (gi:real^N^N)$a$b`;
                 `\J. (A:(num->real^N)->real) (\j. basis(J j))`;
                 `\J. (B:(num->real^N)->real) (\j. basis(J j))`;
                 `\ip jq. product((1..k) DELETE l)
                            (\j. (gi:real^N^N)$((ip:num->num) j)$((jq:num->num) j))`]
         RFA_SLOT_CORE_A) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    REWRITE_TAC[IN_DELETE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  BETA_TAC THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (lhand(concl th)) THEN
                       CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[th]]) THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `1 <= (ip:num->num) l /\ ip l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `l:num`;
                   `\j. (gi:real^N^N)$((ip:num->num) j)$((jq:num->num) j)`]
           RFA_PRODUCT_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`A:(num->real^N)->real`; `l:num`; `\j. basis((ip:num->num) j):real^N`;
                   `(M:real^N^N) ** basis((ip:num->num) l)`] LRG_SLOT_EXPAND) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `\j. basis((ip:num->num) j):real^N`) THEN REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o BETA_RULE)] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\q. ((M:real^N^N) ** basis((ip:num->num) l))$q *
             (A:(num->real^N)->real) (\j. if j = l then basis q else basis(ip j))) =
      sum(1..dimindex(:N))
        (\d. M$d$(ip l) * A (\j. basis(if j = l then d else ip j)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA; COND_RAND];
      REWRITE_TAC[]];
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `1 <= (ip:num->num) l /\ ip l <= dimindex(:N) /\
                  1 <= (jq:num->num) l /\ jq l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT]]);;

let RFA_LTQ_SLOT_B = prove
 (`!k l (gi:real^N^N) (M:real^N^N) (A:(num->real^N)->real) B.
        1 <= l /\ l <= k /\
        (!u. linear (\v. lift(B (\j. if j = l then v else u j))))
        ==> sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. A (\m. basis(ip m)) *
                     B (\j. if j = l then M ** basis(jq l) else basis(jq j)) *
                     product(1..k) (\j. gi$(ip j)$(jq j)))) =
            rfa_ltq k gi (gi ** transp M) l A B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RFA_LTQ_ALT] THEN
  MP_TAC(ISPECL [`k:num`; `l:num`; `\a b. (M:real^N^N)$a$b`; `\a b. (gi:real^N^N)$a$b`;
                 `\J. (A:(num->real^N)->real) (\j. basis(J j))`;
                 `\J. (B:(num->real^N)->real) (\j. basis(J j))`;
                 `\ip jq. product((1..k) DELETE l)
                            (\j. (gi:real^N^N)$((ip:num->num) j)$((jq:num->num) j))`]
         RFA_SLOT_CORE_B) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    REWRITE_TAC[IN_DELETE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  BETA_TAC THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (lhand(concl th)) THEN
                       CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[th]]) THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `1 <= (jq:num->num) l /\ jq l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `l:num`;
                   `\j. (gi:real^N^N)$((ip:num->num) j)$((jq:num->num) j)`]
           RFA_PRODUCT_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`B:(num->real^N)->real`; `l:num`; `\j. basis((jq:num->num) j):real^N`;
                   `(M:real^N^N) ** basis((jq:num->num) l)`] LRG_SLOT_EXPAND) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `\j. basis((jq:num->num) j):real^N`) THEN REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o BETA_RULE)] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\q. ((M:real^N^N) ** basis((jq:num->num) l))$q *
             (B:(num->real^N)->real) (\j. if j = l then basis q else basis(jq j))) =
      sum(1..dimindex(:N))
        (\d. M$d$(jq l) * B (\j. basis(if j = l then d else jq j)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA; COND_RAND];
      REWRITE_TAC[]];
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `1 <= (ip:num->num) l /\ ip l <= dimindex(:N) /\
                  1 <= (jq:num->num) l /\ jq l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[TRANSP_COMPONENT]]);;

(* The Christoffel matrix in direction v: column a is Gamma(v, e_a). *)

let RFA_CHRIST_MATRIX_BASIS = prove
 (`!(G:real^N->real^N^N) y v a.
        1 <= a /\ a <= dimindex(:N)
        ==> ((lambda d a. (christoffel G y v (basis a))$d):real^N^N) ** basis a =
            christoffel G y v (basis a)`,
  SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; CART_EQ; LAMBDA_BETA]);;

let RFA_MDERIV_MATRIX = prove
 (`!U (G:real^N->real^N^N) y v.
        metric_field U G /\ y IN U
        ==> mderiv G y v =
            transp((lambda d a. (christoffel G y v (basis a))$d):real^N^N) ** G y +
            G y ** ((lambda d a. (christoffel G y v (basis a))$d):real^N^N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> (G:real^N->real^N^N) y$i$j = G y$j$i`
  (LABEL_TAC "sym") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `basis i:real^N`; `basis j:real^N`] LRG_METRIC_SYM) THEN
    ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mderiv (G:real^N->real^N^N) y v$a$b =
    (G y ** christoffel G y v (basis a))$b + (G y ** christoffel G y v (basis b))$a`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `basis a:real^N`; `v:real^N`; `basis b:real^N`]
           LRG_MDERIV_CHRISTOFFEL) THEN
    ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX; DOT_BASIS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; LRG_MATRIX_MUL_COMPONENT;
               MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
  BINOP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN
  STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[TRANSP_COMPONENT; LAMBDA_BETA] THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y$d$b = G y$b$d` SUBST1_TAC THENL
   [USE_THEN "sym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let RFA_GDG_MATRIX = prove
 (`!U (G:real^N->real^N^N) y v.
        metric_field U G /\ y IN U
        ==> matrix_inv(G y) ** mderiv G y v ** matrix_inv(G y) =
            matrix_inv(G y) **
            transp((lambda d a. (christoffel G y v (basis a))$d):real^N^N) +
            ((lambda d a. (christoffel G y v (basis a))$d):real^N^N) **
            matrix_inv(G y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`]
         RFA_MDERIV_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y ** matrix_inv(G y) = mat 1 /\
                matrix_inv(G y) ** G y = mat 1` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_INV THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ADD_RDISTRIB; MATRIX_ADD_LDISTRIB] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_RID];
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_LID]]);;

(* ========================================================================= *)
(* Metric compatibility.  The directional derivative of the                  *)
(* inner product of two tensor fields is the sum of the inner products with  *)
(* the covariant derivatives in that direction.                              *)
(* ========================================================================= *)

let RFA_SUM2_ADD = prove
 (`!s t (f:A->B->real) g.
        FINITE s /\ FINITE t
        ==> sum s (\i. sum t (\j. f i j + g i j)) =
            sum s (\i. sum t (\j. f i j)) + sum s (\i. sum t (\j. g i j))`,
  SIMP_TAC[SUM_ADD]);;

let RFA_SUM_SWAP3 = prove
 (`!s t r (f:C->A->B->real).
        FINITE s /\ FINITE t /\ FINITE r
        ==> sum s (\i. sum t (\j. sum r (\l. f l i j))) =
            sum r (\l. sum s (\i. sum t (\j. f l i j)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\i. sum r (\l. sum t (\j. (f:C->A->B->real) l i j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN BETA_TAC THEN
    GEN_REWRITE_TAC LAND_CONV
     [MATCH_MP SUM_SWAP (CONJ (ASSUME `FINITE(t:B->bool)`) (ASSUME `FINITE(r:C->bool)`))] THEN
    REWRITE_TAC[];
    GEN_REWRITE_TAC LAND_CONV
     [MATCH_MP SUM_SWAP (CONJ (ASSUME `FINITE(s:A->bool)`) (ASSUME `FINITE(r:C->bool)`))] THEN
    REWRITE_TAC[]]);;

let RFA_POINT_EXPAND = prove
 (`!a b d e p (c:num->real) f n.
        ((a + sum(1..n) c) * b + d * (e + sum(1..n) f)) * p =
        (a * b * p + d * e * p) + sum(1..n) (\l. c l * b * p + d * f l * p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_RMUL; ETA_AX] THEN
  CONV_TAC REAL_RING);;

let RFA_MC_SLOTS = prove
 (`!k (gi:real^N^N) (M:real^N^N) (A:(num->real^N)->real) B.
        (!u l. 1 <= l /\ l <= k ==> linear (\v. lift(A (\j. if j = l then v else u j)))) /\
        (!u l. 1 <= l /\ l <= k ==> linear (\v. lift(B (\j. if j = l then v else u j))))
        ==> sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. sum(1..k)
                 (\l. A (\j. if j = l then M ** basis(ip l) else basis(ip j)) *
                      B (\m. basis(jq m)) * product(1..k) (\j. gi$(ip j)$(jq j)) +
                      A (\m. basis(ip m)) *
                      B (\j. if j = l then M ** basis(jq l) else basis(jq j)) *
                      product(1..k) (\j. gi$(ip j)$(jq j))))) =
            sum(1..k) (\l. rfa_ltq k gi (M ** gi) l A B +
                           rfa_ltq k gi (gi ** transp M) l A B)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP RFA_SUM_SWAP3
     (CONJ (SPEC `k:num` LRG_INDEX_TUPLES_FINITE)
           (CONJ (SPEC `k:num` LRG_INDEX_TUPLES_FINITE) (SPECL [`1`; `k:num`] FINITE_NUMSEG)))] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[MATCH_MP RFA_SUM2_ADD (CONJ (SPEC `k:num` LRG_INDEX_TUPLES_FINITE)
                                          (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC RFA_LTQ_SLOT_A THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC RFA_LTQ_SLOT_B THEN ASM_SIMP_TAC[]]);;

let RFA_MC_ALG = prove
 (`!k (gi:real^N^N) (M:real^N^N) (Z:real^N^N) (A:(num->real^N)->real) B
    (TA:(num->num)->real) (TB:(num->num)->real).
        (!u l. 1 <= l /\ l <= k ==> linear (\v. lift(A (\j. if j = l then v else u j)))) /\
        (!u l. 1 <= l /\ l <= k ==> linear (\v. lift(B (\j. if j = l then v else u j)))) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> (M ** gi)$i$j + (gi ** transp M)$i$j + Z$i$j = &0)
        ==> sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. ((TA ip + sum(1..k) (\l. A (\j. if j = l then M ** basis(ip l)
                                                     else basis(ip j)))) *
                      B (\m. basis(jq m)) +
                      A (\m. basis(ip m)) *
                      (TB jq + sum(1..k) (\l. B (\j. if j = l then M ** basis(jq l)
                                                     else basis(jq j))))) *
                     product(1..k) (\j. gi$(ip j)$(jq j)))) +
            sum(1..k) (\l. rfa_ltq k gi Z l A B) =
            sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. TA ip * B (\m. basis(jq m)) * product(1..k) (\j. gi$(ip j)$(jq j)))) +
            sum (index_tuples k (:N))
             (\ip. sum (index_tuples k (:N))
               (\jq. A (\m. basis(ip m)) * TB jq * product(1..k) (\j. gi$(ip j)$(jq j))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RFA_POINT_EXPAND] THEN BETA_TAC THEN
  REWRITE_TAC[MATCH_MP RFA_SUM2_ADD (CONJ (SPEC `k:num` LRG_INDEX_TUPLES_FINITE)
                                          (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  ASM_SIMP_TAC[RFA_MC_SLOTS] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `z = &0 ==> x + y + z = x + y`) THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  MATCH_MP_TAC RFA_LTQ_CANCEL THEN ASM_REWRITE_TAC[]);;

let RFA_LTINNER_SMOOTH = prove
 (`!k U (G:real^N->real^N^N) tf tg.
        metric_field U G /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\
        (!u. smooth_map_on U (\y. lift(tg y u)))
        ==> smooth_map_on U (\y. lift(ltinner k G tf tg y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[ltinner] THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
  ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN X_GEN_TAC `i:num->num` THEN
  DISCH_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
  ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_PRODUCT_REAL THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let RFA_LTINNER_SYM = prove
 (`!k U (G:real^N->real^N^N) tf tg y.
        metric_field U G /\ y IN U
        ==> ltinner k G tf tg y = ltinner k G tg tf y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltinner] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_SWAP (CONJ (SPEC `k:num` LRG_INDEX_TUPLES_FINITE)
                            (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `product(1..k) (\m. matrix_inv((G:real^N->real^N^N) y)$((j:num->num) m)$((i:num->num) m)) =
    product(1..k) (\m. matrix_inv(G y)$(i m)$(j m))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    CONV_TAC REAL_RING]);;

let RFA_LINE_DERIV_SMOOTH = prove
 (`!U (f:real^N->real) y v.
        open U /\ smooth_map_on U (\x. lift(f x)) /\ y IN U
        ==> ((\s. f(y + s % v)) has_real_derivative
             drop(frechet_derivative (\z. lift(f z)) (at y) v)) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. lift((f:real^N->real) z)`;
                 `frechet_derivative (\z. lift((f:real^N->real) z)) (at y)`;
                 `y:real^N`; `v:real^N`; `&0`] RFA_LINE_DERIVATIVE) THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_DIRDERIV_LNABLA = prove
 (`!k U (G:real^N->real^N^N) tf y v ip.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U /\
        ip IN index_tuples k (:N)
        ==> drop(frechet_derivative (\z. lift(tf z (\m. basis(ip m)))) (at y) v) =
            lnabla k G tf y (\m. if m = k + 1 then v else basis(ip m)) +
            sum(1..k) (\l. tf y (\j. if j = l
                                    then ((lambda d a. (christoffel G y v (basis a))$d)
                                          :real^N^N) ** basis(ip l)
                                    else basis(ip j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[lnabla] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. lift((tf:real^N->(num->real^N)->real) z
                 (\m. if m = k + 1 then v else basis((ip:num->num) m)))) (at y) =
    frechet_derivative (\z. lift(tf z (\m. basis(ip m)))) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `s1 = s2 ==> d = (d - s1) + s2`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `~(i = k + 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= (ip:num->num) i /\ ip i <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_CHRIST_MATRIX_BASIS] THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let RFA_LTINNER_MC = prove
 (`!k U (G:real^N->real^N^N) tf tg y v.
        metric_field U G /\ ltensor_field k U tf /\ ltensor_field k U tg /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\
        (!u. smooth_map_on U (\x. lift(tg x u))) /\ y IN U
        ==> drop(frechet_derivative (\z. lift(ltinner k G tf tg z)) (at y) v) =
            ltinner k G (\z u. lnabla k G tf z (\m. if m = k + 1 then v else u m)) tg y +
            ltinner k G tf (\z u. lnabla k G tg z (\m. if m = k + 1 then v else u m)) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z. ltinner k (G:real^N->real^N^N) tf tg z`;
                 `y:real^N`; `v:real^N`] RFA_LINE_DERIV_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LTINNER_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "d1") THEN
  MP_TAC(ISPECL [`k:num`; `\s. matrix_inv((G:real^N->real^N^N)(y + s % v))`;
                 `--(matrix_inv((G:real^N->real^N^N) y) ** mderiv G y v ** matrix_inv(G y))`;
                 `\s. (tf:real^N->(num->real^N)->real)(y + s % v)`;
                 `\ip. drop(frechet_derivative
                         (\z. lift((tf:real^N->(num->real^N)->real) z (\m. basis(ip m))))
                         (at y) v)`;
                 `\s. (tg:real^N->(num->real^N)->real)(y + s % v)`;
                 `\ip. drop(frechet_derivative
                         (\z. lift((tg:real^N->(num->real^N)->real) z (\m. basis(ip m))))
                         (at y) v)`;
                 `&0`] RFA_LTC_DERIV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN
      MP_TAC(ISPECL [`\x. lift(matrix_inv((G:real^N->real^N^N) x)$a$b)`;
                     `\h. lift(--((matrix_inv((G:real^N->real^N^N) y) ** mderiv G y h **
                                  matrix_inv(G y))$a$b))`;
                     `y:real^N`; `v:real^N`; `&0`] RFA_LINE_DERIVATIVE) THEN
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID; MATRIX_NEG_COMPONENT] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LRG_HAS_DERIVATIVE_GINV_ENTRY THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`U:real^N->bool`;
                       `\x. (tf:real^N->(num->real^N)->real) x (\m. basis((ip:num->num) m))`;
                       `y:real^N`; `v:real^N`] RFA_LINE_DERIV_SMOOTH) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`U:real^N->bool`;
                       `\x. (tg:real^N->(num->real^N)->real) x (\m. basis((ip:num->num) m))`;
                       `y:real^N`; `v:real^N`] RFA_LINE_DERIV_SMOOTH) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; GSYM RFA_LTINNER_LTC] THEN
  DISCH_THEN(LABEL_TAC "d2") THEN
  USE_THEN "d1" (fun th1 -> USE_THEN "d2" (fun th2 ->
    MP_TAC(MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL (CONJ th1 th2)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!ip. ip IN index_tuples k (:N)
         ==> drop(frechet_derivative
                   (\z. lift((tf:real^N->(num->real^N)->real) z (\m. basis(ip m))))
                   (at y) v) =
             lnabla k G tf y (\m. if m = k + 1 then v else basis(ip m)) +
             sum(1..k) (\l. tf y (\j. if j = l
                                     then ((lambda d a. (christoffel G y v (basis a))$d)
                                           :real^N^N) ** basis(ip l)
                                     else basis(ip j)))`
  (LABEL_TAC "dA") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_DIRDERIV_LNABLA THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ip. ip IN index_tuples k (:N)
         ==> drop(frechet_derivative
                   (\z. lift((tg:real^N->(num->real^N)->real) z (\m. basis(ip m))))
                   (at y) v) =
             lnabla k G tg y (\m. if m = k + 1 then v else basis(ip m)) +
             sum(1..k) (\l. tg y (\j. if j = l
                                     then ((lambda d a. (christoffel G y v (basis a))$d)
                                           :real^N^N) ** basis(ip l)
                                     else basis(ip j)))`
  (LABEL_TAC "dB") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_DIRDERIV_LNABLA THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `matrix_inv((G:real^N->real^N^N) y)`;
                 `(lambda d a. (christoffel (G:real^N->real^N^N) y v (basis a))$d):real^N^N`;
                 `--(matrix_inv((G:real^N->real^N^N) y) ** mderiv G y v ** matrix_inv(G y))`;
                 `(tf:real^N->(num->real^N)->real) y`; `(tg:real^N->(num->real^N)->real) y`;
                 `\ip. lnabla k (G:real^N->real^N^N) tf y
                         (\m. if m = k + 1 then v else basis(ip m))`;
                 `\jq. lnabla k (G:real^N->real^N^N) tg y
                         (\m. if m = k + 1 then v else basis(jq m))`]
         RFA_MC_ALG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
      REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `ltensor_field k U (tg:real^N->(num->real^N)->real)` THEN
      REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`]
             RFA_GDG_MATRIX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[MATRIX_NEG_COMPONENT; MATRIX_ADD_COMPONENT] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  BETA_TAC THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (lhand(concl th)) THEN
                       CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[th; ltinner]]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  USE_THEN "dA" (fun th ->
    REWRITE_TAC[MATCH_MP th (ASSUME `(ip:num->num) IN index_tuples k (:N)`)]) THEN
  USE_THEN "dB" (fun th ->
    REWRITE_TAC[MATCH_MP th (ASSUME `(jq:num->num) IN index_tuples k (:N)`)]));;

(* ========================================================================= *)
(* Fixing the last slot of a tensor field; the covariant                     *)
(* derivative of a slot-fixed field; the squared norm of a (k+1)-tensor as a *)
(* contraction of slot-fixed inner products.                                 *)
(* ========================================================================= *)

let RFA_SUM_NUMSEG_LAST = prove
 (`!(f:num->real) k. sum(1..k + 1) f = sum(1..k) f + f(k + 1)`,
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`]);;

let RFA_FIX_SLOT_FIELD = prove
 (`!k U (sf:real^N->(num->real^N)->real) w.
        ltensor_field (k + 1) U sf /\ (!u. smooth_map_on U (\x. lift(sf x u)))
        ==> ltensor_field k U (\z u. sf z (\m. if m = k + 1 then w else u m)) /\
            (!u. smooth_map_on U (\x. lift(sf x (\m. if m = k + 1 then w else u m))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `ltensor_field (k + 1) U (sf:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dep") (LABEL_TAC "lin")) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->real^N`; `u':num->real^N`] THEN DISCH_TAC THEN
    USE_THEN "dep" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!v:real^N. (\m. if m = k + 1 then w else if m = i then v else (u:num->real^N) m) =
                 (\j. if j = i then v else if j = k + 1 then w else u j)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(i = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "lin" (MP_TAC o SPECL [`i:num`; `\m. if m = k + 1 then (w:real^N) else u m`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]]);;

let RFA_LNABLA_FIX_SLOT = prove
 (`!k U (G:real^N->real^N^N) sf w y u.
        open U /\ ltensor_field (k + 1) U sf /\ y IN U
        ==> lnabla k G (\z u. sf z (\m. if m = k + 1 then w else u m)) y u =
            lnabla (k + 1) G sf y
              (\m. if m = k + 1 then w else if m = k + 2 then u(k + 1) else u m) +
            sf y (\m. if m = k + 1 then christoffel G y (u(k + 1)) w else u m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z (u1:num->real^N) u2.
        z IN U /\ (!m. 1 <= m /\ m <= k + 1 ==> u1 m = u2 m)
        ==> (sf:real^N->(num->real^N)->real) z u1 = sf z u2`
  (LABEL_TAC "dep") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ltensor_field (k + 1) U (sf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lnabla; RFA_SUM_NUMSEG_LAST; ARITH_RULE `(k + 1) + 1 = k + 2`;
              ARITH_RULE `~(k + 2 = k + 1)`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `d1 = d2 /\ s1 = s2 /\ e1 = e2 ==> d1 - s1 = (d2 - (s2 + e1)) + e2`) THEN
  REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    USE_THEN "dep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(m = k + 2)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(i = k + 1) /\ ~(i = k + 2)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    USE_THEN "dep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `m:num = k + 1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(m = k + 2)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    USE_THEN "dep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `m:num = k + 1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(m = k + 2)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

let RFA_PRODUCT_NUMSEG_LAST = prove
 (`!(f:num->real) k. product(1..k + 1) f = product(1..k) f * f(k + 1)`,
  REWRITE_TAC[GSYM ADD1; PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`]);;

let RFA_SUM4_REORDER = prove
 (`!s t (f:A->B->A->B->real).
        FINITE s /\ FINITE t
        ==> sum s (\i. sum t (\a. sum s (\j. sum t (\b. f i a j b)))) =
            sum t (\a. sum t (\b. sum s (\i. sum s (\j. f i a j b))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_SWAP (CONJ (ASSUME `FINITE(s:A->bool)`) (ASSUME `FINITE(t:B->bool)`))] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `a:B` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `s:A->bool`; `t:B->bool`;
                 `\b i j. (f:A->B->A->B->real) i a j b`] RFA_SUM_SWAP3) THEN
  ASM_REWRITE_TAC[]);;

let RFA_LTNORM2_SUC = prove
 (`!k (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) y.
        ltnorm2 (k + 1) G sf y =
        sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv(G y)$a$b *
          ltinner k G (\z u. sf z (\m. if m = k + 1 then basis a else u m))
                      (\z u. sf z (\m. if m = k + 1 then basis b else u m)) y))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ltnorm2; ltinner; LRG_SUM_INDEX_TUPLES_SUC; RFA_PRODUCT_NUMSEG_LAST] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC[RFA_SUM4_REORDER; LRG_INDEX_TUPLES_FINITE; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `product(1..k) (\m. matrix_inv((G:real^N->real^N^N) y)
                         $(if m = k + 1 then a else (ip:num->num) m)
                         $(if m = k + 1 then b else (jq:num->num) m)) =
    product(1..k) (\m. matrix_inv(G y)$(ip m)$(jq m))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COND_RAND] THEN CONV_TAC REAL_RING);;

(* ========================================================================= *)
(* Linearity of the inner product in the second argument, and                *)
(* the first and second covariant derivatives of a squared norm.             *)
(* ========================================================================= *)

let RFA_LTNORM2_LTINNER = prove
 (`!k (G:real^N->real^N^N) tf y. ltnorm2 k G tf y = ltinner k G tf tf y`,
  REWRITE_TAC[ltnorm2; ltinner]);;

let RFA_LTINNER_RLOCAL = prove
 (`!k (G:real^N->real^N^N) tf tg tg' y.
        (!u. tg y u = tg' y u) ==> ltinner k G tf tg y = ltinner k G tf tg' y`,
  SIMP_TAC[ltinner]);;

let RFA_LTINNER_RADD = prove
 (`!k (G:real^N->real^N^N) tf (f:real^N->(num->real^N)->real) g y.
        ltinner k G tf (\z u. f z u + g z u) y =
        ltinner k G tf f y + ltinner k G tf g y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltinner] THEN
  REWRITE_TAC[GSYM(MATCH_MP SUM_ADD (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  CONV_TAC REAL_RING);;

let RFA_LTINNER_RCMUL = prove
 (`!k (G:real^N->real^N^N) tf (f:real^N->(num->real^N)->real) c y.
        ltinner k G tf (\z u. c * f z u) y = c * ltinner k G tf f y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltinner; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  CONV_TAC REAL_RING);;

let RFA_LTINNER_RSUM = prove
 (`!k (G:real^N->real^N^N) tf (Fa:A->real^N->(num->real^N)->real) s y.
        FINITE s
        ==> ltinner k G tf (\z u. sum s (\a. Fa a z u)) y =
            sum s (\a. ltinner k G tf (Fa a) y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltinner] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC RFA_SUM_SWAP3 THEN ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE]);;

let RFA_FRECHET_LIFT_CMUL = prove
 (`!U (f:real^N->real) c y h.
        open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
        ==> drop(frechet_derivative (\z. lift(c * f z)) (at y) h) =
            c * drop(frechet_derivative (\z. lift(f z)) (at y) h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(c * (f:real^N->real) z)) (at y) =
    (\h. c % frechet_derivative (\z. lift(f z)) (at y) h)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[DROP_CMUL]]);;

let RFA_COND_NEST = prove
 (`!b (x:A) y z. (if b then x else if b then y else z) = (if b then x else z)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let RFA_COND_NEST2 = prove
 (`!b c (x:A) y z w.
        (if b then x else if c then y else if b then z else w) =
        (if b then x else if c then y else w)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* First derivative of a squared norm. *)

let RFA_DNORM2_FORM = prove
 (`!k U (G:real^N->real^N^N) tf z w.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ z IN U
        ==> drop(frechet_derivative (\x. lift(ltnorm2 k G tf x)) (at z) w) =
            &2 * ltinner k G tf
                   (\z' u. lnabla k G tf z' (\m. if m = k + 1 then w else u m)) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LTNORM2_LTINNER] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `tf:real^N->(num->real^N)->real`;
                 `z:real^N`; `w:real^N`] RFA_LTINNER_MC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z' u. lnabla k (G:real^N->real^N^N) tf z'
                           (\m. if m = k + 1 then w else u m)`;
                 `tf:real^N->(num->real^N)->real`; `z:real^N`] RFA_LTINNER_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a = c /\ b = c ==> a + b = &2 * c`) THEN
  CONJ_TAC THEN REFL_TAC);;

(* Second covariant derivative of a squared norm, in the frame slots. *)

let RFA_HESS_NORM2 = prove
 (`!k U (G:real^N->real^N^N) tf y w1 w2.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> lnabla 1 G (\z u. &2 * ltinner k G tf
                         (\z' u'. lnabla k G tf z' (\m. if m = k + 1 then u 1 else u' m)) z)
                   y (\m. if m = 1 then w1 else w2) =
            &2 * ltinner k G (\z u. lnabla k G tf z (\m. if m = k + 1 then w2 else u m))
                             (\z u. lnabla k G tf z (\m. if m = k + 1 then w1 else u m)) y +
            &2 * ltinner k G tf
                   (\z u. lnabla (k + 1) G (lnabla k G tf) z
                            (\m. if m = k + 1 then w1 else if m = k + 2 then w2 else u m)) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. ltensor_field k U (\z u. lnabla k (G:real^N->real^N^N) tf z
                                   (\m. if m = k + 1 then w else u m)) /\
        (!u. smooth_map_on U (\x. lift(lnabla k G tf x (\m. if m = k + 1 then w else u m))))`
  (LABEL_TAC "fix") THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_FIX_SLOT_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. lnabla k (G:real^N->real^N^N)
          (\z u. lnabla k G tf z (\m. if m = k + 1 then w1 else u m)) y
          (\m. if m = k + 1 then w2 else u m) =
        lnabla (k + 1) G (lnabla k G tf) y
          (\m. if m = k + 1 then w1 else if m = k + 2 then w2 else u m) +
        lnabla k G tf y (\m. if m = k + 1 then christoffel G y w2 w1 else u m)`
  (LABEL_TAC "fs") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla k (G:real^N->real^N^N) tf`; `w1:real^N`; `y:real^N`;
                   `\m. if m = k + 1 then (w2:real^N) else u m`] RFA_LNABLA_FIX_SLOT) THEN
    ASM_REWRITE_TAC[RFA_COND_NEST; RFA_COND_NEST2];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [lnabla] THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\z. ltinner k (G:real^N->real^N^N) tf
                        (\z' u'. lnabla k G tf z' (\m. if m = k + 1 then w1 else u' m)) z`;
                 `&2`; `y:real^N`; `w2:real^N`] RFA_FRECHET_LIFT_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LTINNER_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`;
                 `\z' u'. lnabla k (G:real^N->real^N^N) tf z'
                            (\m. if m = k + 1 then w1 else u' m)`;
                 `y:real^N`; `w2:real^N`] RFA_LTINNER_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ltinner k G tf
      (\z u. lnabla k (G:real^N->real^N^N)
               (\z' u'. lnabla k G tf z' (\m. if m = k + 1 then w1 else u' m)) z
               (\m. if m = k + 1 then w2 else u m)) y =
    ltinner k G tf
      (\z u. lnabla (k + 1) G (lnabla k G tf) z
               (\m. if m = k + 1 then w1 else if m = k + 2 then w2 else u m)) y +
    ltinner k G tf
      (\z' u'. lnabla k G tf z' (\m. if m = k + 1 then christoffel G y w2 w1 else u' m)) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM RFA_LTINNER_RADD] THEN MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN
    BETA_TAC THEN USE_THEN "fs" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = a' /\ b = b' /\ c = c' ==> &2 * (a + (b + c)) - &2 * c' = &2 * a' + &2 * b'`) THEN
  REPEAT CONJ_TAC THEN REFL_TAC);;

let RFA_BOCHNER_TRACE = prove
 (`!k U (G:real^N->real^N^N) tf y.
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
              matrix_inv(G y)$i$j *
              (&2 * ltinner k G
                      (\z u. lnabla k G tf z (\m. if m = k + 1 then basis i else u m))
                      (\z u. lnabla k G tf z (\m. if m = k + 1 then basis j else u m)) y +
               &2 * ltinner k G tf
                      (\z u. lnabla (k + 1) G (lnabla k G tf) z
                               (\m. if m = k + 1 then basis j else if m = k + 2 then basis i
                                    else u m)) y))) =
            &2 * ltinner k G tf (ltlap k G tf) y +
            &2 * ltnorm2 (k + 1) G (lnabla k G tf) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LTNORM2_SUC] THEN
  SUBGOAL_THEN
   `ltinner k G tf (ltlap k G tf) y =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      matrix_inv((G:real^N->real^N^N) y)$a$b *
      ltinner k G tf
        (\z u. lnabla (k + 1) G (lnabla k G tf) z
                 (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                      else u m)) y))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `ltinner k G tf
        (\z u. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                 matrix_inv((G:real^N->real^N^N) y)$a$b *
                 lnabla (k + 1) G (lnabla k G tf) z
                   (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                        else u m)))) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN REWRITE_TAC[ltlap; RFA_LNABLA_ITER_2];
      SIMP_TAC[RFA_LTINNER_RSUM; FINITE_NUMSEG; RFA_LTINNER_RCMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      matrix_inv((G:real^N->real^N^N) y)$i$j *
      ltinner k G tf
        (\z u. lnabla (k + 1) G (lnabla k G tf) z
                 (\m. if m = k + 1 then basis j else if m = k + 2 then basis i
                      else u m)) y)) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      matrix_inv(G y)$a$b *
      ltinner k G tf
        (\z u. lnabla (k + 1) G (lnabla k G tf) z
                 (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                      else u m)) y))`
  (LABEL_TAC "swap") THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "swap" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a = &2 * a' /\ b = &2 * b' ==> a + b = &2 * b' + &2 * a'`) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN CONJ_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

(* The Laplacian of a squared norm (Bochner formula, local form). *)

let RFA_LLAP_LTNORM2 = prove
 (`!k U (G:real^N->real^N^N) tf y.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> llap G (ltnorm2 k G tf) y =
            &2 * ltinner k G tf (ltlap k G tf) y +
            &2 * ltnorm2 (k + 1) G (lnabla k G tf) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltnorm2 k (G:real^N->real^N^N) tf`; `y:real^N`] LRG_LLAP_LNABLA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!u. lnabla 1 G (\z u. drop(frechet_derivative
                               (\w. lift(ltnorm2 k (G:real^N->real^N^N) tf w)) (at z) (u 1)))
          y u =
        lnabla 1 G (\z u. &2 * ltinner k G tf
                     (\z' u'. lnabla k G tf z' (\m. if m = k + 1 then u 1 else u' m)) z)
          y u`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_DNORM2_FORM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`] RFA_HESS_NORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC RFA_BOCHNER_TRACE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The action of a 2-tensor on one slot of a k-tensor                        *)
(* (rfa_qact) is a bilinear operation of the class; with the Ricci tensor    *)
(* written as a contraction of Rm it is bilinear in (Rm, T).                 *)
(* ========================================================================= *)

let rfa_qact = new_definition
 `rfa_qact m (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
           (tf:real^N->(num->real^N)->real) y (u:num->real^N) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      matrix_inv(G y)$a$b * sf y (\j. if j = 1 then u m else basis a) *
      tf y (\j. if j = m then basis b else u j)))`;;

let rfa_qsig = new_definition
 `rfa_qsig m = \i. if i = 1 then m else if 2 <= i /\ i <= m then i - 1 else i`;;

let RFA_QSIG_PERMUTES = prove
 (`!m k. 1 <= m /\ m <= k ==> rfa_qsig m permutes 1..k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_qsig] THEN
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\i. if i = m then 1 else if 1 <= i /\ i < m then i + 1 else i` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_QACT_LBILIN = prove
 (`!k m. 1 <= m /\ m <= k
         ==> lbilin_on k 2 k (\(G:real^N->real^N^N) sf tf. rfa_qact m G sf tf)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `2 + k = k + 2`]
          (ISPECL [`2`; `k:num`] RFA_LBILIN_ON_PROD)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `2`; `k:num`; `2`; `m + 2`;
                 `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
                   (tf:real^N->(num->real^N)->real). ltprod 2 sf tf`]
         RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rfa_qsig m` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] RFA_LBILIN_ON_PERM)) THEN
  ASM_SIMP_TAC[RFA_QSIG_PERMUTES] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `sf:real^N->(num->real^N)->real`;
                       `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[ltperm; ltprod; rfa_qact] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [UNDISCH_TAC `ltensor_field 2 U (sf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins; rfa_qsig] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC;
    UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins; rfa_qsig] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC]);;

let RFA_QACT_RIC_LBILIN = prove
 (`!k m. 1 <= m /\ m <= k
         ==> lbilin_on k 4 k
               (\(G:real^N->real^N^N) sf tf.
                  rfa_qact m G (ltcontr G (ltperm (swap(2,3)) sf)) tf)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `m:num`] RFA_QACT_LBILIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SUBST1_CONTR) THEN
  REWRITE_TAC[ARITH_RULE `2 + 2 = 4`] THEN
  DISCH_THEN(MP_TAC o SPEC `swap(2,3)` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] RFA_LBILIN_ON_SUBST1_PERM)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[]]);;

(* The quadratic part of the evolution of |Rm|^2: twice the reaction         *)
(* operator of RFA_LRM4_EVOLUTION plus twice the Ricci action on each of the *)
(* four slots.                                                               *)

let RFA_RMNORM_EVOL_OP = prove
 (`!(B8:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin 4 4 4 B8
        ==> lbilin_on 4 4 4
              (\G sf tf y u. &2 * B8 G sf tf y u +
                             sum(1..4) (\l. &2 * rfa_qact l G
                                         (ltcontr G (ltperm (swap(2,3)) sf)) tf y u))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RFA_LBILIN_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_CMUL THEN MATCH_MP_TAC RFA_LBILIN_ON_LBILIN THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_LBILIN_ON_SUM THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RFA_LBILIN_ON_CMUL THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    EXISTS_TAC `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
                 (tf:real^N->(num->real^N)->real).
                  rfa_qact l G (ltcontr G (ltperm (swap(2,3)) sf)) tf` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_QACT_RIC_LBILIN THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The time derivative of |Rm|^2 along a local Ricci flow.                   *)
(* ========================================================================= *)

let RFA_LTC_RBASIS = prove
 (`!k (gi:real^N^N) (A:(num->real^N)->real) C C'.
        (!jq. jq IN index_tuples k (:N) ==> C (\m. basis(jq m)) = C' (\m. basis(jq m)))
        ==> rfa_ltc k gi A C = rfa_ltc k gi A C'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ltc] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[]);;

let RFA_QACTE_RIC = prove
 (`!k U (G:real^N->real^N^N) tf y l jq.
        metric_field U G /\ y IN U /\ 1 <= l /\ l <= k /\ jq IN index_tuples k (:N)
        ==> rfa_qacte (matrix_inv(G y))
              (--((lambda i j. --(&2) * lricci G y (basis i) (basis j)):real^N^N))
              l (tf y) (\m. basis(jq m)) =
            &2 * rfa_qact l G (ltcontr G (ltperm (swap(2,3)) (lrm4 G))) tf y
                   (\m. basis(jq m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= (jq:num->num) l /\ jq l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
  REWRITE_TAC[rfa_qacte; rfa_qact; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX; MATRIX_NEG_COMPONENT; LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\j. if j = 1 then basis((jq:num->num) l):real^N else basis a`]
         RFA_LRIC2_CONTR) THEN
  ASM_REWRITE_TAC[lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC REAL_RING);;

let RFA_RMNORM2_ALG = prove
 (`!U (G0:real^N->real^N^N) (Bf:real^N->(num->real^N)->real) y.
        metric_field U G0 /\ y IN U
        ==> sum (index_tuples 4 (:N))
             (\ip. sum (index_tuples 4 (:N))
               (\jq. ((ltlap 4 G0 (lrm4 G0) y (\m. basis(ip m)) + Bf y (\m. basis(ip m))) *
                      lrm4 G0 y (\m. basis(jq m)) +
                      lrm4 G0 y (\m. basis(ip m)) *
                      (ltlap 4 G0 (lrm4 G0) y (\m. basis(jq m)) +
                       Bf y (\m. basis(jq m)))) *
                     product(1..4) (\j. matrix_inv(G0 y)$(ip j)$(jq j)))) +
            sum(1..4) (\m. rfa_ltq 4 (matrix_inv(G0 y))
                       (--(matrix_inv(G0 y) **
                           (lambda i j. --(&2) * lricci G0 y (basis i) (basis j)) **
                           matrix_inv(G0 y))) m (lrm4 G0 y) (lrm4 G0 y)) =
            &2 * ltinner 4 G0 (lrm4 G0) (ltlap 4 G0 (lrm4 G0)) y +
            ltinner 4 G0 (lrm4 G0)
              (\z u. &2 * Bf z u +
                     sum(1..4) (\l. &2 * rfa_qact l G0
                                  (ltcontr G0 (ltperm (swap(2,3)) (lrm4 G0)))
                                  (lrm4 G0) z u)) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (index_tuples 4 (:N))
     (\ip. sum (index_tuples 4 (:N))
       (\jq. ((ltlap 4 G0 (lrm4 G0) y (\m. basis(ip m)) +
               (Bf:real^N->(num->real^N)->real) y (\m. basis(ip m))) *
              lrm4 G0 y (\m. basis(jq m)) +
              lrm4 G0 y (\m. basis(ip m)) *
              (ltlap 4 G0 (lrm4 G0) y (\m. basis(jq m)) + Bf y (\m. basis(jq m)))) *
             product(1..4) (\j. matrix_inv((G0:real^N->real^N^N) y)$(ip j)$(jq j)))) =
    &2 * ltinner 4 G0 (lrm4 G0) (ltlap 4 G0 (lrm4 G0)) y +
    &2 * ltinner 4 G0 (lrm4 G0) Bf y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `ltinner 4 G0 (\z u. ltlap 4 G0 (lrm4 G0) z u +
                         (Bf:real^N->(num->real^N)->real) z u) (lrm4 G0) y +
      ltinner 4 (G0:real^N->real^N^N) (lrm4 G0)
        (\z u. ltlap 4 G0 (lrm4 G0) z u + Bf z u) y` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ltinner; GSYM(MATCH_MP RFA_SUM2_ADD
        (CONJ (SPEC `4` LRG_INDEX_TUPLES_FINITE) (SPEC `4` LRG_INDEX_TUPLES_FINITE)))] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC(REAL_RING
       `p = q ==> (a * r + r' * a') * p = a * r * q + r' * a' * q`) THEN
      REFL_TAC;
      MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                     `\z u. ltlap 4 (G0:real^N->real^N^N) (lrm4 G0) z u +
                            (Bf:real^N->(num->real^N)->real) z u`;
                     `lrm4 (G0:real^N->real^N^N)`; `y:real^N`] RFA_LTINNER_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[RFA_LTINNER_RADD; ETA_AX] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..4) (\m. rfa_ltq 4 (matrix_inv((G0:real^N->real^N^N) y))
                 (--(matrix_inv(G0 y) **
                     (lambda i j. --(&2) * lricci G0 y (basis i) (basis j)) **
                     matrix_inv(G0 y))) m (lrm4 G0 y) (lrm4 G0 y)) =
    ltinner 4 G0 (lrm4 G0)
      (\z u. sum(1..4) (\l. &2 * rfa_qact l G0
                              (ltcontr G0 (ltperm (swap(2,3)) (lrm4 G0)))
                              (lrm4 G0) z u)) y`
  SUBST1_TAC THENL
   [SIMP_TAC[RFA_LTINNER_RSUM; FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `--(matrix_inv((G0:real^N->real^N^N) y) **
         (lambda i j. --(&2) * lricci G0 y (basis i) (basis j)) **
         matrix_inv(G0 y)) =
      matrix_inv(G0 y) **
      (--((lambda i j. --(&2) * lricci G0 y (basis i) (basis j)):real^N^N)) **
      matrix_inv(G0 y)`
    SUBST1_TAC THENL [REWRITE_TAC[MATRIX_MUL_LNEG; MATRIX_MUL_RNEG]; ALL_TAC] THEN
    ASM_SIMP_TAC[RFA_LTQ_QACT] THEN REWRITE_TAC[RFA_LTINNER_LTC] THEN
    MATCH_MP_TAC RFA_LTC_RBASIS THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC RFA_QACTE_RIC THEN
    MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RFA_LTINNER_RADD; RFA_LTINNER_RCMUL; ETA_AX] THEN REAL_ARITH_TAC);;

let RFA_RMNORM2_DERIV = prove
 (`!(B8:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
    U a b (G:real->real^N->real^N^N) t y.
        (!U a b (G:real->real^N->real^N^N) t y u.
            lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
            ==> ((\s. lrm4 (G s) y u) has_real_derivative
                 ltlap 4 (G t) (lrm4 (G t)) y u +
                 B8 (G t) (lrm4 (G t)) (lrm4 (G t)) y u) (atreal t)) /\
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. ltnorm2 4 (G s) (lrm4 (G s)) y) has_real_derivative
             &2 * ltinner 4 (G t) (lrm4 (G t)) (ltlap 4 (G t) (lrm4 (G t))) y +
             ltinner 4 (G t) (lrm4 (G t))
               (\z u. &2 * B8 (G t) (lrm4 (G t)) (lrm4 (G t)) z u +
                      sum(1..4) (\l. &2 * rfa_qact l (G t)
                                  (ltcontr (G t) (ltperm (swap(2,3)) (lrm4 (G t))))
                                  (lrm4 (G t)) z u)) y) (atreal t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "evol") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  REWRITE_TAC[RFA_LTNORM2_LTC] THEN
  MP_TAC(ISPECL
   [`4`; `\s. matrix_inv((G:real->real^N->real^N^N) s y)`;
    `--(matrix_inv((G:real->real^N->real^N^N) t y) **
        (lambda i j. --(&2) * lricci (G t) y (basis i) (basis j)) **
        matrix_inv(G t y))`;
    `\s. lrm4 ((G:real->real^N->real^N^N) s) y`;
    `\ip. ltlap 4 ((G:real->real^N->real^N^N) t) (lrm4 (G t)) y (\m. basis(ip m)) +
          (B8:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
            (G t) (lrm4 (G t)) (lrm4 (G t)) y (\m. basis(ip m))`;
    `\s. lrm4 ((G:real->real^N->real^N^N) s) y`;
    `\ip. ltlap 4 ((G:real->real^N->real^N^N) t) (lrm4 (G t)) y (\m. basis(ip m)) +
          (B8:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
            (G t) (lrm4 (G t)) (lrm4 (G t)) y (\m. basis(ip m))`;
    `t:real`] RFA_LTC_DERIV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
      MATCH_MP_TAC LRG_VDERIV_MATRIX_ENTRY_REAL THEN BETA_TAC THEN
      MATCH_MP_TAC LRG_FLOW_DGINV THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN
      USE_THEN "evol" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net
                   ==> (f has_real_derivative y) net`) THEN
  MATCH_MP_TAC RFA_RMNORM2_ALG THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The evolution inequality for |Rm|^2 under a local Ricci flow:             *)
(*   d/dt |Rm|^2 <= Lap |Rm|^2 - 2 |D Rm|^2 + C |Rm|^3.                      *)
(* ========================================================================= *)

let RFA_LTENSOR_FIELD_EQ = prove
 (`!k U (f:real^N->(num->real^N)->real) g.
        ltensor_field k U f /\ (!y u. y IN U ==> g y u = f y u)
        ==> ltensor_field k U g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f") (LABEL_TAC "eq")) THEN
  REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g:real^N->(num->real^N)->real) y = f y` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "f" (MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
  ASM_REWRITE_TAC[]);;

let RFA_LBILIN_ON_FIELD = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E
        ==> !U G tf tg.
               metric_field U G /\ ltensor_field p U tf /\ ltensor_field q U tg /\
               (!u. smooth_map_on U (\y. lift(tf y u))) /\
               (!u. smooth_map_on U (\y. lift(tg y u)))
               ==> ltensor_field k U (E G tf tg)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree"))) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LTENSOR_FIELD_EQ THEN
  EXISTS_TAC `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
                   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
           RFA_LBILIN_FIELD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                               `tf:real^N->(num->real^N)->real`;
                               `tg:real^N->(num->real^N)->real`]) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "agree" MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let RFA_INNER_CUBIC_BOUND = prove
 (`!k U (G0:real^N->real^N^N) Rf Ef y C0.
        metric_field U G0 /\ ltensor_field k U Rf /\ ltensor_field k U Ef /\
        y IN U /\ &0 <= C0 /\
        ltnorm2 k G0 Ef y <= C0 * ltnorm2 k G0 Rf y * ltnorm2 k G0 Rf y
        ==> ltinner k G0 Rf Ef y <=
            sqrt C0 * sqrt(ltnorm2 k G0 Rf y) *
            (sqrt(ltnorm2 k G0 Rf y) * sqrt(ltnorm2 k G0 Rf y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= ltnorm2 k (G0:real^N->real^N^N) Rf y /\ &0 <= ltnorm2 k (G0:real^N->real^N^N) Ef y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[LTNORM2_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `Rf:real^N->(num->real^N)->real`; `Ef:real^N->(num->real^N)->real`;
                 `y:real^N`] RFA_LTINNER_ABS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sqrt(ltnorm2 k (G0:real^N->real^N^N) Ef y) <=
    sqrt C0 * sqrt(ltnorm2 k (G0:real^N->real^N^N) Rf y) * sqrt(ltnorm2 k (G0:real^N->real^N^N) Rf y)`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LE_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(ltnorm2 k (G0:real^N->real^N^N) Rf y)` MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `s = sqrt(ltnorm2 k (G0:real^N->real^N^N) Rf y)` THEN
  ABBREV_TAC `e = sqrt(ltnorm2 k (G0:real^N->real^N^N) Ef y)` THEN
  ABBREV_TAC `c = sqrt C0` THEN
  ABBREV_TAC `x = ltinner k (G0:real^N->real^N^N) Rf Ef y` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `s * e <= s * (c * s * s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s * (c * s * s) = c * s * (s * s)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  UNDISCH_TAC `abs x <= s * e` THEN REAL_ARITH_TAC);;

let RFA_LRM_NORM2_EVOLUTION_0 = prove
 (`?C. &0 <= C /\
       !U a b (G:real->real^N->real^N^N) t y.
          lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
          ==> ?d. ((\s. lrm_deriv_norm2 0 (G s) y) has_real_derivative d) (atreal t) /\
                  d <= llap (G t) (lrm_deriv_norm2 0 (G t)) y -
                       &2 * lrm_deriv_norm2 (0 + 1) (G t) y +
                       C * sqrt(lrm_deriv_norm2 0 (G t) y) *
                       sum(0..0) (\i. sqrt(lrm_deriv_norm2 i (G t) y) *
                                      sqrt(lrm_deriv_norm2 (0 - i) (G t) y))`,
  X_CHOOSE_THEN
   `B8:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "evol")) RFA_LRM4_EVOLUTION THEN
  FIRST_ASSUM(LABEL_TAC "op" o MATCH_MP RFA_RMNORM_EVOL_OP) THEN
  USE_THEN "op" (MP_TAC o MATCH_MP RFA_LBILIN_ON_NORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb"))) THEN
  EXISTS_TAC `sqrt C0` THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `a:real`; `b:real`;
                       `G:real->real^N->real^N^N`; `t:real`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUM_SING_NUMSEG; SUB_REFL; ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `lrm_deriv_norm2 1 ((G:real->real^N->real^N^N) t) y =
    ltnorm2 (4 + 1) (G t) (lnabla 4 (G t) (lrm4 (G t))) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[lrm_deriv_norm2; RFA_LNABLA_ITER_1]; ALL_TAC] THEN
  SUBGOAL_THEN `!(H:real^N->real^N^N). lrm_deriv_norm2 0 H = ltnorm2 4 H (lrm4 H)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B8:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                     (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
                 `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`] RFA_RMNORM2_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> EXISTS_TAC(rand(rator(concl th))) THEN
                       CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `lrm4 ((G:real->real^N->real^N^N) t)`; `y:real^N`] RFA_LLAP_LTNORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= z ==> &2 * a + x <= (&2 * a + &2 * n) - &2 * n + z`) THEN
  MATCH_MP_TAC RFA_INNER_CUBIC_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "op" (MP_TAC o MATCH_MP RFA_LBILIN_ON_FIELD) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                               `lrm4 ((G:real->real^N->real^N^N) t)`;
                               `lrm4 ((G:real->real^N->real^N^N) t)`]) THEN
    ASM_REWRITE_TAC[] THEN TRY(DISCH_THEN MATCH_ACCEPT_TAC);
    USE_THEN "nb" (MP_TAC o SPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                                   `lrm4 ((G:real->real^N->real^N^N) t)`;
                                   `lrm4 ((G:real->real^N->real^N^N) t)`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; BETA_TAC THEN DISCH_THEN MATCH_ACCEPT_TAC]]);;

