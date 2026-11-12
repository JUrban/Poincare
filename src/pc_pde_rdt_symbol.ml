(* ========================================================================= *)
(* Unit pc_pde_rdt_symbol: the local Ricci-DeTurck operator                  *)
(* pde_lrdt H G = -2 Ric(G) + L_W G with W = W(G,H).  PDE_LRDT_SYMBOL:       *)
(* pde_lrdt H G = tr_G Hess_H G + F(y, G(y), DG(y)) with F smooth (the       *)
(* second derivatives of G cancel); PDE_LRDT_PULLBACK: the operator is       *)
(* natural under diffeomorphisms.                                            *)
(* ========================================================================= *)

needs "src/pc_pde_iface.ml";;
needs "src/pc_rf_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Jet formulas and the cancellation of the second derivatives.  Jets at a   *)
(* point, as functions of indices:                                           *)
(*   g a b = G_ab, gi a b = (G^-1)_ab, d1 c a b = d_c G_ab,                  *)
(*   d2 c e a b = d_c d_e G_ab, hc m a b = Gamma_H(e_a,e_b)_m,               *)
(*   hdc c m a b = d_c Gamma_H(e_a,e_b)_m.                                   *)
(* ========================================================================= *)

let pde_jchr = new_definition
 `pde_jchr n (gi:num->num->real) (d1:num->num->num->real) m a b =
    sum(1..n) (\k. gi m k * inv(&2) * (d1 a k b + d1 b k a - d1 k a b))`;;

let pde_jdgi = new_definition
 `pde_jdgi n (gi:num->num->real) (d1:num->num->num->real) c i j =
    --(sum(1..n) (\p. sum(1..n) (\q. gi i p * d1 c p q * gi q j)))`;;

let pde_jdchr = new_definition
 `pde_jdchr n (gi:num->num->real) (d1:num->num->num->real)
            (d2:num->num->num->num->real) c m a b =
    sum(1..n) (\k. pde_jdgi n gi d1 c m k * inv(&2) * (d1 a k b + d1 b k a - d1 k a b) +
                   gi m k * inv(&2) * (d2 c a k b + d2 c b k a - d2 c k a b))`;;

let pde_jric = new_definition
 `pde_jric n (gi:num->num->real) (d1:num->num->num->real)
           (d2:num->num->num->num->real) a b =
    sum(1..n) (\c. pde_jdchr n gi d1 d2 c c a b - pde_jdchr n gi d1 d2 a c c b +
                   sum(1..n) (\p. pde_jchr n gi d1 p a b * pde_jchr n gi d1 c c p -
                                  pde_jchr n gi d1 p c b * pde_jchr n gi d1 c a p))`;;

let pde_jw = new_definition
 `pde_jw n (gi:num->num->real) (d1:num->num->num->real) (hc:num->num->num->real) m =
    sum(1..n) (\i. sum(1..n) (\j. gi i j * (pde_jchr n gi d1 m i j - hc m i j)))`;;

let pde_jdw = new_definition
 `pde_jdw n (gi:num->num->real) (d1:num->num->num->real) (d2:num->num->num->num->real)
          (hc:num->num->num->real) (hdc:num->num->num->num->real) c m =
    sum(1..n) (\i. sum(1..n) (\j.
       pde_jdgi n gi d1 c i j * (pde_jchr n gi d1 m i j - hc m i j) +
       gi i j * (pde_jdchr n gi d1 d2 c m i j - hdc c m i j)))`;;

let pde_jlw = new_definition
 `pde_jlw n (g:num->num->real) (gi:num->num->real) (d1:num->num->num->real)
          (d2:num->num->num->num->real) (hc:num->num->num->real)
          (hdc:num->num->num->num->real) a b =
    sum(1..n) (\m. pde_jw n gi d1 hc m * d1 m a b +
                   pde_jdw n gi d1 d2 hc hdc a m * g m b +
                   g a m * pde_jdw n gi d1 d2 hc hdc b m)`;;

(* The first covariant derivative (w.r.t. H) of G at (e_a,e_b), direction p, *)
(* and its derivative in the direction q.                                    *)

let pde_jsl = new_definition
 `pde_jsl n (g:num->num->real) (d1:num->num->num->real) (hc:num->num->num->real) a b p =
    d1 p a b - sum(1..n) (\m. hc m p a * g m b) - sum(1..n) (\m. g a m * hc m p b)`;;

let pde_jdsl = new_definition
 `pde_jdsl n (g:num->num->real) (d1:num->num->num->real) (d2:num->num->num->num->real)
           (hc:num->num->num->real) (hdc:num->num->num->num->real) a b p q =
    d2 q p a b - sum(1..n) (\m. hdc q m p a * g m b + hc m p a * d1 q m b) -
    sum(1..n) (\m. d1 q a m * hc m p b + g a m * hdc q m p b)`;;

let pde_jhess = new_definition
 `pde_jhess n (g:num->num->real) (d1:num->num->num->real) (d2:num->num->num->num->real)
            (hc:num->num->num->real) (hdc:num->num->num->num->real) a b p q =
    pde_jdsl n g d1 d2 hc hdc a b p q -
    (sum(1..n) (\m. hc m q a * pde_jsl n g d1 hc m b p) +
     sum(1..n) (\m. hc m q b * pde_jsl n g d1 hc a m p) +
     sum(1..n) (\m. hc m q p * pde_jsl n g d1 hc a b m))`;;

let pde_jtrhess = new_definition
 `pde_jtrhess n (g:num->num->real) (gi:num->num->real) (d1:num->num->num->real)
              (d2:num->num->num->num->real) (hc:num->num->num->real)
              (hdc:num->num->num->num->real) a b =
    sum(1..n) (\p. sum(1..n) (\q. gi p q * pde_jhess n g d1 d2 hc hdc a b p q))`;;

let pde_jdj = new_definition
 `pde_jdj n (g:num->num->real) (gi:num->num->real) (d1:num->num->num->real)
          (d2:num->num->num->num->real) (hc:num->num->num->real)
          (hdc:num->num->num->num->real) a b =
    --(&2) * pde_jric n gi d1 d2 a b + pde_jlw n g gi d1 d2 hc hdc a b -
    pde_jtrhess n g gi d1 d2 hc hdc a b`;;

(* The parts linear in the second derivatives. *)

let pde_ljchr = new_definition
 `pde_ljchr n (gi:num->num->real) (d2:num->num->num->num->real) c m a b =
    sum(1..n) (\k. gi m k * inv(&2) * (d2 c a k b + d2 c b k a - d2 c k a b))`;;

let pde_ljdw = new_definition
 `pde_ljdw n (gi:num->num->real) (d2:num->num->num->num->real) c m =
    sum(1..n) (\i. sum(1..n) (\j. gi i j * pde_ljchr n gi d2 c m i j))`;;

let PDE_JDCHR_SPLIT = prove
 (`!n gi d1 d2 c m a b.
     pde_jdchr n gi d1 d2 c m a b =
     pde_jdchr n gi d1 (\c e i j. &0) c m a b + pde_ljchr n gi d2 c m a b`,
  REWRITE_TAC[pde_jdchr; pde_ljchr; GSYM SUM_ADD_NUMSEG] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let PDE_JRIC_SPLIT = prove
 (`!n gi d1 d2 a b.
     pde_jric n gi d1 d2 a b =
     pde_jric n gi d1 (\c e i j. &0) a b +
     sum(1..n) (\c. pde_ljchr n gi d2 c c a b - pde_ljchr n gi d2 a c c b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jric] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [PDE_JDCHR_SPLIT] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let PDE_JDW_SPLIT = prove
 (`!n gi d1 d2 hc hdc c m.
     pde_jdw n gi d1 d2 hc hdc c m =
     pde_jdw n gi d1 (\c e i j. &0) hc hdc c m + pde_ljdw n gi d2 c m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jdw; pde_ljdw] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [PDE_JDCHR_SPLIT] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let PDE_JLW_SPLIT = prove
 (`!n g gi d1 d2 hc hdc a b.
     pde_jlw n g gi d1 d2 hc hdc a b =
     pde_jlw n g gi d1 (\c e i j. &0) hc hdc a b +
     sum(1..n) (\m. pde_ljdw n gi d2 a m * g m b + g a m * pde_ljdw n gi d2 b m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jlw] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [PDE_JDW_SPLIT] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let PDE_JTRHESS_SPLIT = prove
 (`!n g gi d1 d2 hc hdc a b.
     pde_jtrhess n g gi d1 d2 hc hdc a b =
     pde_jtrhess n g gi d1 (\c e i j. &0) hc hdc a b +
     sum(1..n) (\p. sum(1..n) (\q. gi p q * d2 q p a b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jtrhess; pde_jhess; pde_jdsl] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let PDE_JDJ_SPLIT = prove
 (`!n g gi d1 d2 hc hdc a b.
     pde_jdj n g gi d1 d2 hc hdc a b =
     pde_jdj n g gi d1 (\c e i j. &0) hc hdc a b +
     (--(&2) * sum(1..n) (\c. pde_ljchr n gi d2 c c a b - pde_ljchr n gi d2 a c c b) +
      sum(1..n) (\m. pde_ljdw n gi d2 a m * g m b + g a m * pde_ljdw n gi d2 b m) -
      sum(1..n) (\p. sum(1..n) (\q. gi p q * d2 q p a b)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jdj] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [PDE_JRIC_SPLIT; PDE_JLW_SPLIT;
                                                 PDE_JTRHESS_SPLIT] THEN
  REAL_ARITH_TAC);;

(* Contractions with the inverse metric. *)

let PDE_JSWAP3 = prove
 (`!n (FF:num->num->num->real).
     sum(1..n) (\m. sum(1..n) (\i. sum(1..n) (\j. FF m i j))) =
     sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\m. FF m i j)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let PDE_JCONTRACT_R = prove
 (`!n (g:num->num->real) gi (Y:num->real) b.
     (!k. 1 <= k /\ k <= n ==> sum(1..n) (\m. g m b * gi m k) = if k = b then &1 else &0) /\
     1 <= b /\ b <= n
     ==> sum(1..n) (\m. sum(1..n) (\k. gi m k * Y k) * g m b) = Y b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. if k = b then (Y:num->real) b else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..n) (\m. (g:num->num->real) m b * gi m k) * (Y:num->real) k` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO]];
    ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]]);;

let PDE_JCONTRACT_L = prove
 (`!n (g:num->num->real) gi (Y:num->real) a.
     (!k. 1 <= k /\ k <= n ==> sum(1..n) (\m. g a m * gi m k) = if k = a then &1 else &0) /\
     1 <= a /\ a <= n
     ==> sum(1..n) (\m. g a m * sum(1..n) (\k. gi m k * Y k)) = Y a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `\m (b:num). (g:num->num->real) a m`; `gi:num->num->real`;
                 `Y:num->real`; `a:num`] PDE_JCONTRACT_R) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The second-order part of L_W G, contracted with G G^-1 = I. *)

let PDE_JLDW_CONTRACT_R = prove
 (`!n (g:num->num->real) gi d2 a b.
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> g i j = g j i) /\
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n
            ==> sum(1..n) (\m. g i m * gi m j) = if j = i then &1 else &0) /\
     1 <= a /\ a <= n /\ 1 <= b /\ b <= n
     ==> sum(1..n) (\m. pde_ljdw n gi d2 a m * g m b) =
         sum(1..n) (\i. sum(1..n) (\j. gi i j *
           (inv(&2) * (d2 a i b j + d2 a j b i - d2 a b i j))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_ljdw; pde_ljchr; GSYM SUM_RMUL; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [PDE_JSWAP3] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:num`; `g:num->num->real`; `gi:num->num->real`;
                 `\k. (gi:num->num->real) i j *
                      (inv(&2) * ((d2:num->num->num->num->real) a i k j + d2 a j k i -
                                  d2 a k i j))`; `b:num`] PDE_JCONTRACT_R) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..n) (\m. (g:num->num->real) b m * (gi:num->num->real) m k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let PDE_JLDW_CONTRACT_L = prove
 (`!n (g:num->num->real) gi d2 a b.
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n
            ==> sum(1..n) (\m. g i m * gi m j) = if j = i then &1 else &0) /\
     1 <= a /\ a <= n /\ 1 <= b /\ b <= n
     ==> sum(1..n) (\m. g a m * pde_ljdw n gi d2 b m) =
         sum(1..n) (\i. sum(1..n) (\j. gi i j *
           (inv(&2) * (d2 b i a j + d2 b j a i - d2 b a i j))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_ljdw; pde_ljchr; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [PDE_JSWAP3] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:num`; `g:num->num->real`; `gi:num->num->real`;
                 `\k. (gi:num->num->real) i j *
                      (inv(&2) * ((d2:num->num->num->num->real) b i k j + d2 b j k i -
                                  d2 b k i j))`; `a:num`] PDE_JCONTRACT_L) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* A double contraction of a symmetric matrix with an antisymmetric array. *)

let PDE_JSYM_ZERO = prove
 (`!n (gi:num->num->real) (Z:num->num->real).
     (!c k. 1 <= c /\ c <= n /\ 1 <= k /\ k <= n ==> gi c k = gi k c) /\
     (!c k. 1 <= c /\ c <= n /\ 1 <= k /\ k <= n ==> Z c k + Z k c = &0)
     ==> sum(1..n) (\c. sum(1..n) (\k. gi c k * Z c k)) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(1..n) (\c. sum(1..n) (\k. (gi:num->num->real) c k * Z c k)) =
    sum(1..n) (\c. sum(1..n) (\k. gi c k * (Z:num->num->real) k c))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\c. sum(1..n) (\k. (gi:num->num->real) c k * Z c k)) +
    sum(1..n) (\c. sum(1..n) (\k. gi c k * (Z:num->num->real) k c)) = &0`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_SIMP_TAC[REAL_MUL_RZERO];
    ASM_REAL_ARITH_TAC]);;

(* The second derivatives cancel. *)

let PDE_JLIN_ZERO = prove
 (`!n (g:num->num->real) gi (d2:num->num->num->num->real) a b.
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> gi i j = gi j i) /\
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> g i j = g j i) /\
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n
            ==> sum(1..n) (\m. g i m * gi m j) = if j = i then &1 else &0) /\
     (!c e i j. 1 <= c /\ c <= n /\ 1 <= e /\ e <= n /\ 1 <= i /\ i <= n /\
                1 <= j /\ j <= n
                ==> d2 c e i j = d2 e c i j /\ d2 c e i j = d2 c e j i) /\
     1 <= a /\ a <= n /\ 1 <= b /\ b <= n
     ==> --(&2) * sum(1..n) (\c. pde_ljchr n gi d2 c c a b - pde_ljchr n gi d2 a c c b) +
         sum(1..n) (\m. pde_ljdw n gi d2 a m * g m b + g a m * pde_ljdw n gi d2 b m) -
         sum(1..n) (\p. sum(1..n) (\q. gi p q * d2 q p a b)) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  MP_TAC(ISPECL [`n:num`; `g:num->num->real`; `gi:num->num->real`;
                 `d2:num->num->num->num->real`; `a:num`; `b:num`] PDE_JLDW_CONTRACT_R) THEN
  MP_TAC(ISPECL [`n:num`; `g:num->num->real`; `gi:num->num->real`;
                 `d2:num->num->num->num->real`; `a:num`; `b:num`] PDE_JLDW_CONTRACT_L) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[pde_ljchr] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..n) (\c. sum(1..n) (\k. (gi:num->num->real) c k *
      (--(&2) * (inv(&2) * (d2 c a k b + d2 c b k a - d2 c k a b) -
                 inv(&2) * (d2 a c k b + d2 a b k c - d2 a k c b)) +
       (inv(&2) * (d2 a c b k + d2 a k b c - d2 a b c k) +
        inv(&2) * (d2 b c a k + d2 b k a c - d2 b a c k)) -
       (d2:num->num->num->num->real) k c a b)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`n:num`; `gi:num->num->real`;
    `\c k. --(&2) * (inv(&2) * ((d2:num->num->num->num->real) c a k b + d2 c b k a -
                                d2 c k a b) -
                     inv(&2) * (d2 a c k b + d2 a b k c - d2 a k c b)) +
           (inv(&2) * (d2 a c b k + d2 a k b c - d2 a b c k) +
            inv(&2) * (d2 b c a k + d2 b k a c - d2 b a c k)) -
           d2 k c a b`] PDE_JSYM_ZERO)) THEN
  ASM_SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`c:num`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(d2:num->num->num->num->real) a c k b = d2 c a k b /\ d2 a c b k = d2 c a k b /\
    d2 b c a k = d2 c b k a /\ d2 k c a b = d2 c k a b /\
    d2 a b c k = d2 a b k c /\ d2 b a c k = d2 a b k c /\ d2 b a k c = d2 a b k c /\
    d2 a k b c = d2 a k c b /\ d2 k a c b = d2 a k c b /\ d2 k b c a = d2 b k a c`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let PDE_JDJ_D2_FREE = prove
 (`!n (g:num->num->real) gi d1 (d2:num->num->num->num->real) hc hdc a b.
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> gi i j = gi j i) /\
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> g i j = g j i) /\
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n
            ==> sum(1..n) (\m. g i m * gi m j) = if j = i then &1 else &0) /\
     (!c e i j. 1 <= c /\ c <= n /\ 1 <= e /\ e <= n /\ 1 <= i /\ i <= n /\
                1 <= j /\ j <= n
                ==> d2 c e i j = d2 e c i j /\ d2 c e i j = d2 c e j i) /\
     1 <= a /\ a <= n /\ 1 <= b /\ b <= n
     ==> pde_jdj n g gi d1 d2 hc hdc a b = pde_jdj n g gi d1 (\c e i j. &0) hc hdc a b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [PDE_JDJ_SPLIT] THEN
  MP_TAC(ISPECL [`n:num`; `g:num->num->real`; `gi:num->num->real`;
                 `d2:num->num->num->num->real`; `a:num`; `b:num`] PDE_JLIN_ZERO) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The jets of a matrix field at a point; the Christoffel symbols, their     *)
(* derivatives, the derivatives of the inverse matrix and the Ricci form of  *)
(* a metric field as jet formulas (via the differential polynomials of       *)
(* pc_rf_glue).  A small calculus of partial derivatives of real functions.  *)
(* ========================================================================= *)

let pde_jg = new_definition
 `pde_jg (G:real^N->real^N^N) (y:real^N) = \a b. (G y)$a$b`;;

let pde_jgi = new_definition
 `pde_jgi (G:real^N->real^N^N) (y:real^N) = \a b. matrix_inv(G y)$a$b`;;

let pde_jd1 = new_definition
 `pde_jd1 (G:real^N->real^N^N) (y:real^N) = \c a b. (mderiv G y (basis c))$a$b`;;

let pde_jd2 = new_definition
 `pde_jd2 (G:real^N->real^N^N) (y:real^N) =
    \c e a b. ((matrify:real^(N,N)finite_prod->real^N^N)
                 (iterated_partial [c; e] ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                   y))$a$b`;;

let pde_jhc = new_definition
 `pde_jhc (H:real^N->real^N^N) (y:real^N) =
    \m a b. (christoffel H y (basis a) (basis b))$m`;;

let pde_jhdc = new_definition
 `pde_jhdc (H:real^N->real^N^N) (y:real^N) =
    \c m a b. (frechet_derivative (\z. christoffel H z (basis a) (basis b)) (at y)
                                  (basis c))$m`;;

(* Evaluations of the differential polynomials as jet formulas. *)

let JP_DX_SUM = prove
 (`!n c m (f:num->pde_jpoly). jp_dx n c (jp_sum m f) = jp_sum m (\p. jp_dx n c (f p))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[jp_sum; jp_dx]);;

let PDE_MDERIV_ENTRY_ITERATED = prove
 (`!(G:real^N->real^N^N) y a p q.
     ((matrify:real^(N,N)finite_prod->real^N^N)
        (iterated_partial [a] ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y))$p$q =
     mderiv G y (basis a) $p$q`,
  REWRITE_TAC[PDE_MDERIV_BASIS_ENTRY; jp_eval]);;

let JP_EVAL_CHR_JET = prove
 (`!(G:real^N->real^N^N) y m a b.
     jp_eval (jp_chr (dimindex(:N)) m a b) G y =
     pde_jchr (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) m a b`,
  REWRITE_TAC[jp_chr; jp_neg; JP_EVAL_SUM; jp_eval; PDE_MDERIV_ENTRY_ITERATED] THEN
  REWRITE_TAC[pde_jchr; pde_jgi; pde_jd1] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let JP_EVAL_DINV_JET = prove
 (`!(G:real^N->real^N^N) y c i j.
     jp_eval (jp_dx (dimindex(:N)) c (JPinv i j)) G y =
     pde_jdgi (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) c i j`,
  REWRITE_TAC[jp_dx; JP_EVAL_SUM; jp_eval; PDE_MDERIV_ENTRY_ITERATED] THEN
  REWRITE_TAC[pde_jdgi; pde_jgi; pde_jd1; REAL_MUL_LNEG; REAL_MUL_LID]);;

let JP_EVAL_DX_CLAUSES = prove
 (`(!n c r (G:real^N->real^N^N) y. jp_eval (jp_dx n c (JPconst r)) G y = &0) /\
   (!n c l i j (G:real^N->real^N^N) y.
      jp_eval (jp_dx n c (JPvar l i j)) G y = jp_eval (JPvar (CONS c l) i j) G y) /\
   (!n c e1 e2 (G:real^N->real^N^N) y.
      jp_eval (jp_dx n c (JPadd e1 e2)) G y =
      jp_eval (jp_dx n c e1) G y + jp_eval (jp_dx n c e2) G y) /\
   (!n c e1 e2 (G:real^N->real^N^N) y.
      jp_eval (jp_dx n c (JPmul e1 e2)) G y =
      jp_eval (jp_dx n c e1) G y * jp_eval e2 G y +
      jp_eval e1 G y * jp_eval (jp_dx n c e2) G y)`,
  REWRITE_TAC[jp_dx; jp_eval]);;

let JP_EVAL_DCHR_JET = prove
 (`!(G:real^N->real^N^N) y c m a b.
     jp_eval (jp_dx (dimindex(:N)) c (jp_chr (dimindex(:N)) m a b)) G y =
     pde_jdchr (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y) c m a b`,
  REWRITE_TAC[jp_chr; jp_neg; JP_DX_SUM; JP_EVAL_SUM; JP_EVAL_DX_CLAUSES;
              JP_EVAL_DINV_JET] THEN
  REWRITE_TAC[jp_eval; PDE_MDERIV_ENTRY_ITERATED] THEN
  REWRITE_TAC[pde_jdchr; pde_jgi; pde_jd1; pde_jd2] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The Christoffel symbols, their derivatives and the Ricci form. *)

let PDE_CHR_JET = prove
 (`!(G:real^N->real^N^N) y m a b.
     1 <= m /\ m <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
     1 <= b /\ b <= dimindex(:N)
     ==> christoffel G y (basis a) (basis b) $m =
         pde_jchr (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) m a b`,
  SIMP_TAC[JP_CHR; JP_EVAL_CHR_JET]);;

let PDE_DCHR_JET = prove
 (`!U (G:real^N->real^N^N) y m a b c.
     metric_field U G /\ y IN U /\
     1 <= m /\ m <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
     1 <= b /\ b <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
     ==> frechet_derivative (\z. christoffel G z (basis a) (basis b)) (at y) (basis c)$m =
         pde_jdchr (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y) c m a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM JP_EVAL_DCHR_JET] THEN
  MATCH_MP_TAC JP_DCHR THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let PDE_RIC_JET = prove
 (`!U (G:real^N->real^N^N) y a b.
     metric_field U G /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> lricci G y (basis a) (basis b) =
         pde_jric (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y) a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:num`; `b:num`]
                JP_RIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[jp_ric; jp_neg; JP_EVAL_SUM; jp_eval; JP_EVAL_DCHR_JET; JP_EVAL_CHR_JET] THEN
  REWRITE_TAC[pde_jric; SUM_SUB_NUMSEG] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; GSYM real_sub]);;

(* Partial derivatives of the jets themselves. *)

let PDE_JG_PARTIAL = prove
 (`!U (G:real^N->real^N^N) y c a b.
     metric_field U G /\ y IN U /\ 1 <= c /\ c <= dimindex(:N)
     ==> partial_derivative c (\z. lift((G z)$a$b)) y = lift(pde_jd1 G y c a b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] JP_METRIC_FIELD_GOOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `JPvar [] a b`) THEN
  REWRITE_TAC[jp_good] THEN DISCH_THEN(MP_TAC o SPECL [`c:num`; `y:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[jp_dx; jp_eval; iterated_partial; o_THM; MATRIFY_VECTORIZE;
                  PDE_MDERIV_ENTRY_ITERATED; pde_jd1] THEN
  REWRITE_TAC[ETA_AX]);;

let PDE_JD1_PARTIAL = prove
 (`!U (G:real^N->real^N^N) y c e a b.
     metric_field U G /\ y IN U /\ 1 <= c /\ c <= dimindex(:N)
     ==> partial_derivative c (\z. lift((mderiv G z (basis e))$a$b)) y =
         lift(pde_jd2 G y c e a b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] JP_METRIC_FIELD_GOOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `JPvar [e] a b`) THEN
  REWRITE_TAC[jp_good] THEN DISCH_THEN(MP_TAC o SPECL [`c:num`; `y:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[jp_dx; GSYM PDE_MDERIV_BASIS_ENTRY] THEN
  REWRITE_TAC[jp_eval; pde_jd2; ETA_AX]);;

let PDE_JGI_PARTIAL = prove
 (`!U (G:real^N->real^N^N) y c i j.
     metric_field U G /\ y IN U /\ 1 <= c /\ c <= dimindex(:N)
     ==> partial_derivative c (\z. lift(matrix_inv(G z)$i$j)) y =
         lift(pde_jdgi (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) c i j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] JP_METRIC_FIELD_GOOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `JPinv i j`) THEN
  REWRITE_TAC[jp_good] THEN DISCH_THEN(MP_TAC o SPECL [`c:num`; `y:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[JP_EVAL_DINV_JET] THEN REWRITE_TAC[jp_eval; ETA_AX]);;

let PDE_CHR_PARTIAL = prove
 (`!U (G:real^N->real^N^N) y m a b c.
     metric_field U G /\ y IN U /\
     1 <= m /\ m <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
     1 <= b /\ b <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
     ==> partial_derivative c (\z. lift(christoffel G z (basis a) (basis b)$m)) y =
         lift(pde_jdchr (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y) c m a b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num`; `m:num`; `\z. christoffel (G:real^N->real^N^N) z (basis a) (basis b)`;
                 `y:real^N`] PARTIAL_DERIVATIVE_COMPONENT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MATCH_MP_TAC PDE_DCHR_JET THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let PDE_HCHR_PARTIAL = prove
 (`!U (H:real^N->real^N^N) y m a b c.
     metric_field U H /\ y IN U
     ==> partial_derivative c (\z. lift(christoffel H z (basis a) (basis b)$m)) y =
         lift(pde_jhdc H y c m a b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num`; `m:num`; `\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b)`;
                 `y:real^N`] PARTIAL_DERIVATIVE_COMPONENT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pde_jhdc; partial_derivative]);;

(* A small calculus for partial derivatives of real functions. *)

let PDE_PD_LIFT_ADD = prove
 (`!(f:real^N->real) g c y.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> partial_derivative c (\z. lift(f z + g z)) y =
         partial_derivative c (\z. lift(f z)) y + partial_derivative c (\z. lift(g z)) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
  MP_TAC(ISPECL [`c:num`; `\z. lift((f:real^N->real) z)`; `\z. lift((g:real^N->real) z)`;
                 `y:real^N`] PARTIAL_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[]);;

let PDE_PD_LIFT_SUB = prove
 (`!(f:real^N->real) g c y.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> partial_derivative c (\z. lift(f z - g z)) y =
         partial_derivative c (\z. lift(f z)) y - partial_derivative c (\z. lift(g z)) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  MP_TAC(ISPECL [`c:num`; `\z. lift((f:real^N->real) z)`; `\z. lift((g:real^N->real) z)`;
                 `y:real^N`] PARTIAL_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[]);;

let PDE_PD_LIFT_MUL = prove
 (`!(f:real^N->real) g c y.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> partial_derivative c (\z. lift(f z * g z)) y =
         f y % partial_derivative c (\z. lift(g z)) y +
         g y % partial_derivative c (\z. lift(f z)) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((f:real^N->real) z * g z)) =
                (\z. drop(lift(f z)) % lift(g z))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; LIFT_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num`; `\z. lift((f:real^N->real) z)`; `\z. lift((g:real^N->real) z)`;
                 `y:real^N`] PARTIAL_DERIVATIVE_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let PDE_PD_LIFT_SUM = prove
 (`!(f:num->real^N->real) s c y.
     FINITE s /\ (!i. i IN s ==> (\z. lift(f i z)) differentiable (at y))
     ==> partial_derivative c (\z. lift(sum s (\i. f i z))) y =
         vsum s (\i. partial_derivative c (\z. lift(f i z)) y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`c:num`; `\i z. lift((f:num->real^N->real) i z)`; `s:num->bool`;
                 `y:real^N`] PARTIAL_DERIVATIVE_VSUM) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Smoothness of the entries, real partial derivatives (drop form), the      *)
(* DeTurck field W = W(G,H) and the Lie derivative L_W G as jet formulas.    *)
(* ========================================================================= *)

(* Smoothness of real combinations and of the entries. *)

let PDE_SMOOTH_LIFT_ADD_REAL = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x + g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift((f:real^M->real) x)`;
                 `\x. lift((g:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let PDE_SMOOTH_LIFT_SUB_REAL = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x - g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift((f:real^M->real) x)`;
                 `\x. lift((g:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let PDE_SMOOTH_LIFT_NEG_REAL = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) ==> smooth_map_on s (\x. lift(--(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift((f:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_NEG) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let PDE_SMOOTH_GINV_ENTRY = prove
 (`!U (G:real^N->real^N^N) i j.
     metric_field U G ==> smooth_map_on U (\z. lift(matrix_inv(G z)$i$j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `(\z. lift(matrix_inv((G:real^N->real^N^N) z)$i$j)) =
                (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
                ((vectorize:real^N^N->real^(N,N)finite_prod) o (\z. matrix_inv(G z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]);;

let PDE_SMOOTH_G_ENTRY = prove
 (`!U (G:real^N->real^N^N) i j.
     metric_field U G ==> smooth_map_on U (\z. lift((G z)$i$j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `(\z. lift(((G:real^N->real^N^N) z)$i$j)) =
                (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
                ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY]);;

let PDE_SMOOTH_MDERIV_ENTRY = prove
 (`!U (G:real^N->real^N^N) w i j.
     metric_field U G ==> smooth_map_on U (\z. lift((mderiv G z w)$i$j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `(\z. lift((mderiv (G:real^N->real^N^N) z w)$i$j)) =
                (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
                ((vectorize:real^N^N->real^(N,N)finite_prod) o (\z. mderiv G z w))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  MATCH_MP_TAC LRG_SMOOTH_MDERIV THEN ASM_REWRITE_TAC[]);;

let PDE_SMOOTH_CHR_ENTRY = prove
 (`!U (G:real^N->real^N^N) u v m.
     metric_field U G ==> smooth_map_on U (\z. lift(christoffel G z u v$m))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `(\z. lift(christoffel (G:real^N->real^N^N) z u v$m)) =
                (\x:real^N. lift(x$m)) o (\z. christoffel G z u v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
  MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]);;

(* A recursive tactic for smoothness of real expressions built from sums,   *)
(* products, differences and atoms.                                          *)

let rec PDE_SMOOTH_REAL_TAC atoms g =
  (FIRST
    [MATCH_ACCEPT_TAC SMOOTH_MAP_ON_CONST;
     ASM_REWRITE_TAC[] THEN NO_TAC;
     FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) atoms);
     MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
     ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
     PDE_SMOOTH_REAL_TAC atoms;
     MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN PDE_SMOOTH_REAL_TAC atoms;
     MATCH_MP_TAC PDE_SMOOTH_LIFT_ADD_REAL THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN PDE_SMOOTH_REAL_TAC atoms;
     MATCH_MP_TAC PDE_SMOOTH_LIFT_SUB_REAL THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN PDE_SMOOTH_REAL_TAC atoms;
     MATCH_MP_TAC PDE_SMOOTH_LIFT_NEG_REAL THEN ASM_REWRITE_TAC[] THEN
     PDE_SMOOTH_REAL_TAC atoms]) g;;

(* Real partial derivatives in drop form. *)

let PDE_RD_ADD = prove
 (`!(f:real^N->real) g c y.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> drop(partial_derivative c (\z. lift(f z + g z)) y) =
         drop(partial_derivative c (\z. lift(f z)) y) +
         drop(partial_derivative c (\z. lift(g z)) y)`,
  SIMP_TAC[PDE_PD_LIFT_ADD; DROP_ADD]);;

let PDE_RD_SUB = prove
 (`!(f:real^N->real) g c y.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> drop(partial_derivative c (\z. lift(f z - g z)) y) =
         drop(partial_derivative c (\z. lift(f z)) y) -
         drop(partial_derivative c (\z. lift(g z)) y)`,
  SIMP_TAC[PDE_PD_LIFT_SUB; DROP_SUB]);;

let PDE_RD_MUL = prove
 (`!(f:real^N->real) g c y.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> drop(partial_derivative c (\z. lift(f z * g z)) y) =
         f y * drop(partial_derivative c (\z. lift(g z)) y) +
         g y * drop(partial_derivative c (\z. lift(f z)) y)`,
  SIMP_TAC[PDE_PD_LIFT_MUL; DROP_ADD; DROP_CMUL]);;

let PDE_RD_SUM = prove
 (`!(f:num->real^N->real) s c y.
     FINITE s /\ (!i. i IN s ==> (\z. lift(f i z)) differentiable (at y))
     ==> drop(partial_derivative c (\z. lift(sum s (\i. f i z))) y) =
         sum s (\i. drop(partial_derivative c (\z. lift(f i z)) y))`,
  SIMP_TAC[PDE_PD_LIFT_SUM; DROP_VSUM; o_DEF]);;

(* The DeTurck field. *)

let PDE_LDETURCK_COMPONENT = prove
 (`!(H:real^N->real^N^N) G z m.
     pde_ldeturck H G z $ m =
     sum(1..dimindex(:N))
       (\i. sum(1..dimindex(:N))
              (\j. matrix_inv(G z)$i$j *
                   (christoffel G z (basis i) (basis j)$m -
                    christoffel H z (basis i) (basis j)$m)))`,
  REWRITE_TAC[pde_ldeturck; VSUM_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT]);;

let PDE_LDETURCK_JET = prove
 (`!(H:real^N->real^N^N) G z m.
     1 <= m /\ m <= dimindex(:N)
     ==> pde_ldeturck H G z $ m =
         pde_jw (dimindex(:N)) (pde_jgi G z) (pde_jd1 G z) (pde_jhc H z) m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_LDETURCK_COMPONENT; pde_jw] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[PDE_CHR_JET; pde_jhc] THEN REWRITE_TAC[pde_jgi]);;

let PDE_LDETURCK_SMOOTH = prove
 (`!U (H:real^N->real^N^N) G.
     metric_field U G /\ metric_field U H ==> smooth_map_on U (pde_ldeturck H G)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `pde_ldeturck (H:real^N->real^N^N) G =
    (\z. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. drop(lift(matrix_inv(G z)$i$j)) %
                       (christoffel G z (basis i) (basis j) -
                        christoffel H z (basis i) (basis j)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pde_ldeturck; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_SMOOTH_GINV_ENTRY THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

(* Derivative of a double sum of products with differences. *)

let PDE_RD_DSUM = prove
 (`!U (a:num->num->real^N->real) b c y k n.
     open U /\ y IN U /\
     (!i j. smooth_map_on U (\z. lift(a i j z))) /\
     (!i j. smooth_map_on U (\z. lift(b i j z))) /\
     (!i j. smooth_map_on U (\z. lift(c i j z)))
     ==> drop(partial_derivative k
                (\z. lift(sum(1..n) (\i. sum(1..n) (\j. a i j z * (b i j z - c i j z))))) y) =
         sum(1..n) (\i. sum(1..n) (\j.
           drop(partial_derivative k (\z. lift(a i j z)) y) * (b i j y - c i j y) +
           a i j y * (drop(partial_derivative k (\z. lift(b i j z)) y) -
                      drop(partial_derivative k (\z. lift(c i j z)) y))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:real^N->real. smooth_map_on U (\z. lift(f z)) ==> (\z. lift(f z)) differentiable (at y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i z. sum(1..n) (\j. (a:num->num->real^N->real) i j z *
                                         (b i j z - c i j z))`;
                 `1..n`; `k:num`; `y:real^N`] PDE_RD_SUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    PDE_SMOOTH_REAL_TAC [];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\j z. (a:num->num->real^N->real) i j z * (b i j z - c i j z)`;
                 `1..n`; `k:num`; `y:real^N`] PDE_RD_SUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    PDE_SMOOTH_REAL_TAC [];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(a:num->num->real^N->real) i j`;
                 `\z. (b:num->num->real^N->real) i j z - c i j z`; `k:num`; `y:real^N`]
                PDE_RD_MUL) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN PDE_SMOOTH_REAL_TAC [];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(b:num->num->real^N->real) i j`; `(c:num->num->real^N->real) i j`;
                 `k:num`; `y:real^N`] PDE_RD_SUB) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

let PDE_LDETURCK_PARTIAL = prove
 (`!U (H:real^N->real^N^N) G y c m.
     metric_field U G /\ metric_field U H /\ y IN U /\
     1 <= c /\ c <= dimindex(:N) /\ 1 <= m /\ m <= dimindex(:N)
     ==> drop(partial_derivative c (\z. lift(pde_ldeturck H G z $ m)) y) =
         pde_jdw (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y)
                 (pde_jhc H y) (pde_jhdc H y) c m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  REWRITE_TAC[PDE_LDETURCK_COMPONENT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\i j z. matrix_inv((G:real^N->real^N^N) z)$i$j`;
                 `\i j z. christoffel (G:real^N->real^N^N) z (basis i) (basis j)$m`;
                 `\i j z. christoffel (H:real^N->real^N^N) z (basis i) (basis j)$m`;
                 `y:real^N`; `c:num`; `dimindex(:N)`] PDE_RD_DSUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[PDE_SMOOTH_GINV_ENTRY; PDE_SMOOTH_CHR_ENTRY]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pde_jdw] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `c:num`; `i:num`;
                 `j:num`] PDE_JGI_PARTIAL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `m:num`; `i:num`;
                 `j:num`; `c:num`] PDE_CHR_PARTIAL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`; `m:num`; `i:num`;
                 `j:num`; `c:num`] PDE_HCHR_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[PDE_CHR_JET; LIFT_DROP; pde_jhc] THEN REWRITE_TAC[pde_jgi] THEN
  REAL_ARITH_TAC);;

(* The Lie derivative along W. *)

let PDE_MDERIV_EXPAND = prove
 (`!(G:real^N->real^N^N) y w a b.
     (vectorize o G) differentiable (at y)
     ==> (mderiv G y w)$a$b =
         sum(1..dimindex(:N)) (\m. w$m * (mderiv G y (basis m))$a$b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `linear (\x:real^N. lift((mderiv (G:real^N->real^N^N) y x)$a$b))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mderiv] THEN
    SUBGOAL_THEN
     `(\x. lift(((matrify:real^(N,N)finite_prod->real^N^N)
                 (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                      (G:real^N->real^N^N)) (at y) x))$a$b)) =
      (\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$a$b)) o
      frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G) (at y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE; LRG_LINEAR_MATRIFY_ENTRY];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `drop((\x:real^N. lift((mderiv (G:real^N->real^N^N) y x)$a$b))
                   (vsum(1..dimindex(:N)) (\m. (w:real^N)$m % basis m)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[BASIS_EXPANSION; LIFT_DROP]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_VSUM_MUL
                          (CONJ th (SPECL [`1`; `dimindex(:N)`] FINITE_NUMSEG))]) THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL; LIFT_DROP]);;

let PDE_LLIE_JET = prove
 (`!U (H:real^N->real^N^N) G y a b.
     metric_field U G /\ metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> llie (pde_ldeturck H G) G y $a$b =
         pde_jlw (dimindex(:N)) (pde_jg G y) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y)
                 (pde_jhc H y) (pde_jhdc H y) a b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `(pde_ldeturck (H:real^N->real^N^N) G) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[PDE_LDETURCK_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c m. 1 <= c /\ c <= dimindex(:N) /\ 1 <= m /\ m <= dimindex(:N)
          ==> matrix(frechet_derivative (pde_ldeturck (H:real^N->real^N^N) G) (at y))$m$c =
              pde_jdw (dimindex(:N)) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y)
                      (pde_jhc H y) (pde_jhdc H y) c m`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix; LAMBDA_BETA] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                   `c:num`; `m:num`] PDE_LDETURCK_PARTIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`c:num`; `m:num`; `pde_ldeturck (H:real^N->real^N^N) G`; `y:real^N`]
                  PARTIAL_DERIVATIVE_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_DROP; partial_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[llie; MATRIX_ADD_COMPONENT] THEN
  ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; TRANSP_COMPONENT] THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)) differentiable (at y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `y:real^N`; `pde_ldeturck (H:real^N->real^N^N) G y`;
                 `a:num`; `b:num`] PDE_MDERIV_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pde_jlw; SUM_ADD_NUMSEG] THEN
  BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PDE_LDETURCK_JET] THEN REWRITE_TAC[pde_jg; pde_jd1] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* tr_G Hess_H G as a jet formula.  The first covariant derivative           *)
(* (w.r.t. H) of the metric tensor of G at basis vectors, its derivative,    *)
(* the slot expansion, and the trace.                                        *)
(* ========================================================================= *)

let PDE_LNABLA_ITER_2 = prove
 (`!k (G:real^N->real^N^N) tf. lnabla_iter k 2 G tf = lnabla (k + 1) G (lnabla k G tf)`,
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; lnabla_iter; ADD_CLAUSES]);;

let PDE_LNABLA2_BASIS = prove
 (`!U (G:real^N->real^N^N) H z (u:num->real^N) a b p.
     metric_field U G /\ metric_field U H /\ z IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= p /\ p <= dimindex(:N) /\
     u 1 = basis a /\ u 2 = basis b /\ u 3 = basis p
     ==> lnabla 2 H (lmetric2 G) z u =
         pde_jsl (dimindex(:N)) (pde_jg G z) (pde_jd1 G z) (pde_jhc H z) a b p`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LRG_LNABLA_EQ; lmetric2; SUM_2; ARITH_RULE `2 + 1 = 3`] THEN
  REWRITE_TAC[ARITH_RULE `~(2 = 1) /\ ~(1 = 2)`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))
                differentiable (at z)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `z:real^N`; `basis a:real^N`; `basis b:real^N`]
                LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN
   `christoffel (H:real^N->real^N^N) z (basis p) (basis a) dot
      ((G:real^N->real^N^N) z ** basis b) =
    sum(1..dimindex(:N)) (\m. pde_jhc H z m p a * pde_jg G z m b) /\
    basis a dot (G z ** christoffel H z (basis p) (basis b)) =
    sum(1..dimindex(:N)) (\m. pde_jg G z a m * pde_jhc H z m p b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[dot; pde_jhc; pde_jg] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DOT_BASIS];
      ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[dot; pde_jhc; pde_jg]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_jsl] THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[pde_jd1] THEN REAL_ARITH_TAC);;

let PDE_LNABLA2_FIELD = prove
 (`!U (G:real^N->real^N^N) H.
     metric_field U G /\ metric_field U H
     ==> ltensor_field 3 U (lnabla 2 H (lmetric2 G)) /\
         (!u. smooth_map_on U (\y. lift(lnabla 2 H (lmetric2 G) y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `H:real^N->real^N^N`; `lmetric2 (G:real^N->real^N^N)`]
                LNABLA_TENSOR_FIELD) THEN
  ASM_SIMP_TAC[LRG_LMETRIC2_FIELD; ARITH_RULE `2 + 1 = 3`]);;

(* The default simplifier discharges conditions only to depth 3; the chains *)
(* differentiable <- smooth <- (sum, product, entry) need more.            *)

let PDE_DEEP_SIMP_TAC thl =
  CONV_TAC(GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 12 thl);;

let PDE_ASM_DEEP_SIMP_TAC = ASM PDE_DEEP_SIMP_TAC;;

(* The derivative of the first covariant derivative. *)

let PDE_JSL_PARTIAL = prove
 (`!U (G:real^N->real^N^N) H y a b p q.
     metric_field U G /\ metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> drop(partial_derivative q
                (\x. lift(pde_jsl (dimindex(:N)) (pde_jg G x) (pde_jd1 G x) (pde_jhc H x)
                                  a b p)) y) =
         pde_jdsl (dimindex(:N)) (pde_jg G y) (pde_jd1 G y) (pde_jd2 G y)
                  (pde_jhc H y) (pde_jhdc H y) a b p q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `!f:real^N->real^1. smooth_map_on U f ==> f differentiable (at y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] PDE_JD1_PARTIAL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] PDE_JG_PARTIAL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`] PDE_HCHR_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[pde_jsl; pde_jg; pde_jd1; pde_jhc] THEN
  PDE_ASM_DEEP_SIMP_TAC[PDE_RD_SUB; PDE_RD_MUL; PDE_RD_SUM; FINITE_NUMSEG; IN_NUMSEG; LIFT_DROP;
               LRG_SMOOTH_LIFT_MUL_REAL; LRG_SMOOTH_LIFT_SUM_REAL;
               PDE_SMOOTH_LIFT_SUB_REAL; PDE_SMOOTH_MDERIV_ENTRY; PDE_SMOOTH_G_ENTRY;
               PDE_SMOOTH_CHR_ENTRY] THEN
  REWRITE_TAC[pde_jdsl; pde_jg; pde_jd1; pde_jhc] THEN
  BINOP_TAC THENL [BINOP_TAC THENL [REWRITE_TAC[]; ALL_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The second covariant derivative at basis vectors. *)

let PDE_HESS4_JET = prove
 (`!U (G:real^N->real^N^N) H y a b p q.
     metric_field U G /\ metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> lnabla_iter 2 2 H (lmetric2 G) y
           (\m. if m = 1 then basis a else if m = 2 then basis b
                else if m = 3 then basis p else basis q) =
         pde_jhess (dimindex(:N)) (pde_jg G y) (pde_jd1 G y) (pde_jd2 G y)
                   (pde_jhc H y) (pde_jhdc H y) a b p q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  ABBREV_TAC `S = lnabla 2 (H:real^N->real^N^N) (lmetric2 (G:real^N->real^N^N))` THEN
  ABBREV_TAC `u4 = \m. if m = 1 then basis a else if m = 2 then basis b
                       else if m = 3 then basis p else basis q:real^N` THEN
  SUBGOAL_THEN `(u4:num->real^N) 1 = basis a /\ u4 2 = basis b /\ u4 3 = basis p /\
                u4 4 = basis q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u4" THEN CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `H:real^N->real^N^N`]
                PDE_LNABLA2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[PDE_LNABLA_ITER_2; ARITH_RULE `2 + 1 = 3`] THEN
  ASM_REWRITE_TAC[LRG_LNABLA_EQ; ARITH_RULE `3 + 1 = 4`; SUM_3] THEN
  REWRITE_TAC[GSYM partial_derivative] THEN
  SUBGOAL_THEN
   `drop(partial_derivative q (\x. lift((S:real^N->(num->real^N)->real) x u4)) y) =
    pde_jdsl (dimindex(:N)) (pde_jg G y) (pde_jd1 G y) (pde_jd2 G y)
             (pde_jhc H y) (pde_jhdc H y) a b p q`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `drop(partial_derivative q
             (\x. lift(pde_jsl (dimindex(:N)) (pde_jg (G:real^N->real^N^N) x) (pde_jd1 G x)
                               (pde_jhc (H:real^N->real^N^N) x) a b p)) y)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      EXPAND_TAC "S" THEN MATCH_MP_TAC PDE_LNABLA2_BASIS THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_JSL_PARTIAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i (v:real^N). 1 <= i /\ i <= 3
        ==> (S:real^N->(num->real^N)->real) y (\j. if j = i then v else u4 j) =
            sum(1..dimindex(:N)) (\r. v$r * S y (\j. if j = i then basis r else u4 j))`
  (LABEL_TAC "SLOT") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SLOT_EXPAND THEN
    UNDISCH_TAC `ltensor_field 3 U (S:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. 1 <= r /\ r <= dimindex(:N)
        ==> (S:real^N->(num->real^N)->real) y (\j. if j = 1 then basis r else u4 j) =
            pde_jsl (dimindex(:N)) (pde_jg G y) (pde_jd1 G y) (pde_jhc H y) r b p /\
            S y (\j. if j = 2 then basis r else u4 j) =
            pde_jsl (dimindex(:N)) (pde_jg G y) (pde_jd1 G y) (pde_jhc H y) a r p /\
            S y (\j. if j = 3 then basis r else u4 j) =
            pde_jsl (dimindex(:N)) (pde_jg G y) (pde_jd1 G y) (pde_jhc H y) a b r`
  (LABEL_TAC "BAS") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "S" THEN MATCH_MP_TAC PDE_LNABLA2_BASIS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "SLOT" (fun th ->
    ONCE_REWRITE_TAC[MATCH_MP th (ARITH_RULE `1 <= 1 /\ 1 <= 3`);
                MATCH_MP th (ARITH_RULE `1 <= 2 /\ 2 <= 3`);
                MATCH_MP th (ARITH_RULE `1 <= 3 /\ 3 <= 3`)]) THEN
  REWRITE_TAC[pde_jhess] THEN AP_TERM_TAC THEN
  BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  USE_THEN "BAS" (fun th -> REWRITE_TAC[MATCH_MP th
    (CONJ (ASSUME `1 <= r`) (ASSUME `r <= dimindex(:N)`))]) THEN
  REWRITE_TAC[pde_jhc]);;

let PDE_TRHESS_JET = prove
 (`!U (H:real^N->real^N^N) G y a b.
     metric_field U G /\ metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> pde_ltrhess G H G y $a$b =
         pde_jtrhess (dimindex(:N)) (pde_jg G y) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y)
                     (pde_jhc H y) (pde_jhdc H y) a b`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[pde_ltrhess; LAMBDA_BETA] THEN
  REWRITE_TAC[pde_jtrhess] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  REWRITE_TAC[pde_jgi] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PDE_HESS4_JET THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The operator as a jet formula, the cancellation of the second             *)
(* derivatives, the symbol F (smooth in the point, G and DG), and            *)
(* PDE_LRDT_SYMBOL.                                                          *)
(* ========================================================================= *)

let PDE_LRDT_ENTRY_JET = prove
 (`!U (H:real^N->real^N^N) G y a b.
     metric_field U G /\ metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> (pde_lrdt H G y - pde_ltrhess G H G y)$a$b =
         pde_jdj (dimindex(:N)) (pde_jg G y) (pde_jgi G y) (pde_jd1 G y) (pde_jd2 G y)
                 (pde_jhc H y) (pde_jhdc H y) a b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_lrdt; MATRIX_SUB_COMPONENT; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT;
              pde_lricci_matrix] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:num`; `b:num`]
                PDE_RIC_JET) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:num`; `b:num`] PDE_LLIE_JET) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:num`; `b:num`] PDE_TRHESS_JET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[pde_jdj] THEN REAL_ARITH_TAC);;

(* The symmetries needed for the cancellation. *)

let PDE_JD2_SYM = prove
 (`!U (G:real^N->real^N^N) y c e i j.
     metric_field U G /\ y IN U /\
     1 <= c /\ c <= dimindex(:N) /\ 1 <= e /\ e <= dimindex(:N)
     ==> pde_jd2 G y c e i j = pde_jd2 G y e c i j /\
         pde_jd2 G y c e i j = pde_jd2 G y c e j i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pde_jd2; iterated_partial] THEN
    SUBGOAL_THEN
     `partial_derivative c (partial_derivative e
        ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))) y =
      partial_derivative e (partial_derivative c (vectorize o G)) y`
    (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[smooth_map_on]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k l. ((matrify:real^(N,N)finite_prod->real^N^N)
             (iterated_partial [c; e] ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                         (G:real^N->real^N^N)) y))$k$l =
          drop(iterated_partial [c; e] (\z. lift((G z)$k$l)) y)`
  (fun th -> REWRITE_TAC[pde_jd2; th]) THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`[c; e]:num list`;
                   `\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$k$l)`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)`;
                   `U:real^N->bool`; `y:real^N`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; o_THM; MATRIFY_VECTORIZE] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o AP_TERM `\M:real^N^N. M$i$j`) THEN REWRITE_TAC[TRANSP_COMPONENT] THEN
  SIMP_TAC[]);;

let PDE_LRDT_ENTRY_D2FREE = prove
 (`!U (H:real^N->real^N^N) G y a b.
     metric_field U G /\ metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> (pde_lrdt H G y - pde_ltrhess G H G y)$a$b =
         pde_jdj (dimindex(:N)) (pde_jg G y) (pde_jgi G y) (pde_jd1 G y) (\c e i j. &0)
                 (pde_jhc H y) (pde_jhdc H y) a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:num`; `b:num`] PDE_LRDT_ENTRY_JET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PDE_JDJ_D2_FREE THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pde_jgi] THEN ASM_MESON_TAC[LRG_MATRIX_INV_SYM];
    REWRITE_TAC[pde_jg] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\M:real^N^N. M$j$i`) THEN REWRITE_TAC[TRANSP_COMPONENT];
    REWRITE_TAC[pde_jg; pde_jgi] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MATRIX_INV o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\M:real^N^N. M$i$j`) THEN
    ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; MAT_COMPONENT] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PDE_JD2_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Smoothness of the jet formulas in smooth jets. *)

let PDE_SM_JCHR = prove
 (`!S n (gi:real^M->num->num->real) (d1:real^M->num->num->num->real) m a b.
     open S /\ (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j)))
     ==> smooth_map_on S (\x. lift(pde_jchr n (gi x) (d1 x) m a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jchr] THEN PDE_SMOOTH_REAL_TAC []);;

let PDE_SM_JDGI = prove
 (`!S n (gi:real^M->num->num->real) (d1:real^M->num->num->num->real) c i j.
     open S /\ (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j)))
     ==> smooth_map_on S (\x. lift(pde_jdgi n (gi x) (d1 x) c i j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jdgi] THEN PDE_SMOOTH_REAL_TAC []);;

let PDE_SM_JDCHR = prove
 (`!S n (gi:real^M->num->num->real) (d1:real^M->num->num->num->real)
    (d2:real^M->num->num->num->num->real) c m a b.
     open S /\ (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j)))
     ==> smooth_map_on S (\x. lift(pde_jdchr n (gi x) (d1 x) (d2 x) c m a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jdchr] THEN PDE_SMOOTH_REAL_TAC [PDE_SM_JDGI]);;

let PDE_SM_JRIC = prove
 (`!S n (gi:real^M->num->num->real) (d1:real^M->num->num->num->real)
    (d2:real^M->num->num->num->num->real) a b.
     open S /\ (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j)))
     ==> smooth_map_on S (\x. lift(pde_jric n (gi x) (d1 x) (d2 x) a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jric] THEN
  PDE_SMOOTH_REAL_TAC [PDE_SM_JDCHR; PDE_SM_JCHR]);;

let PDE_SM_JW = prove
 (`!S n (gi:real^M->num->num->real) (d1:real^M->num->num->num->real)
    (hc:real^M->num->num->num->real) m.
     open S /\ (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j)))
     ==> smooth_map_on S (\x. lift(pde_jw n (gi x) (d1 x) (hc x) m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jw] THEN PDE_SMOOTH_REAL_TAC [PDE_SM_JCHR]);;

let PDE_SM_JDW = prove
 (`!S n (gi:real^M->num->num->real) (d1:real^M->num->num->num->real)
    (d2:real^M->num->num->num->num->real) (hc:real^M->num->num->num->real)
    (hdc:real^M->num->num->num->num->real) c m.
     open S /\ (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(hdc x c e i j)))
     ==> smooth_map_on S (\x. lift(pde_jdw n (gi x) (d1 x) (d2 x) (hc x) (hdc x) c m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jdw] THEN
  PDE_SMOOTH_REAL_TAC [PDE_SM_JDGI; PDE_SM_JCHR; PDE_SM_JDCHR]);;

let PDE_SM_JLW = prove
 (`!S n (g:real^M->num->num->real) (gi:real^M->num->num->real)
    (d1:real^M->num->num->num->real) (d2:real^M->num->num->num->num->real)
    (hc:real^M->num->num->num->real) (hdc:real^M->num->num->num->num->real) a b.
     open S /\ (!i j. smooth_map_on S (\x. lift(g x i j))) /\
     (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(hdc x c e i j)))
     ==> smooth_map_on S
           (\x. lift(pde_jlw n (g x) (gi x) (d1 x) (d2 x) (hc x) (hdc x) a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jlw] THEN
  PDE_SMOOTH_REAL_TAC [PDE_SM_JW; PDE_SM_JDW]);;

let PDE_SM_JSL = prove
 (`!S n (g:real^M->num->num->real) (d1:real^M->num->num->num->real)
    (hc:real^M->num->num->num->real) a b p.
     open S /\ (!i j. smooth_map_on S (\x. lift(g x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j)))
     ==> smooth_map_on S (\x. lift(pde_jsl n (g x) (d1 x) (hc x) a b p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jsl] THEN PDE_SMOOTH_REAL_TAC []);;

let PDE_SM_JDSL = prove
 (`!S n (g:real^M->num->num->real) (d1:real^M->num->num->num->real)
    (d2:real^M->num->num->num->num->real) (hc:real^M->num->num->num->real)
    (hdc:real^M->num->num->num->num->real) a b p q.
     open S /\ (!i j. smooth_map_on S (\x. lift(g x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(hdc x c e i j)))
     ==> smooth_map_on S (\x. lift(pde_jdsl n (g x) (d1 x) (d2 x) (hc x) (hdc x) a b p q))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jdsl] THEN PDE_SMOOTH_REAL_TAC []);;

let PDE_SM_JHESS = prove
 (`!S n (g:real^M->num->num->real) (d1:real^M->num->num->num->real)
    (d2:real^M->num->num->num->num->real) (hc:real^M->num->num->num->real)
    (hdc:real^M->num->num->num->num->real) a b p q.
     open S /\ (!i j. smooth_map_on S (\x. lift(g x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(hdc x c e i j)))
     ==> smooth_map_on S (\x. lift(pde_jhess n (g x) (d1 x) (d2 x) (hc x) (hdc x) a b p q))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jhess] THEN
  PDE_SMOOTH_REAL_TAC [PDE_SM_JDSL; PDE_SM_JSL]);;

let PDE_SM_JTRHESS = prove
 (`!S n (g:real^M->num->num->real) (gi:real^M->num->num->real)
    (d1:real^M->num->num->num->real) (d2:real^M->num->num->num->num->real)
    (hc:real^M->num->num->num->real) (hdc:real^M->num->num->num->num->real) a b.
     open S /\ (!i j. smooth_map_on S (\x. lift(g x i j))) /\
     (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(hdc x c e i j)))
     ==> smooth_map_on S
           (\x. lift(pde_jtrhess n (g x) (gi x) (d1 x) (d2 x) (hc x) (hdc x) a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jtrhess] THEN
  PDE_SMOOTH_REAL_TAC [PDE_SM_JHESS]);;

let PDE_SM_JDJ = prove
 (`!S n (g:real^M->num->num->real) (gi:real^M->num->num->real)
    (d1:real^M->num->num->num->real) (d2:real^M->num->num->num->num->real)
    (hc:real^M->num->num->num->real) (hdc:real^M->num->num->num->num->real) a b.
     open S /\ (!i j. smooth_map_on S (\x. lift(g x i j))) /\
     (!i j. smooth_map_on S (\x. lift(gi x i j))) /\
     (!c i j. smooth_map_on S (\x. lift(d1 x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(d2 x c e i j))) /\
     (!c i j. smooth_map_on S (\x. lift(hc x c i j))) /\
     (!c e i j. smooth_map_on S (\x. lift(hdc x c e i j)))
     ==> smooth_map_on S
           (\x. lift(pde_jdj n (g x) (gi x) (d1 x) (d2 x) (hc x) (hdc x) a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jdj] THEN
  PDE_SMOOTH_REAL_TAC [PDE_SM_JRIC; PDE_SM_JLW; PDE_SM_JTRHESS]);;

(* ========================================================================= *)
(* The symbol F of the Ricci-DeTurck operator, a smooth function of          *)
(* (y, G(y), DG(y)), and PDE_LRDT_SYMBOL.                                    *)
(* ========================================================================= *)

let pde_rdt_sym = new_definition
 `pde_rdt_sym (H:real^N->real^N^N)
    (x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum) =
    (vectorize:real^N^N->real^(N,N)finite_prod)
    ((lambda a b.
       pde_jdj (dimindex(:N))
         (\i j. ((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x)))$i$j)
         (\i j. matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                             (fstcart(sndcart x)))$i$j)
         (\c i j. ((matrify:real^(N,N)finite_prod->real^N^N)
                     ((matrify:real^((N,N)finite_prod,N)finite_prod->real^N^(N,N)finite_prod)
                        (sndcart(sndcart x)) ** basis c))$i$j)
         (\c e i j. &0) (pde_jhc H (fstcart x)) (pde_jhdc H (fstcart x)) a b):real^N^N)`;;

(* The domain is open. *)

let PDE_SYM_DOMAIN_OPEN = prove
 (`!U:real^N->bool.
     open U
     ==> open {pastecart y (pastecart P Q) |
                 y IN U /\ ~(det((matrify:real^(N,N)finite_prod->real^N^N) P) = &0) /\
                 Q IN (:real^((N,N)finite_prod,N)finite_prod)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{pastecart y (pastecart P Q) |
       y IN U /\ ~(det((matrify:real^(N,N)finite_prod->real^N^N) P) = &0) /\
       Q IN (:real^((N,N)finite_prod,N)finite_prod)} =
    {x | x IN {x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum |
               fstcart x IN U} /\
         invertible((matrify:real^(N,N)finite_prod->real^N^N) ((fstcart o sndcart) x))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM; o_THM; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_UNIV; INVERTIBLE_DET_NZ; PASTECART_INJ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum |
      fstcart x IN (U:real^N->bool)}`;
    `(fstcart o sndcart):real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                         finite_sum->real^(N,N)finite_prod`] PDE_OPEN_INVERTIBLE_SET) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE THEN
    REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]]);;

(* Smoothness of the atoms of F. *)

let PDE_SYM_ATOM_P = prove
 (`!S i j.
     open S
     ==> smooth_map_on S
           (\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
              lift(((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x)))$i$j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
       lift(((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x)))$i$j)) =
    (\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)) o (fstcart o sndcart)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC LINEAR_COMPOSE THEN CONJ_TAC) THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART; LRG_LINEAR_MATRIFY_ENTRY]);;

let PDE_SYM_ATOM_PINV = prove
 (`!S i j.
     open S /\
     (!x. x IN S ==> ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x))) = &0))
     ==> smooth_map_on S
           (\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
              lift(matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                                (fstcart(sndcart x)))$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
       lift(matrix_inv((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x)))$i$j)) =
    (\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)) o
    ((vectorize:real^N^N->real^(N,N)finite_prod) o
     (\x. matrix_inv((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x)))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY] THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
       fstcart(sndcart x)) = fstcart o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let PDE_SYM_ATOM_Q = prove
 (`!S c i j.
     open S
     ==> smooth_map_on S
           (\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
              lift(((matrify:real^(N,N)finite_prod->real^N^N)
                     ((matrify:real^((N,N)finite_prod,N)finite_prod->real^N^(N,N)finite_prod)
                        (sndcart(sndcart x)) ** basis c))$i$j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL; MATRIFY_ADD; MATRIFY_CMUL;
              MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; MATRIX_ADD_COMPONENT;
              MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let PDE_SYM_ATOM_HC = prove
 (`!S (U:real^N->bool) H m a b.
     open S /\ metric_field U H /\
     (!x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
        x IN S ==> fstcart x IN U)
     ==> smooth_map_on S (\x. lift(christoffel H (fstcart x) (basis a) (basis b)$m))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `(\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
       lift(christoffel (H:real^N->real^N^N) (fstcart x) (basis a) (basis b)$m)) =
    (\z. lift(christoffel H z (basis a) (basis b)$m)) o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[PDE_SMOOTH_CHR_ENTRY] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART]]);;

let PDE_SYM_ATOM_HDC = prove
 (`!S (U:real^N->bool) H c m a b.
     open S /\ metric_field U H /\
     (!x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
        x IN S ==> fstcart x IN U)
     ==> smooth_map_on S
           (\x. lift(frechet_derivative (\z. christoffel H z (basis a) (basis b))
                                        (at (fstcart x)) (basis c)$m))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `(\x:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum.
       lift(frechet_derivative (\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b))
                               (at (fstcart x)) (basis c)$m)) =
    ((\v:real^N. lift(v$m)) o
     partial_derivative c (\z. christoffel H z (basis a) (basis b))) o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; partial_derivative]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

(* F is smooth. *)

let PDE_RDT_SYM_SMOOTH = prove
 (`!(U:real^N->bool) (H:real^N->real^N^N).
     metric_field U H
     ==> smooth_map_on
           {pastecart y (pastecart P Q) |
              y IN U /\ ~(det((matrify:real^(N,N)finite_prod->real^N^N) P) = &0) /\
              Q IN (:real^((N,N)finite_prod,N)finite_prod)}
           (pde_rdt_sym H)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  ABBREV_TAC
   `S0 = {pastecart y (pastecart P Q) |
            y IN (U:real^N->bool) /\ ~(det((matrify:real^(N,N)finite_prod->real^N^N) P) = &0) /\
            Q IN (:real^((N,N)finite_prod,N)finite_prod)}` THEN
  SUBGOAL_THEN
   `open (S0:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum
               ->bool) /\
    !x. x IN S0
        ==> fstcart x IN U /\
            ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x))) = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "S0" THEN MATCH_MP_TAC PDE_SYM_DOMAIN_OPEN THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "S0" THEN
      REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_rdt_sym (H:real^N->real^N^N) =
    (vectorize:real^N^N->real^(N,N)finite_prod) o
    (\x. (lambda a b.
       pde_jdj (dimindex(:N))
         (\i j. ((matrify:real^(N,N)finite_prod->real^N^N) (fstcart(sndcart x)))$i$j)
         (\i j. matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                             (fstcart(sndcart x)))$i$j)
         (\c i j. ((matrify:real^(N,N)finite_prod->real^N^N)
                     ((matrify:real^((N,N)finite_prod,N)finite_prod->real^N^(N,N)finite_prod)
                        (sndcart(sndcart x)) ** basis c))$i$j)
         (\c e i j. &0) (pde_jhc H (fstcart x)) (pde_jhdc H (fstcart x)) a b):real^N^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_rdt_sym; o_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MATCH_MP_TAC PDE_SM_JDJ THEN ASM_REWRITE_TAC[pde_jhc; pde_jhdc] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MATCH_MP_TAC PDE_SYM_ATOM_P THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_SYM_ATOM_PINV THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC PDE_SYM_ATOM_Q THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    MATCH_MP_TAC PDE_SYM_ATOM_HC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC PDE_SYM_ATOM_HDC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[]]);;

(* The quasilinear structure of the Ricci-DeTurck operator. *)

let PDE_LRDT_SYMBOL = prove
 (`!(U:real^N->bool) (H:real^N->real^N^N).
        metric_field U H
        ==> ?F. smooth_map_on
                  {pastecart y (pastecart P Q) |
                     y IN U /\ ~(det((matrify:real^(N,N)finite_prod->real^N^N) P) = &0) /\
                     Q IN (:real^((N,N)finite_prod,N)finite_prod)}
                  (F:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum
                     ->real^(N,N)finite_prod) /\
                !G y. metric_field U G /\ y IN U
                      ==> pde_lrdt H G y =
                          pde_ltrhess G H G y +
                          (matrify:real^(N,N)finite_prod->real^N^N)
                          (F (pastecart y
                               (pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G y))
                                 ((vectorize:real^N^(N,N)finite_prod->
                                             real^((N,N)finite_prod,N)finite_prod)
                                  (matrix(frechet_derivative
                                           ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                           (at y)))))))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `pde_rdt_sym (H:real^N->real^N^N)` THEN
  ASM_SIMP_TAC[PDE_RDT_SYM_SMOOTH] THEN
  MAP_EVERY X_GEN_TAC [`G:real^N->real^N^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. matrix(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                   (G:real^N->real^N^N)) (at y)) ** v =
        frechet_derivative (vectorize o G) (at y) v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_WORKS THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_ADD_COMPONENT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x = y + z <=> x - y = z`] THEN
  REWRITE_TAC[GSYM MATRIX_SUB_COMPONENT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:num`; `b:num`] PDE_LRDT_ENTRY_D2FREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pde_rdt_sym; MATRIFY_VECTORIZE; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[pde_jg; pde_jgi; pde_jd1; mderiv]);;

(* ========================================================================= *)
(* Naturality, part 1.  Matrices as bilinear forms, the Ricci matrix of      *)
(* a pullback, the congruence identity J (J^T M J)^-1 J^T = M^-1, and the    *)
(* DeTurck field of pullbacks: D phi (W(phi^* H, phi^* G)) = W(H,G) o phi.   *)
(* ========================================================================= *)

let PDE_MATRIX_EQ_DOT = prove
 (`!A B:real^N^N. (!a b. a dot (A ** b) = a dot (B ** b)) ==> A = B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`basis i:real^N`; `basis j:real^N`]) THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT]);;

let PDE_LRICCI_MATRIX_DOT = prove
 (`!U (G:real^N->real^N^N) y a b.
     metric_field U G /\ y IN U
     ==> a dot (pde_lricci_matrix G y ** b) = lricci G y a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`; `b:real^N`]
                LRG_LRICCI_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN
  STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; pde_lricci_matrix; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REAL_ARITH_TAC);;

(* The congruence identity. *)

let PDE_INV_CONGR = prove
 (`!(J:real^N^N) (M:real^N^N).
     invertible J /\ invertible M
     ==> J ** matrix_inv(transp J ** M ** J) ** transp J = matrix_inv M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(transp(J:real^N^N)) /\ invertible((M:real^N^N) ** (J:real^N^N))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_TRANSP; INVERTIBLE_MATRIX_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL] THEN
  MP_TAC(ISPEC `J:real^N^N` MATRIX_INV) THEN
  MP_TAC(ISPEC `transp J:real^N^N` MATRIX_INV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(J:real^N^N) ** ((matrix_inv J ** matrix_inv M) ** matrix_inv(transp J)) ** transp J =
    ((J ** matrix_inv J) ** matrix_inv M) ** (matrix_inv(transp J) ** transp J)`
  SUBST1_TAC THENL [REWRITE_TAC[MATRIX_MUL_ASSOC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let PDE_SUM4_SWAP = prove
 (`!n (FF:num->num->num->num->real).
     sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\p. sum(1..n) (\q. FF i j p q)))) =
     sum(1..n) (\p. sum(1..n) (\q. sum(1..n) (\i. sum(1..n) (\j. FF i j p q))))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\i. sum(1..n) (\p. sum(1..n) (\q. sum(1..n)
                 (\j. (FF:num->num->num->num->real) i j p q))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [PDE_JSWAP3] THEN REWRITE_TAC[];
    GEN_REWRITE_TAC LAND_CONV [PDE_JSWAP3] THEN REWRITE_TAC[]]);;

let PDE_TRACE_CONGR_SUM = prove
 (`!(J:real^N^N) (M:real^N^N) (A:num->num->real).
     invertible J /\ invertible M
     ==> sum(1..dimindex(:N))
           (\i. sum(1..dimindex(:N))
                  (\j. matrix_inv(transp J ** M ** J)$i$j *
                       sum(1..dimindex(:N))
                         (\p. sum(1..dimindex(:N)) (\q. J$p$i * J$q$j * A p q)))) =
         sum(1..dimindex(:N))
           (\p. sum(1..dimindex(:N)) (\q. matrix_inv M$p$q * A p q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP PDE_INV_CONGR
    (CONJ (ASSUME `invertible(J:real^N^N)`) (ASSUME `invertible(M:real^N^N)`))) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [PDE_SUM4_SWAP] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; TRANSP_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Components of Christoffel symbols at general vectors. *)

let PDE_CHR_EXPAND = prove
 (`!U (G:real^N->real^N^N) y u v m.
     metric_field U G /\ y IN U
     ==> christoffel G y u v $m =
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N))
           (\q. u$p * v$q * christoffel G y (basis p) (basis q) $m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L2") (LABEL_TAC "L1")) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [GSYM BASIS_EXPANSION] THEN
  USE_THEN "L1" (fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_VSUM_MUL
      (CONJ (SPEC `v:real^N` th) (SPECL [`1`; `dimindex(:N)`] FINITE_NUMSEG)))]) THEN
  REWRITE_TAC[VSUM_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  USE_THEN "L2" (fun th -> REWRITE_TAC[MATCH_MP LINEAR_VSUM_MUL
      (CONJ (SPEC `basis p:real^N` th) (SPECL [`1`; `dimindex(:N)`] FINITE_NUMSEG))]) THEN
  REWRITE_TAC[VSUM_COMPONENT; VECTOR_MUL_COMPONENT; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The DeTurck field of pulled back metrics. *)

let PDE_DIFFEO_JAC_INVERTIBLE = prove
 (`!(U:real^N->bool) U' (phi:real^N->real^N) phi' z.
     diffeomorphism_on U' U phi phi' /\ z IN U'
     ==> invertible(matrix(frechet_derivative phi (at z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `z:real^N`] LRG_DIFFEO_INV_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
  EXISTS_TAC `matrix(frechet_derivative (phi':real^N->real^N) (at (phi(z:real^N))))` THEN
  ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
  SUBGOAL_THEN
   `frechet_derivative (phi':real^N->real^N) (at (phi(z:real^N))) o
    frechet_derivative phi (at z) = I`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]; REWRITE_TAC[MATRIX_I]]);;

let PDE_LDETURCK_PULLBACK = prove
 (`!(U:real^N->bool) U' (phi:real^N->real^N) phi' H G z.
     diffeomorphism_on U' U phi phi' /\ metric_field U H /\ metric_field U G /\ z IN U'
     ==> frechet_derivative phi (at z)
           (pde_ldeturck (mpullback phi H) (mpullback phi G) z) =
         pde_ldeturck H G (phi z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `z:real^N`] PDE_DIFFEO_JAC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `G:real^N->real^N^N`; `z:real^N`]
                LCHRISTOFFEL_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `H:real^N->real^N^N`; `z:real^N`]
                LCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "PH") THEN DISCH_THEN(LABEL_TAC "PG") THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[PDE_LDETURCK_COMPONENT; pde_ldeturck] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; LINEAR_SUB] THEN
  REWRITE_TAC[VSUM_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  USE_THEN "PG" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "PH" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_ARITH `(a + c) - (b + c) = a - b:real`] THEN
  REWRITE_TAC[mpullback] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      matrix_inv(transp(matrix(frechet_derivative (phi:real^N->real^N) (at z))) **
                 (G:real^N->real^N^N) (phi z) ** matrix(frechet_derivative phi (at z)))$i$j *
      sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
        matrix(frechet_derivative phi (at z))$p$i *
        matrix(frechet_derivative phi (at z))$q$j *
        (christoffel G (phi z) (basis p) (basis q)$m -
         christoffel (H:real^N->real^N^N) (phi z) (basis p) (basis q)$m)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(phi:real^N->real^N) z`;
                   `frechet_derivative (phi:real^N->real^N) (at z) (basis i)`;
                   `frechet_derivative (phi:real^N->real^N) (at z) (basis j)`; `m:num`]
                  PDE_CHR_EXPAND) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `(phi:real^N->real^N) z`;
                   `frechet_derivative (phi:real^N->real^N) (at z) (basis i)`;
                   `frechet_derivative (phi:real^N->real^N) (at z) (basis j)`; `m:num`]
                  PDE_CHR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[matrix; LAMBDA_BETA] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PDE_TRACE_CONGR_SUM THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]]);;

(* ========================================================================= *)
(* Naturality, part 2.  The Lie derivative of a pulled back metric along     *)
(* a related vector field, and PDE_LRDT_PULLBACK.                            *)
(* ========================================================================= *)

(* Differentiating D phi (z) X'(z) = X(phi z). *)

let PDE_RELATED_DERIV = prove
 (`!(U:real^N->bool) U' (phi:real^N->real^N) phi' (X:real^N->real^N) X' y v.
     diffeomorphism_on U' U phi phi' /\ smooth_map_on U X /\ smooth_map_on U' X' /\
     (!z. z IN U' ==> frechet_derivative phi (at z) (X' z) = X(phi z)) /\ y IN U'
     ==> frechet_derivative phi (at y) (frechet_derivative X' (at y) v) =
         frechet_derivative X (at (phi y)) (frechet_derivative phi (at y) v) -
         dd2 phi y v (X' y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(X':real^N->real^N) differentiable (at y) /\
                (X:real^N->real^N) differentiable (at (phi y)) /\
                (phi:real^N->real^N) differentiable (at y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. frechet_derivative (phi:real^N->real^N) (at z)`; `X':real^N->real^N`;
                 `frechet_derivative (X':real^N->real^N) (at y)`; `U':real^N->bool`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_DIFFEO_LINEAR_AT];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`U':real^N->bool`; `phi:real^N->real^N`; `y:real^N`; `basis i:real^N`]
                    LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. frechet_derivative (phi:real^N->real^N) (at z) (X' z)) (at y) =
    frechet_derivative (\z. (X:real^N->real^N)(phi z)) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^N`) THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LRG_FRECHET_DERIVATIVE_CHAIN] THEN
  REWRITE_TAC[dd2] THEN VECTOR_ARITH_TAC);;

(* The Lie derivative of a pullback along a related vector field. *)

let PDE_LLIE_PULLBACK = prove
 (`!(U:real^N->bool) U' (phi:real^N->real^N) phi' (G:real^N->real^N^N) X X' y a b.
     diffeomorphism_on U' U phi phi' /\ metric_field U G /\
     smooth_map_on U X /\ smooth_map_on U' X' /\
     (!z. z IN U' ==> frechet_derivative phi (at z) (X' z) = X(phi z)) /\ y IN U'
     ==> a dot (llie X' (mpullback phi G) y ** b) =
         frechet_derivative phi (at y) a dot
         (llie X G (phi y) ** frechet_derivative phi (at y) b)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(X':real^N->real^N) differentiable (at y) /\
                (X:real^N->real^N) differentiable (at (phi y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (X':real^N->real^N) (at y)) /\
                linear(frechet_derivative (X:real^N->real^N) (at (phi y)))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `X:real^N->real^N`; `X':real^N->real^N`; `y:real^N`]
                PDE_RELATED_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `(X':real^N->real^N) y`] LRG_MDERIV_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `dd2 (phi:real^N->real^N) y ((X':real^N->real^N) y) a = dd2 phi y a (X' y) /\
    dd2 phi y (X' y) b = dd2 phi y b (X' y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_DD2_SYM THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[llie; MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  MP_TAC(ISPECL [`phi:real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_MPULLBACK_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_LSUB; DOT_RSUB] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

(* Naturality of the Ricci-DeTurck operator. *)

let PDE_LRDT_PULLBACK = prove
 (`!(U:real^N->bool) U' (phi:real^N->real^N) phi' H G y.
        diffeomorphism_on U' U phi phi' /\ metric_field U H /\ metric_field U G /\ y IN U'
        ==> pde_lrdt (mpullback phi H) (mpullback phi G) y =
            transp(matrix(frechet_derivative phi (at y))) ** pde_lrdt H G (phi y) **
            matrix(frechet_derivative phi (at y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U' (mpullback (phi:real^N->real^N) G) /\
                metric_field U' (mpullback (phi:real^N->real^N) H)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `phi':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_MATRIX_EQ_DOT THEN MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[pde_lrdt; MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; DOT_RADD;
              DOT_RMUL] THEN
  BINOP_TAC THENL
   [AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U':real^N->bool`; `mpullback (phi:real^N->real^N) G`; `y:real^N`;
                   `a:real^N`; `b:real^N`] PDE_LRICCI_MATRIX_DOT) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(phi:real^N->real^N) y`;
                   `frechet_derivative (phi:real^N->real^N) (at y) a`;
                   `frechet_derivative (phi:real^N->real^N) (at y) b`] PDE_LRICCI_MATRIX_DOT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC LRICCI_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `phi':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_LLIE_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `phi':real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDE_LDETURCK_SMOOTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_LDETURCK_SMOOTH THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_LDETURCK_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `phi':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

