(* ========================================================================= *)
(* Unit pc_rfa_halg: the pointwise algebra of Hamilton's matrix Harnack      *)
(* quadratic.  If the quadratic Z = rfa_hz is nonnegative on all (U          *)
(* antisymmetric, W), then the reaction term J = rfa_hj is nonnegative (CLN, *)
(* Hamilton's Ricci Flow, (10.63)-(10.64)).  Main theorem: RFA_HARNACK_ALG   *)
(* proves the statement RFA_HARNACK_ALG_STATEMENT of pc_rfa_u17iface.        *)
(*                                                                           *)
(* Route.  (1) A Gram decomposition of positive semidefinite symmetric      *)
(* forms on a finite set (Cholesky-type induction, RFAH_GRAM).  (2) The     *)
(* slot form: Z is the quadratic form of a symmetric array G on the slots    *)
(* (0,c) (for W) and (a,b) (for U) of (0..n) CROSS (1..n), evaluated at the  *)
(* antisymmetric part of the U-slots (RFAH_SLOT_QF).  (3) The Gram vectors   *)
(* give X k a and antisymmetric Y k a b with M, P, R the sums of X X, Y X    *)
(* and Y Y over k (RFAH_SLOT_REPR).  (4) With these, J is the double sum     *)
(* over k, k' of the squares (A k k' - A k' k + 2 B k k') with               *)
(* A k k' = W_a Y^k_ac X^k'_c, B k k' = U_ab Y^k_ad Y^k'_db (RFAH_HJ_GRAM). *)
(* ========================================================================= *)

needs "src/pc_rfa_u17iface.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Gram decomposition of a positive semidefinite symmetric                   *)
(* form on a finite set: G i j = sum_k L k i * L k j.                        *)
(* ========================================================================= *)

let RFAH_QF_INSERT = prove
 (`!(G:A->A->real) (v:A->real) x t.
     FINITE t /\ ~(x IN t) /\ (!j. j IN t ==> G j x = G x j)
     ==> sum (x INSERT t) (\i. sum (x INSERT t) (\j. G i j * v i * v j)) =
         G x x * v x * v x + &2 * v x * sum t (\j. G x j * v j) +
         sum t (\i. sum t (\j. G i j * v i * v j))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES; SUM_ADD; ASSUME `FINITE (t:A->bool)`;
           ASSUME `~((x:A) IN t)`] THEN
  SUBGOAL_THEN
   `sum t (\i. (G:A->A->real) i x * v i * v x) =
    v x * sum t (\j. G x j * v j) /\
    sum t (\j. (G:A->A->real) x j * v x * v j) =
    v x * sum t (\j. G x j * v j)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    (SUBGOAL_THEN `(G:A->A->real) j x = G x j` MP_TAC THENL
      [ASM_MESON_TAC[]; CONV_TAC REAL_RING]);
    ALL_TAC] THEN
  ABBREV_TAC `q = sum t (\i. sum t (\j. (G:A->A->real) i j * v i * v j))` THEN
  REAL_ARITH_TAC);;

let RFAH_QF_INSERT_UPD = prove
 (`!(G:A->A->real) (v:A->real) x t tau.
     FINITE t /\ ~(x IN t) /\ (!j. j IN t ==> G j x = G x j)
     ==> sum (x INSERT t) (\i. sum (x INSERT t) (\j.
            G i j * (if i = x then tau else v i) *
            (if j = x then tau else v j))) =
         G x x * tau * tau + &2 * tau * sum t (\j. G x j * v j) +
         sum t (\i. sum t (\j. G i j * v i * v j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A->A->real`; `\i:A. if i = x then tau else (v:A->real) i`;
                 `x:A`; `t:A->bool`] RFAH_QF_INSERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!j:A. j IN t ==> ~(j = x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum t (\j. (G:A->A->real) x j * (if j = x then tau else v j)) =
    sum t (\j. G x j * v j) /\
    sum t (\i. sum t (\j. (G:A->A->real) i j * (if i = x then tau else v i) *
                          (if j = x then tau else v j))) =
    sum t (\i. sum t (\j. G i j * v i * v j))`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]);;

let RFAH_LIN_NONNEG = prove
 (`!a b. (!t. &0 <= &2 * t * a + b) ==> a = &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `--(abs b + &1) / (&2 * a)`) THEN
  ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> &2 * x / (&2 * a) * a = x`] THEN
  REAL_ARITH_TAC);;

let RFAH_SCHUR_REAL = prove
 (`!g s l q. &0 < g /\ s pow 2 = g
             ==> g * --(l / g) * --(l / g) + &2 * --(l / g) * l + q =
                 q - l / s * l / s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s = &0) /\ ~(g = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `s pow 2 = g` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `s pow 2 = g` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `~(s = &0)` THEN CONV_TAC REAL_FIELD);;

let RFAH_SQRT_FACT = prove
 (`!g y. &0 < g ==> y = g / sqrt g * y / sqrt g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt g pow 2 = g /\ ~(sqrt g = &0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`sqrt g`; `y:real`]
    (REAL_FIELD `!s y. ~(s = &0) ==> y = s pow 2 / s * y / s`)) THEN
  ASM_REWRITE_TAC[]);;

let RFAH_QF_RANK1 = prove
 (`!(G:A->A->real) (f:A->real) v t.
     FINITE t
     ==> sum t (\i. sum t (\j. (G i j - f i * f j) * v i * v j)) =
         sum t (\i. sum t (\j. G i j * v i * v j)) -
         sum t (\i. f i * v i) pow 2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC[GSYM SUM_SUB; ASSUME `FINITE (t:A->bool)`] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC REAL_RING);;

let RFAH_GRAM_STEP = prove
 (`!(G:A->A->real) x t.
     FINITE t /\ ~(x IN t) /\
     (!i j. i IN x INSERT t /\ j IN x INSERT t ==> G i j = G j i) /\
     (!v. &0 <= sum (x INSERT t) (\i. sum (x INSERT t) (\j. G i j * v i * v j)))
     ==> ?f:A->real.
           (!j. j IN x INSERT t ==> G x j = f x * f j) /\
           (!v. &0 <= sum t (\i. sum t (\j. (G i j - f i * f j) * v i * v j)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sym") (LABEL_TAC "psd")))) THEN
  SUBGOAL_THEN `!j:A. j IN t ==> (G:A->A->real) j x = G x j`
   (LABEL_TAC "symx") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sym" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau (v:A->real). &0 <= (G:A->A->real) x x * tau * tau +
        &2 * tau * sum t (\j. G x j * v j) +
        sum t (\i. sum t (\j. G i j * v i * v j))`
   (LABEL_TAC "K1") THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "psd" (MP_TAC o SPEC `\i:A. if i = x then tau else (v:A->real) i`) THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:A->A->real`; `v:A->real`; `x:A`; `t:A->bool`; `tau:real`]
      RFAH_QF_INSERT_UPD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "symx" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (G:A->A->real) x x` ASSUME_TAC THENL
   [USE_THEN "K1" (MP_TAC o SPECL [`&1`; `\i:A. &0`]) THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; SUM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(G:A->A->real) x x = &0` THENL
   [SUBGOAL_THEN `!v:A->real. sum t (\j. (G:A->A->real) x j * v j) = &0`
     (LABEL_TAC "L0") THENL
     [GEN_TAC THEN MATCH_MP_TAC RFAH_LIN_NONNEG THEN
      EXISTS_TAC `sum t (\i. sum t (\j. (G:A->A->real) i j * v i * v j))` THEN
      X_GEN_TAC `tau:real` THEN
      USE_THEN "K1" (MP_TAC o SPECL [`tau:real`; `v:A->real`]) THEN
      REWRITE_TAC[ASSUME `(G:A->A->real) x x = &0`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!j:A. j IN t ==> (G:A->A->real) x j = &0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\j:A. (G:A->A->real) x j * G x j`; `t:A->bool`]
        SUM_POS_EQ_0) THEN
      REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE; ASSUME `FINITE (t:A->bool)`] THEN
      ANTS_TAC THENL
       [USE_THEN "L0" (MP_TAC o SPEC `\j:A. (G:A->A->real) x j`) THEN
        REWRITE_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `\i:A. &0` THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
      GEN_TAC THEN USE_THEN "K1" (MP_TAC o SPECL [`&0`; `v:A->real`]) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (G:A->A->real) x x` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= (G:A->A->real) x x`;
                           `~((G:A->A->real) x x = &0)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\i:A. (G:A->A->real) x i / sqrt(G x x)` THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:A` THEN DISCH_TAC THEN MATCH_MP_TAC RFAH_SQRT_FACT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:A->real` THEN
  SIMP_TAC[RFAH_QF_RANK1; ASSUME `FINITE (t:A->bool)`] THEN
  SUBGOAL_THEN
   `sum t (\i. (G:A->A->real) x i / sqrt(G x x) * v i) =
    sum t (\j. G x j * v j) / sqrt(G x x)`
   SUBST1_TAC THENL
   [REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  USE_THEN "K1" (MP_TAC o SPECL
    [`--(sum t (\j. (G:A->A->real) x j * v j) / G x x)`; `v:A->real`]) THEN
  MP_TAC(ISPECL [`(G:A->A->real) x x`; `sqrt((G:A->A->real) x x)`;
                 `sum t (\j. (G:A->A->real) x j * v j)`;
                 `sum t (\i. sum t (\j. (G:A->A->real) i j * v i * v j))`]
    RFAH_SCHUR_REAL) THEN
  SIMP_TAC[SQRT_POW_2; ASSUME `&0 < (G:A->A->real) x x`;
           ASSUME `&0 <= (G:A->A->real) x x`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_2]);;

let RFAH_GRAM = prove
 (`!s:A->bool. FINITE s
     ==> !G:A->A->real.
           (!i j. i IN s /\ j IN s ==> G i j = G j i) /\
           (!v:A->real. &0 <= sum s (\i. sum s (\j. G i j * v i * v j)))
           ==> ?L:A->A->real. !i j. i IN s /\ j IN s
                                    ==> G i j = sum s (\k. L k i * L k j)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `G:A->A->real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sym") (LABEL_TAC "psd")) THEN
  MP_TAC(ISPECL [`G:A->A->real`; `x:A`; `t:A->bool`] RFAH_GRAM_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "sym" ACCEPT_TAC; USE_THEN "psd" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "F1") (LABEL_TAC "F2"))) THEN
  USE_THEN "ih" (MP_TAC o SPEC `\i j. (G:A->A->real) i j - f i * f j`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BINOP_TAC THENL
       [USE_THEN "sym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
        REWRITE_TAC[REAL_MUL_SYM]];
      USE_THEN "F2" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:A->A->real` (LABEL_TAC "L")) THEN
  EXISTS_TAC `\k i. if k = x then (f:A->real) i
                    else if i = x then &0 else (L:A->A->real) k i` THEN
  REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES; ASSUME `FINITE (t:A->bool)`; ASSUME `~((x:A) IN t)`] THEN
  SUBGOAL_THEN
   `sum t (\k. (if k = x then (f:A->real) i
                else if i = x then &0 else (L:A->A->real) k i) *
               (if k = x then f j else if j = x then &0 else L k j)) =
    sum t (\k. (if i = x then &0 else L k i) * (if j = x then &0 else L k j))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(k:A = x)` (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:A = x` THEN ASM_CASES_TAC `j:A = x` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0; REAL_ADD_RID] THENL
   [USE_THEN "F1" MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
    USE_THEN "F1" MATCH_MP_TAC THEN ASM_MESON_TAC[IN_INSERT];
    SUBGOAL_THEN `(G:A->A->real) i x = G x i` SUBST1_TAC THENL
     [USE_THEN "sym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    USE_THEN "F1" MATCH_MP_TAC THEN ASM_MESON_TAC[IN_INSERT];
    SUBGOAL_THEN `(i:A) IN t /\ (j:A) IN t` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    USE_THEN "L" (MP_TAC o SPECL [`i:A`; `j:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;


(* ========================================================================= *)
(* J as a double sum of squares when R, P, M are the sums over               *)
(* k of Y Y, Y X and X X (Y antisymmetric in its last two arguments).        *)
(* ========================================================================= *)

(* Products of nested sums over 1..n, factorized.                            *)

let RFAH_SUM_FACTOR22 = prove
 (`!(f:num->num->real) (g:num->num->real) n.
     sum(1..n) (\a. sum(1..n) (\c. f a c)) *
     sum(1..n) (\b. sum(1..n) (\d. g b d)) =
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
       f a c * g b d))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN REFL_TAC);;

let RFAH_SUM_FACTOR32 = prove
 (`!(f:num->num->num->real) (g:num->num->real) n.
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d. f a b d))) *
     sum(1..n) (\c. sum(1..n) (\e. g c e)) =
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
       sum(1..n) (\e. f a b d * g c e)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN REFL_TAC);;

let RFAH_SUM_FACTOR33 = prove
 (`!(p:num->num->num->real) (q:num->num->num->real) n.
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\e. p a b e))) *
     sum(1..n) (\c. sum(1..n) (\d. sum(1..n) (\h. q c d h))) =
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
       sum(1..n) (\e. sum(1..n) (\h. p a b e * q c d h))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN REFL_TAC);;

(* Sums over a finite index set commute outwards past sums over 1..n.       *)

let RFAH_SUM_SWAP_NS = prove
 (`!s:K->bool. FINITE s
     ==> !(f:num->K->real) n.
           sum(1..n) (\i. sum s (f i)) = sum s (\j. sum(1..n) (\i. f i j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG]);;

let RFAH_DSUM_SWAP = prove
 (`!(s:K->bool) (f:K->K->real).
     FINITE s
     ==> sum s (\k. sum s (\k'. f k' k)) = sum s (\k. sum s (\k'. f k k'))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k:K k':K. (f:K->K->real) k' k`; `s:K->bool`; `s:K->bool`]
    SUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* The four terms of rfa_hj for the sum-of-products tensors.                *)

let RFAH_T1 = prove
 (`!n (s:K->bool) (X:K->num->real) (Y:K->num->num->real) (W:num->real).
     FINITE s
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           sum s (\k. Y k a c * Y k b d) * sum s (\k. X k c * X k d) *
           W a * W b)))) =
         sum s (\k. sum s (\k'.
           sum(1..n) (\a. sum(1..n) (\c. W a * Y k a c * X k' c)) *
           sum(1..n) (\a. sum(1..n) (\c. W a * Y k a c * X k' c))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFAH_SUM_FACTOR22] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[RFAH_SUM_SWAP_NS] THEN
  REPEAT(MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
  REAL_ARITH_TAC);;

let RFAH_T2 = prove
 (`!n (s:K->bool) (X:K->num->real) (Y:K->num->num->real) (W:num->real).
     FINITE s
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           sum s (\k. Y k a c * X k d) * sum s (\k. Y k b d * X k c) *
           W a * W b)))) =
         sum s (\k. sum s (\k'.
           sum(1..n) (\a. sum(1..n) (\c. W a * Y k a c * X k' c)) *
           sum(1..n) (\a. sum(1..n) (\c. W a * Y k' a c * X k c))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFAH_SUM_FACTOR22] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[RFAH_SUM_SWAP_NS] THEN
  REPEAT(MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
  REAL_ARITH_TAC);;

let RFAH_T3 = prove
 (`!n (s:K->bool) (X:K->num->real) (Y:K->num->num->real)
    (U:num->num->real) (W:num->real).
     FINITE s
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           sum(1..n) (\e.
             sum s (\k. Y k a d * Y k c e) * sum s (\k. Y k d b * X k e) *
             U a b * W c))))) =
         sum s (\k. sum s (\k'.
           sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d.
             U a b * Y k a d * Y k' d b))) *
           sum(1..n) (\a. sum(1..n) (\c. W a * Y k a c * X k' c))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFAH_SUM_FACTOR32] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[RFAH_SUM_SWAP_NS] THEN
  REPEAT(MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
  REAL_ARITH_TAC);;

let RFAH_T4 = prove
 (`!n (s:K->bool) (Y:K->num->num->real) (U:num->num->real).
     FINITE s
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           sum(1..n) (\e. sum(1..n) (\f.
             sum s (\k. Y k a e * Y k c f) * sum s (\k. Y k b e * Y k d f) *
             U a b * U c d)))))) =
         sum s (\k. sum s (\k'.
           sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\e.
             U a b * Y k a e * Y k' b e))) *
           sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\e.
             U a b * Y k a e * Y k' b e)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFAH_SUM_FACTOR33] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[RFAH_SUM_SWAP_NS] THEN
  REPEAT(MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
  REAL_ARITH_TAC);;

(* The two contractions B and B' of U with Y Y differ by a sign, and B is   *)
(* antisymmetric in (k,k').                                                   *)

let RFAH_BP_NEG = prove
 (`!n (Y:K->num->num->real) (U:num->num->real) k k'.
     (!k a b. Y k a b = --(Y k b a))
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\e.
           U a b * Y k a e * Y k' b e))) =
         --(sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d.
           U a b * Y k a d * Y k' d b))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ya") THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  USE_THEN "ya" (MP_TAC o SPECL [`k':K`; `b:num`; `e:num`]) THEN
  CONV_TAC REAL_RING);;

let RFAH_B_ANTI = prove
 (`!n (Y:K->num->num->real) (U:num->num->real) k k'.
     (!k a b. Y k a b = --(Y k b a)) /\ (!a b. U a b = --(U b a))
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d.
           U a b * Y k' a d * Y k d b))) =
         --(sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d.
           U a b * Y k a d * Y k' d b))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ya") (LABEL_TAC "ua")) THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  USE_THEN "ua" (MP_TAC o SPECL [`b:num`; `a:num`]) THEN
  USE_THEN "ya" (MP_TAC o SPECL [`k':K`; `b:num`; `d:num`]) THEN
  USE_THEN "ya" (MP_TAC o SPECL [`k:K`; `d:num`; `a:num`]) THEN
  CONV_TAC REAL_RING);;

(* The symmetrisation: 2 AA - 2 AA' + 8 BA + 4 BB summed over (k,k') is the  *)
(* sum of the squares (A - A' + 2 B)^2 when B is antisymmetric.             *)

let RFAH_SQ_COMB = prove
 (`!(s:K->bool) (A:K->K->real) (B:K->K->real).
     FINITE s /\ (!k k'. B k' k = --(B k k'))
     ==> &2 * sum s (\k. sum s (\k'. A k k' * A k k')) -
         &2 * sum s (\k. sum s (\k'. A k k' * A k' k)) +
         &8 * sum s (\k. sum s (\k'. B k k' * A k k')) +
         &4 * sum s (\k. sum s (\k'. --(B k k') * --(B k k'))) =
         sum s (\k. sum s (\k'. (A k k' - A k' k + &2 * B k k') pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ba")) THEN
  SUBGOAL_THEN
   `!k k'. ((A:K->K->real) k k' - A k' k + &2 * (B:K->K->real) k k') pow 2 =
           A k k' * A k k' + A k' k * A k' k - &2 * (A k k' * A k' k) +
           &4 * (B k k' * A k k') - &4 * (B k k' * A k' k) +
           &4 * (--(B k k') * --(B k k'))`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL; ASSUME `FINITE (s:K->bool)`] THEN
  SUBGOAL_THEN
   `sum s (\k. sum s (\k'. (A:K->K->real) k' k * A k' k)) =
    sum s (\k. sum s (\k'. A k k' * A k k'))`
   (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`s:K->bool`; `\a:K b:K. (A:K->K->real) a b * A a b`]
      RFAH_DSUM_SWAP) THEN
    REWRITE_TAC[ASSUME `FINITE (s:K->bool)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum s (\k. sum s (\k'. (B:K->K->real) k k' * (A:K->K->real) k' k)) =
    --(sum s (\k. sum s (\k'. B k k' * A k k')))`
   (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`s:K->bool`; `\a:K b:K. (B:K->K->real) b a * (A:K->K->real) a b`]
      RFAH_DSUM_SWAP) THEN
    REWRITE_TAC[ASSUME `FINITE (s:K->bool)`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k':K` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "ba" (MP_TAC o SPECL [`k:K`; `k':K`]) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ABBREV_TAC `a1 = sum s (\k. sum s (\k'. (A:K->K->real) k k' * A k k'))` THEN
  ABBREV_TAC `a2 = sum s (\k. sum s (\k'. (A:K->K->real) k k' * A k' k))` THEN
  ABBREV_TAC `b1 = sum s (\k. sum s (\k'. (B:K->K->real) k k' * (A:K->K->real) k k'))` THEN
  ABBREV_TAC `b2 = sum s (\k. sum s (\k'. --((B:K->K->real) k k') * --(B k k')))` THEN
  REAL_ARITH_TAC);;

(* J for the sum-of-products tensors is a double sum of squares.           *)

let RFAH_HJ_GRAM = prove
 (`!n (s:K->bool) (X:K->num->real) (Y:K->num->num->real)
    (U:num->num->real) (W:num->real).
     FINITE s /\ (!k a b. Y k a b = --(Y k b a)) /\ (!a b. U a b = --(U b a))
     ==> rfa_hj n (\a b c d. sum s (\k. Y k a b * Y k d c))
                  (\a b c. sum s (\k. Y k a b * X k c))
                  (\a b. sum s (\k. X k a * X k b)) U W =
         sum s (\k. sum s (\k'.
           (sum(1..n) (\a. sum(1..n) (\c. W a * Y k a c * X k' c)) -
            sum(1..n) (\a. sum(1..n) (\c. W a * Y k' a c * X k c)) +
            &2 * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d.
                   U a b * Y k a d * Y k' d b)))) pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ya") (LABEL_TAC "ua"))) THEN
  REWRITE_TAC[rfa_hj] THEN
  SIMP_TAC[RFAH_T1; RFAH_T2; RFAH_T3; RFAH_T4; ASSUME `FINITE (s:K->bool)`] THEN
  USE_THEN "ya" (fun th -> REWRITE_TAC[MATCH_MP RFAH_BP_NEG th]) THEN
  MP_TAC(ISPECL [`s:K->bool`;
    `\k:K k':K. sum(1..n) (\a. sum(1..n) (\c.
        (W:num->real) a * (Y:K->num->num->real) k a c * (X:K->num->real) k' c))`;
    `\k:K k':K. sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d.
        (U:num->num->real) a b * (Y:K->num->num->real) k a d * Y k' d b)))`]
    RFAH_SQ_COMB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `FINITE (s:K->bool)`];
      REPEAT GEN_TAC THEN MATCH_MP_TAC RFAH_B_ANTI THEN
      CONJ_TAC THENL [USE_THEN "ya" ACCEPT_TAC; USE_THEN "ua" ACCEPT_TAC]];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let RFAH_HJ_GRAM_POS = prove
 (`!n (s:K->bool) (X:K->num->real) (Y:K->num->num->real)
    (U:num->num->real) (W:num->real).
     FINITE s /\ (!k a b. Y k a b = --(Y k b a)) /\ (!a b. U a b = --(U b a))
     ==> &0 <= rfa_hj n (\a b c d. sum s (\k. Y k a b * Y k d c))
                        (\a b c. sum s (\k. Y k a b * X k c))
                        (\a b. sum s (\k. X k a * X k b)) U W`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:K->bool`; `X:K->num->real`;
                 `Y:K->num->num->real`; `U:num->num->real`; `W:num->real`]
    RFAH_HJ_GRAM) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_POS_LE THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN X_GEN_TAC `k':K` THEN
  DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_LE_POW_2]);;


(* ========================================================================= *)
(* The slot form of Z, the Gram vectors, and the headline.                   *)
(* Slots: (0,c) for W_c and (a,b) for U_ab, in (0..n) CROSS (1..n).          *)
(* ========================================================================= *)

let RFAH_SUM_CROSS_NUMSEG = prove
 (`!(f:num#num->real) m n p q.
     sum ((m..n) CROSS (p..q)) f = sum(m..n) (\i. sum(p..q) (\j. f (i,j)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`m..n`; `\i:num. p..q`; `\i:num j:num. (f:num#num->real) (i,j)`]
    SUM_SUM_PRODUCT) THEN
  REWRITE_TAC[FINITE_NUMSEG; GSYM CROSS; PAIRED_ETA_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let RFAH_SUM_0N = prove
 (`!(f:num->real) n. sum(0..n) f = f 0 + sum(1..n) f`,
  REPEAT GEN_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let RFAH_QF_SPLIT = prove
 (`!(G:num#num->num#num->real) (v:num#num->real) n.
     sum ((0..n) CROSS (1..n)) (\p. sum ((0..n) CROSS (1..n)) (\q.
       G p q * v p * v q)) =
     sum(1..n) (\j. sum(1..n) (\l. G (0,j) (0,l) * v(0,j) * v(0,l))) +
     sum(1..n) (\j. sum(1..n) (\k. sum(1..n) (\l.
       G (0,j) (k,l) * v(0,j) * v(k,l)))) +
     sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\l.
       G (i,j) (0,l) * v(i,j) * v(0,l)))) +
     sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\k. sum(1..n) (\l.
       G (i,j) (k,l) * v(i,j) * v(k,l)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RFAH_SUM_CROSS_NUMSEG] THEN
  REWRITE_TAC[RFAH_SUM_0N] THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[REAL_ADD_ASSOC]);;

let rfah_slot = new_definition
 `rfah_slot (R:num->num->num->num->real) (P:num->num->num->real)
            (M:num->num->real) (p:num#num) (q:num#num) =
    if FST p = 0
    then (if FST q = 0 then M (SND p) (SND q) else P (FST q) (SND q) (SND p))
    else (if FST q = 0 then P (FST p) (SND p) (SND q)
          else R (FST p) (SND p) (SND q) (FST q))`;;

let RFAH_SLOT_EVAL = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    i j k l.
     rfah_slot R P M (0,j) (0,l) = M j l /\
     (~(k = 0) ==> rfah_slot R P M (0,j) (k,l) = P k l j) /\
     (~(i = 0) ==> rfah_slot R P M (i,j) (0,l) = P i j l) /\
     (~(i = 0) /\ ~(k = 0) ==> rfah_slot R P M (i,j) (k,l) = R i j l k)`,
  SIMP_TAC[rfah_slot]);;

let RFAH_SLOT_SYM = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real).
     (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                R a b c d = R c d a b) /\
     (!a b. M a b = M b a)
     ==> !p q. rfah_slot R P M p q = rfah_slot R P M q p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ra") (LABEL_TAC "ms")) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `k:num`; `l:num`] THEN
  REWRITE_TAC[rfah_slot] THEN
  USE_THEN "ms" (MP_TAC o SPECL [`j:num`; `l:num`]) THEN
  USE_THEN "ra" (MP_TAC o SPECL [`k:num`; `l:num`; `j:num`; `i:num`]) THEN
  USE_THEN "ra" (MP_TAC o SPECL [`j:num`; `i:num`; `k:num`; `l:num`]) THEN
  USE_THEN "ra" (MP_TAC o SPECL [`i:num`; `j:num`; `k:num`; `l:num`]) THEN
  REMOVE_THEN "ra" (K ALL_TAC) THEN REMOVE_THEN "ms" (K ALL_TAC) THEN
  ASM_CASES_TAC `i = 0` THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFAH_SLOT_QF_EVAL = prove
 (`!n (R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (v:num#num->real).
     sum ((0..n) CROSS (1..n)) (\p. sum ((0..n) CROSS (1..n)) (\q.
       rfah_slot R P M p q * v p * v q)) =
     sum(1..n) (\j. sum(1..n) (\l. M j l * v(0,j) * v(0,l))) +
     sum(1..n) (\j. sum(1..n) (\k. sum(1..n) (\l.
       P k l j * v(0,j) * v(k,l)))) +
     sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\l.
       P i j l * v(i,j) * v(0,l)))) +
     sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\k. sum(1..n) (\l.
       R i j l k * v(i,j) * v(k,l)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RFAH_QF_SPLIT; RFAH_SLOT_EVAL] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    ASM_SIMP_TAC[RFAH_SLOT_EVAL; ARITH_RULE `1 <= k ==> ~(k = 0)`];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    ASM_SIMP_TAC[RFAH_SLOT_EVAL; ARITH_RULE `1 <= i ==> ~(i = 0)`];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  ASM_SIMP_TAC[RFAH_SLOT_EVAL; ARITH_RULE `1 <= i ==> ~(i = 0)`;
               ARITH_RULE `1 <= k ==> ~(k = 0)`]);;

(* Antisymmetric tensors see only the antisymmetric part of U.              *)

let RFAH_ANTI_P = prove
 (`!(P:num->num->num->real).
     (!a b c. P a b c = --(P b a c))
     ==> !n (v:num#num->real).
           sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
             P a b c * (v(a,b) - v(b,a)) / &2 * v(0,c)))) =
           sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
             P a b c * v(a,b) * v(0,c))))`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "pa") THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
      (P:num->num->num->real) a b c * (v:num#num->real)(b,a) * v(0,c)))) =
    --(sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
      P a b c * v(a,b) * v(0,c)))))`
   (LABEL_TAC "s2") THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    USE_THEN "pa" (MP_TAC o SPECL [`b:num`; `a:num`; `c:num`]) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
      (P:num->num->num->real) a b c * ((v:num#num->real)(a,b) - v(b,a)) / &2 *
      v(0,c)))) =
    inv(&2) * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
      P a b c * v(a,b) * v(0,c)))) -
    inv(&2) * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
      P a b c * v(b,a) * v(0,c))))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "s2" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let RFAH_ANTI_R = prove
 (`!(R:num->num->num->num->real).
     (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                R a b c d = R c d a b)
     ==> !n (v:num#num->real).
           sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
             R a b c d * (v(a,b) - v(b,a)) / &2 * (v(d,c) - v(c,d)) / &2)))) =
           sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
             R a b c d * v(a,b) * v(d,c)))))`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "ra") THEN REPEAT GEN_TAC THEN
  ABBREV_TAC `s11 = sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
             (R:num->num->num->num->real) a b c d * (v:num#num->real)(a,b) *
             v(d,c)))))` THEN
  SUBGOAL_THEN
   `sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
      (R:num->num->num->num->real) a b c d *
      ((v:num#num->real)(a,b) - v(b,a)) / &2 * (v(d,c) - v(c,d)) / &2)))) =
    ((inv(&4) * s11 -
      inv(&4) * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
        R a b c d * v(a,b) * v(c,d)))))) -
     inv(&4) * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
        R a b c d * v(b,a) * v(d,c)))))) +
    inv(&4) * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
        R a b c d * v(b,a) * v(c,d)))))`
   SUBST1_TAC THENL
   [EXPAND_TAC "s11" THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
      (R:num->num->num->num->real) a b c d * (v:num#num->real)(a,b) *
      v(c,d))))) = --s11`
   (LABEL_TAC "s12") THENL
   [EXPAND_TAC "s11" THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    USE_THEN "ra" (MP_TAC o SPECL [`a:num`; `b:num`; `d:num`; `c:num`]) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
      (R:num->num->num->num->real) a b c d * (v:num#num->real)(b,a) *
      v(d,c))))) = --s11`
   (LABEL_TAC "s21") THENL
   [EXPAND_TAC "s11" THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    USE_THEN "ra" (MP_TAC o SPECL [`b:num`; `a:num`; `c:num`; `d:num`]) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
      (R:num->num->num->num->real) a b c d * (v:num#num->real)(b,a) *
      v(c,d))))) = s11`
   (LABEL_TAC "s22") THENL
   [EXPAND_TAC "s11" THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    USE_THEN "ra" (MP_TAC o SPECL [`b:num`; `a:num`; `d:num`; `c:num`]) THEN
    USE_THEN "ra" (MP_TAC o SPECL [`a:num`; `b:num`; `d:num`; `c:num`]) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  USE_THEN "s12" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s21" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s22" (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

(* The quadratic form of the slot array is Z at the antisymmetric part.     *)

let RFAH_SLOT_QF = prove
 (`!n (R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (v:num#num->real).
     (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                R a b c d = R c d a b) /\
     (!a b c. P a b c = --(P b a c))
     ==> sum ((0..n) CROSS (1..n)) (\p. sum ((0..n) CROSS (1..n)) (\q.
           rfah_slot R P M p q * v p * v q)) =
         rfa_hz n R P M (\a b. (v(a,b) - v(b,a)) / &2) (\c. v(0,c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ra") (LABEL_TAC "pa")) THEN
  REWRITE_TAC[RFAH_SLOT_QF_EVAL; rfa_hz] THEN
  USE_THEN "pa" (fun th -> REWRITE_TAC[MATCH_MP RFAH_ANTI_P th]) THEN
  USE_THEN "ra" (fun th -> REWRITE_TAC[MATCH_MP RFAH_ANTI_R th]) THEN
  SUBGOAL_THEN
   `sum(1..n) (\j. sum(1..n) (\k. sum(1..n) (\l.
      (P:num->num->num->real) k l j * (v:num#num->real)(0,j) * v(k,l)))) =
    sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. P a b c * v(a,b) * v(0,c))))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\k. sum(1..n) (\l.
      (R:num->num->num->num->real) i j l k * (v:num#num->real)(i,j) * v(k,l))))) =
    sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
      R a b c d * v(a,b) * v(d,c)))))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN
    BETA_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `mm = sum(1..n) (\a. sum(1..n) (\b.
                     (M:num->num->real) a b * (v:num#num->real)(0,a) * v(0,b)))` THEN
  ABBREV_TAC `pp = sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
                     (P:num->num->num->real) a b c * (v:num#num->real)(a,b) * v(0,c))))` THEN
  ABBREV_TAC `rr = sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
                     (R:num->num->num->num->real) a b c d * (v:num#num->real)(a,b) *
                     v(d,c)))))` THEN
  REAL_ARITH_TAC);;

let RFAH_SLOT_PSD = prove
 (`!n (R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real).
     (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                R a b c d = R c d a b) /\
     (!a b c. P a b c = --(P b a c)) /\
     (!(U:num->num->real) (W:num->real).
        (!a b. U a b = --(U b a)) ==> &0 <= rfa_hz n R P M U W)
     ==> !v:num#num->real.
           &0 <= sum ((0..n) CROSS (1..n)) (\p. sum ((0..n) CROSS (1..n)) (\q.
                   rfah_slot R P M p q * v p * v q))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ra")
    (CONJUNCTS_THEN2 (LABEL_TAC "pa") (LABEL_TAC "zpos"))) THEN
  X_GEN_TAC `v:num#num->real` THEN
  MP_TAC(ISPECL [`n:num`; `R:num->num->num->num->real`; `P:num->num->num->real`;
                 `M:num->num->real`; `v:num#num->real`] RFAH_SLOT_QF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "ra" ACCEPT_TAC; USE_THEN "pa" ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "zpos" MATCH_MP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Reading off R, P, M from a Gram decomposition of the slot array.         *)

let RFAH_IN_SLOTS = prove
 (`!n a b. a IN 1..n /\ b IN 1..n
           ==> (a,b) IN (0..n) CROSS (1..n) /\ (0,b) IN (0..n) CROSS (1..n) /\
               ~(a = 0)`,
  REWRITE_TAC[IN_CROSS; IN_NUMSEG] THEN ARITH_TAC);;

let RFAH_REPR_R = prove
 (`!(S:num#num->bool) (L:num#num->num#num->real) (G:num#num->num#num->real)
    (R:num->num->num->num->real) a b c d.
     FINITE S /\ (a,b) IN S /\ (b,a) IN S /\ (c,d) IN S /\ (d,c) IN S /\
     (!p q. p IN S /\ q IN S ==> sum S (\k. L k p * L k q) = G p q) /\
     G (a,b) (d,c) = R a b c d /\ G (a,b) (c,d) = R a b d c /\
     G (b,a) (d,c) = R b a c d /\ G (b,a) (c,d) = R b a d c /\
     R a b d c = --(R a b c d) /\ R b a c d = --(R a b c d) /\
     R b a d c = R a b c d
     ==> R a b c d =
         sum S (\k. (L k (a,b) - L k (b,a)) / &2 * (L k (d,c) - L k (c,d)) / &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum S (\k. ((L:num#num->num#num->real) k (a,b) - L k (b,a)) / &2 *
               (L k (d,c) - L k (c,d)) / &2) =
    inv(&4) * (((sum S (\k. L k (a,b) * L k (d,c)) -
                 sum S (\k. L k (a,b) * L k (c,d))) -
                sum S (\k. L k (b,a) * L k (d,c))) +
               sum S (\k. L k (b,a) * L k (c,d)))`
   SUBST1_TAC THENL
   [SIMP_TAC[GSYM SUM_SUB; GSYM SUM_ADD; ASSUME `FINITE (S:num#num->bool)`] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

let RFAH_REPR_P = prove
 (`!(S:num#num->bool) (L:num#num->num#num->real) (G:num#num->num#num->real)
    (P:num->num->num->real) a b c.
     FINITE S /\ (a,b) IN S /\ (b,a) IN S /\ (0,c) IN S /\
     (!p q. p IN S /\ q IN S ==> sum S (\k. L k p * L k q) = G p q) /\
     G (a,b) (0,c) = P a b c /\ G (b,a) (0,c) = P b a c /\
     P b a c = --(P a b c)
     ==> P a b c = sum S (\k. (L k (a,b) - L k (b,a)) / &2 * L k (0,c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum S (\k. ((L:num#num->num#num->real) k (a,b) - L k (b,a)) / &2 *
               L k (0,c)) =
    inv(&2) * (sum S (\k. L k (a,b) * L k (0,c)) -
               sum S (\k. L k (b,a) * L k (0,c)))`
   SUBST1_TAC THENL
   [SIMP_TAC[GSYM SUM_SUB; ASSUME `FINITE (S:num#num->bool)`] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

let RFAH_SLOT_REPR = prove
 (`!n (R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real).
     (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                R a b c d = R c d a b) /\
     (!a b c. P a b c = --(P b a c)) /\
     (!a b. M a b = M b a) /\
     (!(U:num->num->real) (W:num->real).
        (!a b. U a b = --(U b a)) ==> &0 <= rfa_hz n R P M U W)
     ==> ?(X:num#num->num->real) (Y:num#num->num->num->real).
           (!k a b. Y k a b = --(Y k b a)) /\
           (!a b c d. a IN 1..n /\ b IN 1..n /\ c IN 1..n /\ d IN 1..n
                      ==> R a b c d =
                          sum ((0..n) CROSS (1..n)) (\k. Y k a b * Y k d c)) /\
           (!a b c. a IN 1..n /\ b IN 1..n /\ c IN 1..n
                    ==> P a b c =
                        sum ((0..n) CROSS (1..n)) (\k. Y k a b * X k c)) /\
           (!a b. a IN 1..n /\ b IN 1..n
                  ==> M a b = sum ((0..n) CROSS (1..n)) (\k. X k a * X k b))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ra") (CONJUNCTS_THEN2 (LABEL_TAC "pa")
    (CONJUNCTS_THEN2 (LABEL_TAC "ms") (LABEL_TAC "zpos")))) THEN
  SUBGOAL_THEN `FINITE ((0..n) CROSS (1..n))` ASSUME_TAC THENL
   [SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG]; ALL_TAC] THEN
  MP_TAC(ISPEC `(0..n) CROSS (1..n)` RFAH_GRAM) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rfah_slot (R:num->num->num->num->real)
                              (P:num->num->num->real) (M:num->num->real)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                     `M:num->num->real`] RFAH_SLOT_SYM) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "ra" ACCEPT_TAC; USE_THEN "ms" ACCEPT_TAC];
        DISCH_THEN MATCH_ACCEPT_TAC];
      MATCH_MP_TAC RFAH_SLOT_PSD THEN REPEAT CONJ_TAC THENL
       [USE_THEN "ra" ACCEPT_TAC; USE_THEN "pa" ACCEPT_TAC;
        USE_THEN "zpos" ACCEPT_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:num#num->num#num->real` (LABEL_TAC "gram")) THEN
  SUBGOAL_THEN
   `!p q. p IN (0..n) CROSS (1..n) /\ q IN (0..n) CROSS (1..n)
          ==> sum ((0..n) CROSS (1..n)) (\k. (L:num#num->num#num->real) k p * L k q) =
              rfah_slot (R:num->num->num->num->real) (P:num->num->num->real)
                        (M:num->num->real) p q`
   (LABEL_TAC "gram'") THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "gram" MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\k:num#num a:num. (L:num#num->num#num->real) k (0,a)` THEN
  EXISTS_TAC `\k:num#num a:num b:num.
                ((L:num#num->num#num->real) k (a,b) - L k (b,a)) / &2` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`; `d:num`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(R:num->num->num->num->real) a b d c = --(R a b c d) /\
      R b a c d = --(R a b c d) /\ R b a d c = R a b c d`
     STRIP_ASSUME_TAC THENL
     [USE_THEN "ra" (MP_TAC o SPECL [`a:num`; `b:num`; `c:num`; `d:num`]) THEN
      USE_THEN "ra" (MP_TAC o SPECL [`b:num`; `a:num`; `d:num`; `c:num`]) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "ra" (K ALL_TAC) THEN REMOVE_THEN "pa" (K ALL_TAC) THEN
    REMOVE_THEN "ms" (K ALL_TAC) THEN REMOVE_THEN "zpos" (K ALL_TAC) THEN
    REMOVE_THEN "gram" (K ALL_TAC) THEN
    MATCH_MP_TAC RFAH_REPR_R THEN
    EXISTS_TAC `rfah_slot (R:num->num->num->num->real)
                          (P:num->num->num->real) (M:num->num->real)` THEN
    ASM_SIMP_TAC[IN_CROSS; IN_NUMSEG; LE_0; RFAH_SLOT_EVAL;
                 ARITH_RULE `1 <= a ==> ~(a = 0)`];
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    USE_THEN "pa" (MP_TAC o SPECL [`b:num`; `a:num`; `c:num`]) THEN
    DISCH_TAC THEN
    REMOVE_THEN "ra" (K ALL_TAC) THEN REMOVE_THEN "pa" (K ALL_TAC) THEN
    REMOVE_THEN "ms" (K ALL_TAC) THEN REMOVE_THEN "zpos" (K ALL_TAC) THEN
    REMOVE_THEN "gram" (K ALL_TAC) THEN
    MATCH_MP_TAC RFAH_REPR_P THEN
    EXISTS_TAC `rfah_slot (R:num->num->num->num->real)
                          (P:num->num->num->real) (M:num->num->real)` THEN
    ASM_SIMP_TAC[IN_CROSS; IN_NUMSEG; LE_0; RFAH_SLOT_EVAL;
                 ARITH_RULE `1 <= a ==> ~(a = 0)`];
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REMOVE_THEN "ra" (K ALL_TAC) THEN REMOVE_THEN "pa" (K ALL_TAC) THEN
    REMOVE_THEN "ms" (K ALL_TAC) THEN REMOVE_THEN "zpos" (K ALL_TAC) THEN
    REMOVE_THEN "gram" (K ALL_TAC) THEN
    USE_THEN "gram'" (MP_TAC o SPECL [`(0,a:num)`; `(0,b:num)`]) THEN
    ASM_SIMP_TAC[IN_CROSS; IN_NUMSEG; LE_0; RFAH_SLOT_EVAL]]);;

(* rfa_hj depends only on the values of R, P, M at indices in 1..n.         *)

let RFAH_HJ_CONG = prove
 (`!n (R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (R':num->num->num->num->real) (P':num->num->num->real) (M':num->num->real)
    (U:num->num->real) (W:num->real).
     (!a b c d. a IN 1..n /\ b IN 1..n /\ c IN 1..n /\ d IN 1..n
                ==> R a b c d = R' a b c d) /\
     (!a b c. a IN 1..n /\ b IN 1..n /\ c IN 1..n ==> P a b c = P' a b c) /\
     (!a b. a IN 1..n /\ b IN 1..n ==> M a b = M' a b)
     ==> rfa_hj n R P M U W = rfa_hj n R' P' M' U W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfa_hj] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = a' /\ b = b' /\ c = c' /\ d = d'
    ==> &2 * a - &2 * b + &8 * c + &4 * d =
        &2 * a' - &2 * b' + &8 * c' + &4 * d'`) THEN
  REPEAT CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
  ASM_SIMP_TAC[]);;

(* The algebraic lemma for every n, and the statement                       *)
(* RFA_HARNACK_ALG_STATEMENT.                                               *)

let RFAH_HARNACK_ALG_N = prove
 (`!n (R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real).
       (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                  R a b c d = R c d a b) /\
       (!a b c. P a b c = --(P b a c)) /\
       (!a b. M a b = M b a) /\
       (!(U:num->num->real) (W:num->real).
          (!a b. U a b = --(U b a)) ==> &0 <= rfa_hz n R P M U W)
       ==> !(U:num->num->real) (W:num->real).
             (!a b. U a b = --(U b a)) ==> &0 <= rfa_hj n R P M U W`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFAH_SLOT_REPR) THEN
  DISCH_THEN(X_CHOOSE_THEN `X:num#num->num->real`
    (X_CHOOSE_THEN `Y:num#num->num->num->real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`U:num->num->real`; `W:num->real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`n:num`; `R:num->num->num->num->real`; `P:num->num->num->real`;
    `M:num->num->real`;
    `\a b c d. sum ((0..n) CROSS (1..n))
                 (\k. (Y:num#num->num->num->real) k a b * Y k d c)`;
    `\a b c. sum ((0..n) CROSS (1..n))
               (\k. (Y:num#num->num->num->real) k a b * (X:num#num->num->real) k c)`;
    `\a b. sum ((0..n) CROSS (1..n))
             (\k. (X:num#num->num->real) k a * X k b)`;
    `U:num->num->real`; `W:num->real`] RFAH_HJ_CONG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RFAH_HJ_GRAM_POS THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let RFA_HARNACK_ALG = prove
 (`!u:N->bool. RFA_HARNACK_ALG_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[RFA_HARNACK_ALG_STATEMENT] THEN
  MATCH_ACCEPT_TAC(SPEC `dimindex(:N)` RFAH_HARNACK_ALG_N));;

