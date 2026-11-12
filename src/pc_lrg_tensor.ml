(* ========================================================================= *)
(* Tensor calculus on open subsets of real^N: covariant derivatives, norms,  *)
(* pullbacks; chart independence of |nabla^l Rm| and of the C^k distance;    *)
(* the second Bianchi identity.  Builds on pc_lrg.                           *)
(* ========================================================================= *)

needs "src/pc_lrg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Definitions: tensor calculus on open subsets of real^N.                   *)
(* A (0,k)-tensor field is T : real^N -> (num->real^N) -> real, multilinear *)
(* in the slots 1..k of its tuple argument.  The covariant derivative puts   *)
(* the derivative direction in slot k+1 (MT: R_ijkl,h = (nabla_h R)_ijkl).   *)
(* ========================================================================= *)

(* Index tuples of length k with entries in 1..N (0 outside 1..k). *)

let index_tuples = new_definition
 `index_tuples k (s:N->bool) =
    {i:num->num | (!m. 1 <= m /\ m <= k ==> 1 <= i m /\ i m <= dimindex s) /\
                  (!m. ~(1 <= m /\ m <= k) ==> i m = 0)}`;;

(* Covariant derivative of a (0,k)-tensor field. *)

let lnabla = new_definition
 `lnabla k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u =
    drop(frechet_derivative (\z. lift(tf z u)) (at y) (u(k + 1))) -
    sum(1..k) (\i. tf y (\j. if j = i then christoffel G y (u(k + 1)) (u i)
                             else u j))`;;

let lnabla_iter = define
 `(lnabla_iter k 0 (G:real^N->real^N^N) tf = tf) /\
  (lnabla_iter k (SUC l) G tf = lnabla (k + l) G (lnabla_iter k l G tf))`;;

(* Squared norm of a (0,k)-tensor at y: full contraction with G(y)^-1. *)

let ltnorm2 = new_definition
 `ltnorm2 k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y =
    sum (index_tuples k (:N))
     (\i. sum (index_tuples k (:N))
           (\j. tf y (\m. basis(i m)) * tf y (\m. basis(j m)) *
                product(1..k) (\m. matrix_inv(G y)$(i m)$(j m))))`;;

(* The metric and the curvature as tensor fields:                          *)
(* R(u1,u2,u3,u4) = g(R(u1,u2)u4, u3) (MT p. 6).                             *)

let lmetric2 = new_definition
 `lmetric2 (G:real^N->real^N^N) y (u:num->real^N) = u 1 dot (G y ** u 2)`;;

let lrm4 = new_definition
 `lrm4 (G:real^N->real^N^N) y (u:num->real^N) =
    u 3 dot (G y ** lriemann G y (u 1) (u 2) (u 4))`;;

(* |nabla^l Rm|^2 and the squared C^k distance of G from G0 (MT Def 2.16). *)

let lrm_deriv_norm2 = new_definition
 `lrm_deriv_norm2 l (G:real^N->real^N^N) y =
    ltnorm2 (4 + l) G (lnabla_iter 4 l G (lrm4 G)) y`;;

let lck_dist2 = new_definition
 `lck_dist2 k (G0:real^N->real^N^N) (G:real^N->real^N^N) y =
    sum(0..k) (\l. ltnorm2 (2 + l) G0
                     (lnabla_iter 2 l G0 (\z u. lmetric2 G z u - lmetric2 G0 z u)) y)`;;

(* Tensor fields and pullbacks. *)

let ltensor_field = new_definition
 `ltensor_field k (U:real^N->bool) (tf:real^N->(num->real^N)->real) <=>
    !y. y IN U
        ==> (!u u'. (!m. 1 <= m /\ m <= k ==> u m = u' m) ==> tf y u = tf y u') /\
            (!i u. 1 <= i /\ i <= k
                   ==> linear (\v. lift(tf y (\j. if j = i then v else u j))))`;;

(* Pullback of a (0,k)-tensor field by a map h. *)

let ltpullback = new_definition
 `ltpullback (h:real^N->real^N) (tf:real^N->(num->real^N)->real) =
    \y u. tf (h y) (\m. frechet_derivative h (at y) (u m))`;;


(* ========================================================================= *)
(* Index tuples: finiteness, decomposition of sums over tuples of length k + *)
(* 1, products of sums.                                                      *)
(* ========================================================================= *)

let LRG_INDEX_TUPLES_FINITE = prove
 (`!k. FINITE(index_tuples k (:N))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{f:num->num | IMAGE f (1..k) SUBSET (1..dimindex(:N)) /\
                  {x | ~(f x = (\x:num. 0) x)} SUBSET (1..k)}` THEN
  SIMP_TAC[FINITE_RESTRICTED_FUNSPACE; FINITE_NUMSEG] THEN
  REWRITE_TAC[index_tuples; SUBSET; IN_ELIM_THM; FORALL_IN_IMAGE; IN_NUMSEG] THEN
  MESON_TAC[]);;

let LRG_INDEX_TUPLES_0 = prove
 (`index_tuples 0 (:N) = {(\m:num. 0)}`,
  REWRITE_TAC[EXTENSION; IN_SING] THEN GEN_TAC THEN
  REWRITE_TAC[index_tuples; IN_ELIM_THM; FUN_EQ_THM] THEN
  REWRITE_TAC[ARITH_RULE `!m. ~(1 <= m /\ m <= 0)`]);;

let LRG_INDEX_TUPLES_SUC = prove
 (`!k. index_tuples (k + 1) (:N) =
       IMAGE (\(i,q). (\m. if m = k + 1 then q else i m))
             {i,q | i IN index_tuples k (:N) /\ q IN 1..dimindex(:N)}`,
  GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  X_GEN_TAC `j:num->num` THEN
  REWRITE_TAC[index_tuples; IN_ELIM_THM; IN_NUMSEG] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`\m. if m = k + 1 then 0 else (j:num->num) m`; `(j:num->num)(k + 1)`] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[ARITH_RULE `1 <= k + 1 /\ k + 1 <= k + 1`];
      ASM_MESON_TAC[ARITH_RULE `1 <= k + 1 /\ k + 1 <= k + 1`]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num->num`; `q:num`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `m:num` THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC]);;

let LRG_PRODUCT_NUMSEG_ADD1 = prove
 (`!f k. product (1..k + 1) f = product (1..k) f * f (k + 1)`,
  REWRITE_TAC[GSYM ADD1; PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`]);;

let LRG_SUM_NUMSEG_ADD1 = prove
 (`!f k. sum (1..k + 1) f = sum (1..k) f + f (k + 1)`,
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`]);;

let LRG_SUM_INDEX_TUPLES_0 = prove
 (`!f. sum (index_tuples 0 (:N)) f = f (\m. 0)`,
  REWRITE_TAC[LRG_INDEX_TUPLES_0; SUM_SING]);;

let LRG_SUM_INDEX_TUPLES_SUC = prove
 (`!f k. sum (index_tuples (k + 1) (:N)) f =
         sum (index_tuples k (:N))
             (\i. sum (1..dimindex(:N))
                      (\q. f (\m. if m = k + 1 then q else i m)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LRG_INDEX_TUPLES_SUC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {i,q | i IN index_tuples k (:N) /\ q IN 1..dimindex(:N)}
        (f o (\(i,q). (\m. if m = k + 1 then q else (i:num->num) m)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_IMAGE THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num->num`; `q:num`; `i':num->num`; `q':num`] THEN
    REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(i:num->num)(k + 1) = 0 /\ (i':num->num)(k + 1) = 0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ARITH_TAC);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = k + 1` THENL
       [ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN REWRITE_TAC[]];
    SIMP_TAC[SUM_SUM_PRODUCT; LRG_INDEX_TUPLES_FINITE; FINITE_NUMSEG] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]]);;

let LRG_PRODUCT_SUM_TUPLES = prove
 (`!(f:num->num->real) k.
        product (1..k) (\m. sum (1..dimindex(:N)) (f m)) =
        sum (index_tuples k (:N)) (\i. product (1..k) (\m. f m (i m)))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LRG_SUM_INDEX_TUPLES_0; PRODUCT_CLAUSES_NUMSEG; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1; LRG_PRODUCT_NUMSEG_ADD1; LRG_SUM_INDEX_TUPLES_SUC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* Multilinear algebra: expansion in a single slot, expansion of a           *)
(* multilinear form over index tuples.                                       *)
(* ========================================================================= *)

let LRG_SLOT_EXPAND = prove
 (`!(tp:(num->real^N)->real) i u v.
        linear (\v. lift(tp (\j. if j = i then v else u j)))
        ==> tp (\j. if j = i then v else u j) =
            sum (1..dimindex(:N))
                (\q. v$q * tp (\j. if j = i then basis q else u j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^N` o MATCH_MP LRG_LINEAR_DROP_EXPAND) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

let LRG_MULTILINEAR_EXPAND = prove
 (`!(tp:(num->real^N)->real) k.
        (!u u'. (!m. 1 <= m /\ m <= k ==> u m = u' m) ==> tp u = tp u') /\
        (!i u. 1 <= i /\ i <= k
               ==> linear (\v. lift(tp (\j. if j = i then v else u j))))
        ==> !w. tp w = sum (index_tuples k (:N))
                          (\i. product (1..k) (\m. (w m)$(i m)) *
                               tp (\m. basis (i m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. r <= k
        ==> !w. (tp:(num->real^N)->real) w =
                sum (index_tuples r (:N))
                    (\i. product (1..r) (\m. (w m)$(i m)) *
                         tp (\m. if 1 <= m /\ m <= r then basis (i m) else w m))`
  (MP_TAC o SPEC `k:num`) THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN GEN_TAC THEN
      REWRITE_TAC[LRG_SUM_INDEX_TUPLES_0; PRODUCT_CLAUSES_NUMSEG; ARITH;
                  REAL_MUL_LID; ARITH_RULE `~(1 <= m /\ m <= 0)`; ETA_AX];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `w:num->real^N` THEN
    SUBGOAL_THEN `(r:num) <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:num->real^N` o
      C MATCH_MP (ASSUME `(r:num) <= k`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD1; LRG_SUM_INDEX_TUPLES_SUC] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[LRG_PRODUCT_NUMSEG_ADD1] THEN
    SUBGOAL_THEN
     `!p. product (1..r) (\m. (w m:real^N)$(if m = r + 1 then p else i m)) =
          product (1..r) (\m. w m$(i m))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN
      STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`tp:(num->real^N)->real`; `r + 1`;
                   `\m. if 1 <= m /\ m <= r then basis ((i:num->num) m)
                        else (w:num->real^N) m`;
                   `(w:num->real^N) (r + 1)`] LRG_SLOT_EXPAND) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `(a:real) = a' /\ (b:real) = b' ==> a = b ==> a' = b'`) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
      ASM_CASES_TAC `j = r + 1` THEN ASM_REWRITE_TAC[] THENL
       [REWRITE_TAC[ARITH_RULE `1 <= r + 1 /\ r + 1 <= r + 1`]; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(j = r + 1)
                               ==> (1 <= j /\ j <= r + 1 <=> 1 <= j /\ j <= r)`]];
    ALL_TAC] THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN X_GEN_TAC `w:num->real^N` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SPEC `w:num->real^N`) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC[]);;

(* ========================================================================= *)
(* Norms of tensors.  With matrix_inv(G y) = (transp S) S the squared norm   *)
(* is a sum of squares of components in the frame transp S; positivity,      *)
(* vanishing, invariance under pullback.                                     *)
(* ========================================================================= *)

let LRG_SUM_SQUARE_EXPAND = prove
 (`!(a:B->A->real) x s t.
        FINITE s /\ FINITE t
        ==> sum t (\p. (sum s (\i. a p i * x i)) pow 2) =
            sum s (\i. sum s (\j. x i * x j * sum t (\p. a p i * a p j)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_SWAP (CONJ (ASSUME `FINITE(t:B->bool)`)
                            (ASSUME `FINITE(s:A->bool)`))] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_SWAP (CONJ (ASSUME `FINITE(t:B->bool)`)
                            (ASSUME `FINITE(s:A->bool)`))] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:B` THEN DISCH_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let LRG_TRANSP_MUL_COMPONENT = prove
 (`!(S:real^N^N) a b.
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> (transp S ** S)$a$b =
            sum (1..dimindex(:N)) (\q. S$q$a * S$q$b)`,
  SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT]);;

let LRG_TRANSP_BASIS_COMPONENT = prove
 (`!(S:real^N^N) q a.
        1 <= q /\ q <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N)
        ==> (transp S ** basis q)$a = S$q$a`,
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DOT_BASIS] THEN
  SIMP_TAC[transp; LAMBDA_BETA]);;

let LRG_INDEX_TUPLES_RANGE = prove
 (`!i k m. i IN index_tuples k (:N) /\ 1 <= m /\ m <= k
           ==> 1 <= i m /\ i m <= dimindex(:N)`,
  SIMP_TAC[index_tuples; IN_ELIM_THM]);;

let LRG_TENSOR_FIELD_EXPAND = prove
 (`!k U (tf:real^N->(num->real^N)->real) y.
        ltensor_field k U tf /\ y IN U
        ==> !w. tf y w = sum (index_tuples k (:N))
                             (\i. product (1..k) (\m. (w m)$(i m)) *
                                  tf y (\m. basis (i m)))`,
  REWRITE_TAC[ltensor_field] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `y:real^N`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LRG_MULTILINEAR_EXPAND THEN ASM_REWRITE_TAC[]);;

let LRG_PRODUCT_TRANSP_MUL = prove
 (`!(S:real^N^N) k i j.
        i IN index_tuples k (:N) /\ j IN index_tuples k (:N)
        ==> product (1..k) (\m. (transp S ** S)$(i m)$(j m)) =
            sum (index_tuples k (:N))
                (\p. product (1..k) (\m. S$(p m)$(i m)) *
                     product (1..k) (\m. S$(p m)$(j m)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product (1..k) (\m. sum (1..dimindex(:N))
                 (\q. (S:real^N^N)$q$((i:num->num) m) * S$q$((j:num->num) m)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC LRG_TRANSP_MUL_COMPONENT THEN
    MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LRG_PRODUCT_SUM_TUPLES] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[GSYM PRODUCT_MUL_NUMSEG]);;

let LRG_LTNORM2_SQUARES = prove
 (`!k U (G:real^N->real^N^N) tf y (S:real^N^N).
        ltensor_field k U tf /\ y IN U /\ matrix_inv(G y) = transp S ** S
        ==> ltnorm2 k G tf y =
            sum (index_tuples k (:N))
                (\p. (tf y (\m. transp S ** basis(p m))) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. p IN index_tuples k (:N)
        ==> (tf:real^N->(num->real^N)->real) y (\m. transp S ** basis(p m)) =
            sum (index_tuples k (:N))
                (\i. product (1..k) (\m. (S:real^N^N)$(p m)$(i m)) *
                     tf y (\m. basis(i m)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                   `y:real^N`] LRG_TENSOR_FIELD_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC LRG_TRANSP_BASIS_COMPONENT THEN
    MP_TAC(ISPECL [`p:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (index_tuples k (:N))
     (\p. (sum (index_tuples k (:N))
             (\i. product (1..k) (\m. (S:real^N^N)$(p m)$(i m)) *
                  (tf:real^N->(num->real^N)->real) y (\m. basis(i m)))) pow 2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SIMP_TAC[LRG_SUM_SQUARE_EXPAND; LRG_INDEX_TUPLES_FINITE] THEN
  REWRITE_TAC[ltnorm2] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_PRODUCT_TRANSP_MUL THEN ASM_REWRITE_TAC[]);;

let LRG_METRIC_INV_POSDEF = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U ==> positive_definite(matrix_inv(G y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_INV_TRANSP] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(matrix_inv((G:real^N->real^N^N) y) ** x = vec 0)` ASSUME_TAC
  THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(x:real^N = vec 0)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `x = (G:real^N->real^N^N) y ** matrix_inv(G y) ** x`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `matrix_inv((G:real^N->real^N^N) y) ** x`] LRG_METRIC_POS) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_SYM]);;

let LRG_METRIC_INV_FACTOR = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> ?S:real^N^N. invertible S /\ matrix_inv(G y) = transp S ** S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP LRG_METRIC_INV_POSDEF
    (CONJ (ASSUME `metric_field U (G:real^N->real^N^N)`)
          (ASSUME `(y:real^N) IN U`))) THEN
  REWRITE_TAC[POSITIVE_DEFINITE_COVARIANCE_EQ] THEN MESON_TAC[]);;

let LTNORM2_POS = prove
 (`!k U (G:real^N->real^N^N) tf y.
        metric_field U G /\ ltensor_field k U tf /\ y IN U
        ==> &0 <= ltnorm2 k G tf y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2]);;

let LRG_MULTILINEAR_TRANSFORM = prove
 (`!(tp:(num->real^N)->real) k (A:real^N^N).
        (!u u'. (!m. 1 <= m /\ m <= k ==> u m = u' m) ==> tp u = tp u') /\
        (!i u. 1 <= i /\ i <= k
               ==> linear (\v. lift(tp (\j. if j = i then v else u j))))
        ==> (!u u'. (!m. 1 <= m /\ m <= k ==> u m = u' m)
                    ==> tp (\m. A ** u m) = tp (\m. A ** u' m)) /\
            (!i u. 1 <= i /\ i <= k
                   ==> linear (\v. lift(tp (\m. A ** (if m = i then v else u m)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\v. lift((tp:(num->real^N)->real)
                  (\m. (A:real^N^N) ** (if m = i then v else (u:num->real^N) m)))) =
      (\v. (\w. lift(tp (\j. if j = i then w else (\j. A ** u j) j)))
           ((\v. A ** v) v))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `\j. (A:real^N^N) ** (u:num->real^N) j`]) THEN
    ASM_REWRITE_TAC[]]);;

let LTNORM2_EQ_0 = prove
 (`!k U (G:real^N->real^N^N) tf y.
        metric_field U G /\ ltensor_field k U tf /\ y IN U
        ==> (ltnorm2 k G tf y = &0 <=> !u. tf y u = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; SUM_0]] THEN
  SUBGOAL_THEN
   `!p. p IN index_tuples k (:N)
        ==> (tf:real^N->(num->real^N)->real) y
              (\m. transp (S:real^N^N) ** basis(p m)) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\p. ((tf:real^N->(num->real^N)->real) y
              (\m. transp (S:real^N^N) ** basis(p m))) pow 2`;
      `index_tuples k (:N)`] SUM_POS_EQ_0) THEN
    ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE; REAL_LE_POW_2; REAL_POW_EQ_0;
                    ARITH_EQ];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->real^N` THEN
  SUBGOAL_THEN
   `(tf:real^N->(num->real^N)->real) y u =
    tf y (\m. transp (S:real^N^N) ** (matrix_inv(transp S) ** u m))`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; INVERTIBLE_TRANSP;
                 MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (tf:real^N->(num->real^N)->real) y
                        (\m. transp (S:real^N^N) ** x m)`; `k:num`]
         LRG_MULTILINEAR_EXPAND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN MATCH_MP_TAC LRG_MULTILINEAR_TRANSFORM THEN
    UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\m. matrix_inv(transp(S:real^N^N)) ** (u:num->real^N) m`) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO]);;

let LRG_LTPULLBACK_TENSOR_FIELD = prove
 (`!k U U' (h:real^N->real^N) h' tf.
        ltensor_field k U tf /\ diffeomorphism_on U' U h h'
        ==> ltensor_field k U' (ltpullback h tf)`,
  REWRITE_TAC[ltensor_field; ltpullback] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tf") ASSUME_TAC) THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "tf" (MP_TAC o SPEC `(h:real^N->real^N) z`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\v. lift((tf:real^N->(num->real^N)->real) ((h:real^N->real^N) z)
          (\m. frechet_derivative h (at z) (if m = i then v else (u:num->real^N) m)))) =
    (\v. (\w. lift(tf (h z) (\j. if j = i then w
                                 else (\j. frechet_derivative h (at z) (u j)) j)))
         (frechet_derivative h (at z) v))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN ASM_REWRITE_TAC[ETA_AX] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`i:num`; `\j. frechet_derivative (h:real^N->real^N) (at z) ((u:num->real^N) j)`]) THEN
  ASM_REWRITE_TAC[]);;

let LTNORM2_PULLBACK = prove
 (`!k U U' (h:real^N->real^N) h' G tf y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\
        ltensor_field k U tf /\ y IN U'
        ==> ltnorm2 k (mpullback h G) (ltpullback h tf) y = ltnorm2 k G tf (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_INV_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(matrix(frechet_derivative (h:real^N->real^N) (at y)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `matrix(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))` THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
    SUBGOAL_THEN
     `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y)) o
      frechet_derivative h (at y) = (\x. x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[MATRIX_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) ((h:real^N->real^N) y))`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(h:real^N->real^N) y`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `(h:real^N->real^N) y`;
                 `S:real^N^N`] LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U':real^N->bool`; `mpullback (h:real^N->real^N) G`;
                 `ltpullback (h:real^N->real^N) tf`; `y:real^N`;
                 `(S:real^N^N) ** transp(matrix_inv(matrix(frechet_derivative
                     (h:real^N->real^N) (at y))))`] LRG_LTNORM2_SQUARES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTPULLBACK_TENSOR_FIELD THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[mpullback] THEN
    ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP] THEN
    ASM_REWRITE_TAC[MATRIX_INV_TRANSP; MATRIX_TRANSP_MUL; TRANSP_TRANSP;
                    MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ltpullback] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  ASM_SIMP_TAC[GSYM MATRIX_WORKS] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC; MATRIX_INV;
               MATRIX_MUL_LID]);;

(* ========================================================================= *)
(* Closure properties of tensor fields; the covariant derivative of a smooth *)
(* tensor field is a smooth tensor field; the metric is parallel.            *)
(* ========================================================================= *)

let LRG_TENSOR_FIELD_SUB = prove
 (`!k s (f:real^N->(num->real^N)->real) g.
        ltensor_field k s f /\ ltensor_field k s g
        ==> ltensor_field k s (\z u. f z u - g z u)`,
  REWRITE_TAC[ltensor_field] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`)) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
    ASM_SIMP_TAC[]]);;

let LRG_TENSOR_FIELD_SUM = prove
 (`!k s (f:num->real^N->(num->real^N)->real) n.
        (!i. 1 <= i /\ i <= n ==> ltensor_field k s (f i))
        ==> ltensor_field k s (\z u. sum (1..n) (\i. f i z u))`,
  REWRITE_TAC[ltensor_field] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n
        ==> (!u u'. (!m. 1 <= m /\ m <= k ==> u m = u' m)
                    ==> (f:num->real^N->(num->real^N)->real) j y u = f j y u') /\
            (!i u. 1 <= i /\ i <= k
                   ==> linear (\v. lift(f j y (\j'. if j' = i then v else u j'))))`
  (LABEL_TAC "fj") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN USE_THEN "fj" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `1 <= j`) (ASSUME `(j:num) <= n`))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN BETA_TAC THEN USE_THEN "fj" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `1 <= j`) (ASSUME `(j:num) <= n`))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;

let LRG_LNABLA_EQ = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
        lnabla k G tf =
        (\z u. drop(frechet_derivative (\x. lift(tf x u)) (at z) (u(k + 1))) -
               sum(1..k) (\i. tf z (\j. if j = i
                                        then christoffel G z (u(k + 1)) (u i)
                                        else u j)))`,
  REWRITE_TAC[FUN_EQ_THM; lnabla]);;

let LRG_LNABLA_DTERM_FIELD = prove
 (`!k U (tf:real^N->(num->real^N)->real).
        open U /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\y. lift(tf y u)))
        ==> ltensor_field (k + 1) U
              (\z u. drop(frechet_derivative (\x. lift(tf x u)) (at z)
                                             (u(k + 1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u u'. (!m. 1 <= m /\ m <= k ==> (u:num->real^N) m = u' m)
           ==> frechet_derivative (\x. lift((tf:real^N->(num->real^N)->real) x u))
                                  (at y) =
               frechet_derivative (\x. lift(tf x u')) (at y)`
  (LABEL_TAC "fd") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(u:num->real^N)(k + 1) = u'(k + 1)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN USE_THEN "fd" MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_CASES_TAC `i = k + 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!v. frechet_derivative
            (\x. lift((tf:real^N->(num->real^N)->real) x
                        (\j. if j = k + 1 then v else u j))) (at y) =
          frechet_derivative (\x. lift(tf x u)) (at y)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN USE_THEN "fd" MATCH_MP_TAC THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k + 1 = i)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(i:num) <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. frechet_derivative
          (\x. lift((tf:real^N->(num->real^N)->real) x
                      (\j. if j = i then c else u j))) (at y) =
        (\a. vsum (1..dimindex(:N))
               (\q. c$q % frechet_derivative
                            (\x. lift(tf x (\j. if j = i then basis q else u j)))
                            (at y) a))`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`\x v. lift((tf:real^N->(num->real^N)->real) x
                                  (\j. if j = i then v else u j))`;
                   `U:real^N->bool`; `y:real^N`; `c:real^N`]
           LRG_HAS_DERIVATIVE_LINFAM_CONST) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
      REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `q:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; LRG_LINEAR_VSUM_COMPONENTS]);;

let LRG_LNABLA_CTERM_FIELD = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) i.
        metric_field U G /\ ltensor_field k U tf /\ 1 <= i /\ i <= k
        ==> ltensor_field (k + 1) U
              (\z u. tf z (\j. if j = i then christoffel G z (u(k + 1)) (u i)
                               else u j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ltensor_field] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ind") (LABEL_TAC "lin")) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g2") (LABEL_TAC "g1")) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->real^N`; `u':num->real^N`] THEN
    DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(u:num->real^N)(k + 1) = u'(k + 1) /\ u i = u' i`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "ind" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `~(i = k + 1) /\ ~(k + 1 = i)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p = k + 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\v. lift((tf:real^N->(num->real^N)->real) y
          (\j. if j = i then christoffel (G:real^N->real^N^N) y v ((u:num->real^N) i)
               else if j = k + 1 then v else u j))) =
      (\v. (\w. lift(tf y (\j. if j = i then w else u j)))
           ((\v. christoffel G y v (u i)) v))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN BETA_TAC THEN
      AP_TERM_TAC THEN USE_THEN "ind" MATCH_MP_TAC THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
    USE_THEN "g1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "lin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num) <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(k + 1 = p)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\v. lift((tf:real^N->(num->real^N)->real) y
          (\j. if j = i then christoffel (G:real^N->real^N^N) y ((u:num->real^N) (k + 1)) v
               else if j = i then v else u j))) =
      (\v. (\w. lift(tf y (\j. if j = i then w else u j)))
           (christoffel G y (u(k + 1)) v))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN BETA_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
    USE_THEN "g2" (fun th -> REWRITE_TAC[th; ETA_AX]) THEN
    USE_THEN "lin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\v. lift((tf:real^N->(num->real^N)->real) y
        (\j. if j = i then christoffel (G:real^N->real^N^N) y ((u:num->real^N) (k + 1)) (u i)
             else if j = p then v else u j))) =
    (\v. lift(tf y (\j. if j = p then v
                       else (\j. if j = i then christoffel G y (u(k + 1)) (u i)
                                 else u j) j)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `j:num = p` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "lin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let LRG_SMOOTH_TENSOR_SLOT = prove
 (`!k U (tf:real^N->(num->real^N)->real) i u (X:real^N->real^N).
        open U /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\y. lift(tf y u))) /\ 1 <= i /\ i <= k /\
        smooth_map_on U X
        ==> smooth_map_on U (\y. lift(tf y (\j. if j = i then X y else u j)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\y. vsum (1..dimindex(:N))
          (\q. lift(drop(lift(((X:real^N->real^N) y)$q)) *
                    drop(lift((tf:real^N->(num->real^N)->real) y
                                (\j. if j = i then basis q else u j)))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`(tf:real^N->(num->real^N)->real) y`; `i:num`;
                   `u:num->real^N`; `(X:real^N->real^N) y`] LRG_SLOT_EXPAND) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
      REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF]];
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `q:num` THEN
    STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\y. lift(((X:real^N->real^N) y)$q)`;
                   `\y. lift((tf:real^N->(num->real^N)->real) y
                               (\j. if j = i then basis q else u j))`]
           SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT]]);;

let LNABLA_TENSOR_FIELD = prove
 (`!k U (G:real^N->real^N^N) tf.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\y. lift(tf y u)))
        ==> ltensor_field (k + 1) U (lnabla k G tf) /\
            (!u. smooth_map_on U (\y. lift(lnabla k G tf y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[LRG_LNABLA_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_DTERM_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_TENSOR_FIELD_SUM THEN REPEAT STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC LRG_LNABLA_CTERM_FIELD THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->real^N` THEN BETA_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_SMOOTH_TENSOR_SLOT THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let LNABLA_METRIC = prove
 (`!U (G:real^N->real^N^N) y u.
        metric_field U G /\ y IN U ==> lnabla 2 G (lmetric2 G) y u = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  REWRITE_TAC[lnabla; lmetric2] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[SUM_2; ARITH] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `y:real^N`; `(u:num->real^N) 1`;
                 `(u:num->real^N) 2`] LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 3`; `(u:num->real^N) 2`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y ((u:num->real^N) 3) (u 1)`;
                 `(u:num->real^N) 2`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Derivative of a family of multilinear forms evaluated on differentiable   *)
(* vectors (product rule), and naturality of the covariant derivative of     *)
(* tensor fields under pullback (LNABLA_PULLBACK).                           *)
(* ========================================================================= *)

let LRG_TUPLE_TAC =
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j = r + 1` THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= r + 1 /\ r + 1 <= r + 1 /\ ~(r + 1 <= r)`;
               ARITH_RULE `~(j = r + 1)
                           ==> (1 <= j /\ j <= r + 1 <=> 1 <= j /\ j <= r)`];;

let LRG_HAS_DERIVATIVE_MULTIFAM = prove
 (`!(M:real^N->(num->real^N)->real) (w:real^N->num->real^N) w' k s y.
        open s /\ y IN s /\ ltensor_field k s M /\
        (!c. (\z. lift(M z c)) differentiable at y) /\
        (!m. 1 <= m /\ m <= k ==> ((\z. w z m) has_derivative (w' m)) (at y))
        ==> ((\z. lift(M z (w z))) has_derivative
             (\e. frechet_derivative (\z. lift(M z (w y))) (at y) e +
                  lift(sum (1..k) (\m. M y (\j. if j = m then w' m e
                                                 else w y j))))) (at y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. r <= k
        ==> !c. ((\z. lift((M:real^N->(num->real^N)->real) z
                    (\m. if 1 <= m /\ m <= r then (w:real^N->num->real^N) z m
                         else c m))) has_derivative
                 (\e. frechet_derivative
                        (\z. lift(M z (\m. if 1 <= m /\ m <= r then w y m
                                           else c m))) (at y) e +
                      lift(sum (1..r)
                        (\m. M y (\j. if j = m then w' m e
                                      else if 1 <= j /\ j <= r then w y j
                                      else c j))))) (at y)`
  (MP_TAC o SPEC `k:num`) THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN GEN_TAC THEN
      REWRITE_TAC[ARITH_RULE `~(1 <= m /\ m <= 0)`; ETA_AX] THEN
      REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; LIFT_NUM; VECTOR_ADD_RID; ETA_AX] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN DISCH_TAC THEN X_GEN_TAC `c:num->real^N` THEN
    SUBGOAL_THEN `(r:num) <= k`
     (fun th -> FIRST_X_ASSUM(LABEL_TAC "ih" o C MP th)) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\z v. lift((M:real^N->(num->real^N)->real) z
                    (\j. if j = r + 1 then v
                         else if 1 <= j /\ j <= r then (w:real^N->num->real^N) z j
                         else (c:num->real^N) j))`;
      `\z. (w:real^N->num->real^N) z (r + 1)`; `(w':num->real^N->real^N) (r + 1)`;
      `s:real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        UNDISCH_TAC `ltensor_field k s (M:real^N->(num->real^N)->real)` THEN
        REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL
         [`r + 1`; `\j. if 1 <= j /\ j <= r then (w:real^N->num->real^N) z j
                       else (c:num->real^N) j`] o CONJUNCT2) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        USE_THEN "ih" (MP_TAC o SPEC
          `\j. if j = r + 1 then basis q else (c:num->real^N) j`) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (MESON[differentiable]
          `((f:real^N->real^1) has_derivative f') (at (y:real^N))
           ==> f differentiable at y`)) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN BETA_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN LRG_TUPLE_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z. lift((M:real^N->(num->real^N)->real) z
              (\j. if j = r + 1 then (w:real^N->num->real^N) z (r + 1)
                   else if 1 <= j /\ j <= r then w z j else (c:num->real^N) j))) =
      (\z. lift(M z (\m. if 1 <= m /\ m <= r + 1 then w z m else c m)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN BETA_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN LRG_TUPLE_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative
        (\z. lift((M:real^N->(num->real^N)->real) z
                (\j. if j = r + 1 then (w:real^N->num->real^N) y (r + 1)
                     else if 1 <= j /\ j <= r then w z j else (c:num->real^N) j)))
        (at y) =
      (\e. frechet_derivative
             (\z. lift(M z (\m. if 1 <= m /\ m <= r + 1 then w y m else c m)))
             (at y) e +
           lift(sum (1..r)
             (\m. M y (\j. if j = m then (w':num->real^N->real^N) m e
                           else if 1 <= j /\ j <= r + 1 then w y j else c j))))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      USE_THEN "ih" (MP_TAC o SPEC
        `\j. if j = r + 1 then (w:real^N->num->real^N) y (r + 1)
             else (c:num->real^N) j`) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN BETA_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN LRG_TUPLE_TAC;
        REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real^N` THEN BETA_TAC THEN
        BINOP_TAC THENL
         [AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN BETA_TAC THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN LRG_TUPLE_TAC;
          AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
          X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
          AP_TERM_TAC THEN LRG_TUPLE_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real^N` THEN BETA_TAC THEN
    REWRITE_TAC[LRG_SUM_NUMSEG_ADD1; LIFT_ADD] THEN
    SUBGOAL_THEN
     `(M:real^N->(num->real^N)->real) y
        (\j. if j = r + 1 then (w':num->real^N->real^N) (r + 1) e
             else if 1 <= j /\ j <= r then (w:real^N->num->real^N) y j
             else (c:num->real^N) j) =
      M y (\j. if j = r + 1 then w' (r + 1) e
               else if 1 <= j /\ j <= r + 1 then w y j else c j)`
    SUBST1_TAC THENL [AP_TERM_TAC THEN LRG_TUPLE_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `(w:real^N->num->real^N) y`) THEN
  REWRITE_TAC[COND_ID; ETA_AX] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`\z. lift((M:real^N->(num->real^N)->real) z
           (\m. if 1 <= m /\ m <= k then (w:real^N->num->real^N) z m else w y m))`;
    `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  AP_TERM_TAC THEN
  UNDISCH_TAC `ltensor_field k s (M:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  SIMP_TAC[]);;

let LRG_TENSOR_FIELD_COMPOSE = prove
 (`!k U U' (h:real^N->real^N) (tf:real^N->(num->real^N)->real).
        ltensor_field k U tf /\ (!z. z IN U' ==> h z IN U)
        ==> ltensor_field k U' (\z. tf (h z))`,
  REWRITE_TAC[ltensor_field] THEN MESON_TAC[]);;

let LNABLA_PULLBACK = prove
 (`!k U U' (h:real^N->real^N) h' G tf y u.
        metric_field U G /\ diffeomorphism_on U' U h h' /\
        ltensor_field k U tf /\ (!u. smooth_map_on U (\z. lift(tf z u))) /\
        y IN U'
        ==> lnabla k (mpullback h G) (ltpullback h tf) y u =
            ltpullback h (lnabla k G tf) y u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN U' ==> (h:real^N->real^N) z IN U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lnabla; ltpullback] THEN BETA_TAC THEN
  MP_TAC(ISPECL
   [`\z. (tf:real^N->(num->real^N)->real) ((h:real^N->real^N) z)`;
    `\z m. frechet_derivative (h:real^N->real^N) (at z) ((u:num->real^N) m)`;
    `\m e. dd2 (h:real^N->real^N) y e ((u:num->real^N) m)`;
    `k:num`; `U':real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_MULTIFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LRG_TENSOR_FIELD_COMPOSE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `c:num->real^N` THEN
      SUBGOAL_THEN
       `(\z. lift((tf:real^N->(num->real^N)->real) ((h:real^N->real^N) z) c)) =
        (\x. lift(tf x c)) o h`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `frechet_derivative (h:real^N->real^N) (at y)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      REWRITE_TAC[dd2; ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                     `(u:num->real^N) m`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^N`;
                 `\z. lift((tf:real^N->(num->real^N)->real) z
                        (\m. frechet_derivative (h:real^N->real^N) (at y)
                               ((u:num->real^N) m)))`;
                 `y:real^N`; `(u:num->real^N) (k + 1)`]
         LRG_FRECHET_DERIVATIVE_CHAIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `frechet_derivative (h:real^N->real^N) (at y)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= k
        ==> (tf:real^N->(num->real^N)->real) ((h:real^N->real^N) y)
              (\m. frechet_derivative h (at y)
                     (if m = i
                      then christoffel (mpullback h G) y ((u:num->real^N) (k + 1)) (u i)
                      else u m)) =
            tf (h y) (\j. if j = i
                          then christoffel G (h y)
                                 (frechet_derivative h (at y) (u (k + 1)))
                                 (frechet_derivative h (at y) (u i))
                          else frechet_derivative h (at y) (u j)) +
            tf (h y) (\j. if j = i then dd2 h y (u (k + 1)) (u i)
                          else frechet_derivative h (at y) (u j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\m. frechet_derivative (h:real^N->real^N) (at y)
             (if m = i
              then christoffel (mpullback h G) y ((u:num->real^N) (k + 1)) (u i)
              else u m)) =
      (\j. if j = i
           then christoffel G (h y) (frechet_derivative h (at y) (u (k + 1)))
                                    (frechet_derivative h (at y) (u i)) +
                dd2 h y (u (k + 1)) (u i)
           else frechet_derivative h (at y) (u j))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC LCHRISTOFFEL_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) y`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`i:num`; `\j. frechet_derivative (h:real^N->real^N) (at y)
                       ((u:num->real^N) j)`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LINEAR_ADD) THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..k)
      (\i. (tf:real^N->(num->real^N)->real) ((h:real^N->real^N) y)
             (\m. frechet_derivative h (at y)
                    (if m = i
                     then christoffel (mpullback h G) y ((u:num->real^N) (k + 1)) (u i)
                     else u m))) =
    sum (1..k)
      (\i. tf (h y) (\j. if j = i
                         then christoffel G (h y)
                                (frechet_derivative h (at y) (u (k + 1)))
                                (frechet_derivative h (at y) (u i))
                         else frechet_derivative h (at y) (u j))) +
    sum (1..k)
      (\m. tf (h y) (\j. if j = m then dd2 h y (u (k + 1)) (u m)
                         else frechet_derivative h (at y) (u j)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The metric and the curvature as tensor fields; smoothness of the          *)
(* curvature; naturality of the curvature 4-tensor.                          *)
(* ========================================================================= *)

let LRG_CHRISTOFFEL_SMOOTH_ARG = prove
 (`!U (G:real^N->real^N^N) a (X:real^N->real^N).
        metric_field U G /\ smooth_map_on U X
        ==> smooth_map_on U (\y. christoffel G y a (X y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y. vsum (1..dimindex(:N))
                    (\q. drop(lift(((X:real^N->real^N) y)$q)) %
                         christoffel (G:real^N->real^N^N) y a (basis q))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LINEAR_APPLY_EXPAND THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_SIMP_TAC[ETA_AX];
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; LRG_CHRISTOFFEL_SMOOTH]]);;

let LRG_LRIEMANN_SMOOTH = prove
 (`!U (G:real^N->real^N^N) a b c.
        metric_field U G ==> smooth_map_on U (\y. lriemann G y a b c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[lriemann] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN
  TRY(MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH_ARG THEN
      ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH] THEN NO_TAC) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
  ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH]);;

let LRG_LMETRIC2_FIELD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 2 U (lmetric2 G) /\
            (!u. smooth_map_on U (\y. lift(lmetric2 G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ltensor_field; lmetric2] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BINOP_TAC THEN TRY AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[ARITH] THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
      SUBGOAL_THEN
       `(\v. lift((u:num->real^N) 1 dot ((G:real^N->real^N^N) y ** v))) =
        (\v. (\x. lift(u 1 dot x)) ((\v. G y ** v) v))`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
      REWRITE_TAC[LINEAR_LIFT_DOT; MATRIX_VECTOR_MUL_LINEAR]];
    GEN_TAC THEN REWRITE_TAC[lmetric2] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]]);;

let LRG_LINEAR_DOT_MATVEC = prove
 (`!a (A:real^N^N). linear (\x:real^N. lift(a dot (A ** x)))`,
  REWRITE_TAC[linear; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]);;

let LRM4_TENSOR_FIELD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 4 U (lrm4 G) /\
            (!u. smooth_map_on U (\y. lift(lrm4 G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN REWRITE_TAC[lrm4] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC; LRG_LRIEMANN_SMOOTH]] THEN
  REWRITE_TAC[ltensor_field; lrm4] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1")
    (CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "l3"))) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2 /\ u 3 = u' 3 /\ u 4 = u' 4`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3 \/ i = 4` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ARITH] THENL
   [SUBGOAL_THEN
     `(\v. lift((u:num->real^N) 3 dot
                ((G:real^N->real^N^N) y ** lriemann G y v (u 2) (u 4)))) =
      (\v. (\x. lift(u 3 dot (G y ** x))) ((\v. lriemann G y v (u 2) (u 4)) v))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
    REWRITE_TAC[LRG_LINEAR_DOT_MATVEC] THEN USE_THEN "l1" MATCH_ACCEPT_TAC;
    SUBGOAL_THEN
     `(\v. lift((u:num->real^N) 3 dot
                ((G:real^N->real^N^N) y ** lriemann G y (u 1) v (u 4)))) =
      (\v. (\x. lift(u 3 dot (G y ** x))) ((\v. lriemann G y (u 1) v (u 4)) v))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
    REWRITE_TAC[LRG_LINEAR_DOT_MATVEC] THEN USE_THEN "l2" MATCH_ACCEPT_TAC;
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
    SUBGOAL_THEN
     `(\v. lift((u:num->real^N) 3 dot
                ((G:real^N->real^N^N) y ** lriemann G y (u 1) (u 2) v))) =
      (\v. (\x. lift(u 3 dot (G y ** x))) ((\v. lriemann G y (u 1) (u 2) v) v))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
    REWRITE_TAC[LRG_LINEAR_DOT_MATVEC] THEN USE_THEN "l3" MATCH_ACCEPT_TAC]);;

let LRM4_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> lrm4 (mpullback h G) y u = ltpullback h (lrm4 G) y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4; ltpullback] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`; `(u:num->real^N) 4`]
         LRIEMANN_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* Iterated covariant derivatives: tensor fields, locality, naturality;      *)
(* chart independence of |nabla^l Rm|^2 and of the squared C^k distance;     *)
(* continuity of |nabla^l Rm|^2.                                             *)
(* ========================================================================= *)

let LRG_LNABLA_ITER_FIELD = prove
 (`!k U (G:real^N->real^N^N) tf.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\y. lift(tf y u)))
        ==> !l. ltensor_field (k + l) U (lnabla_iter k l G tf) /\
                (!u. smooth_map_on U (\y. lift(lnabla_iter k l G tf y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[lnabla_iter; ADD_CLAUSES];
    REWRITE_TAC[lnabla_iter; ADD_CLAUSES; ADD1] THEN
    MATCH_MP_TAC LNABLA_TENSOR_FIELD THEN ASM_REWRITE_TAC[]]);;

let LRG_LNABLA_LOCAL = prove
 (`!k (G1:real^N->real^N^N) G2 tf1 tf2 s y u.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z) /\
        (!z u. z IN s ==> tf1 z u = tf2 z u)
        ==> lnabla k G1 tf1 y u = lnabla k G2 tf2 y u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. christoffel (G1:real^N->real^N^N) y a b = christoffel G2 y a b`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lnabla] THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[]]);;

let LRG_LNABLA_ITER_LOCAL = prove
 (`!k (G1:real^N->real^N^N) G2 tf1 tf2 s.
        open s /\ (!z. z IN s ==> G1 z = G2 z) /\
        (!z u. z IN s ==> tf1 z u = tf2 z u)
        ==> !l z u. z IN s
                    ==> lnabla_iter k l G1 tf1 z u = lnabla_iter k l G2 tf2 z u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[lnabla_iter] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[]);;

let LRG_LNABLA_ITER_PULLBACK = prove
 (`!k U U' (h:real^N->real^N) h' G tf tf'.
        metric_field U G /\ diffeomorphism_on U' U h h' /\
        ltensor_field k U tf /\ (!u. smooth_map_on U (\z. lift(tf z u))) /\
        (!z u. z IN U' ==> tf' z u = ltpullback h tf z u)
        ==> !l z u. z IN U'
                    ==> lnabla_iter k l (mpullback h G) tf' z u =
                        ltpullback h (lnabla_iter k l G tf) z u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[lnabla_iter] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla (k + l) (mpullback (h:real^N->real^N) G)
                (ltpullback h (lnabla_iter k l G tf)) z u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC LNABLA_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let LRG_LTNORM2_EQ = prove
 (`!k (G1:real^N->real^N^N) G2 tf1 tf2 y.
        G1 y = G2 y /\ (!u. tf1 y u = tf2 y u)
        ==> ltnorm2 k G1 tf1 y = ltnorm2 k G2 tf2 y`,
  SIMP_TAC[ltnorm2]);;

let LRM_DERIV_NORM2_PULLBACK = prove
 (`!l U U' (h:real^N->real^N) h' G y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> lrm_deriv_norm2 l (mpullback h G) y = lrm_deriv_norm2 l G (h y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                 `lrm4 (mpullback (h:real^N->real^N) G)`]
         LRG_LNABLA_ITER_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC LRM4_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltnorm2 (4 + l) (mpullback (h:real^N->real^N) G)
                (ltpullback h (lnabla_iter 4 l G (lrm4 G))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC LTNORM2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
    ASM_SIMP_TAC[]]);;

let LRG_LMETRIC2_DIFF_FIELD = prove
 (`!U (G0:real^N->real^N^N) G.
        metric_field U G0 /\ metric_field U G
        ==> ltensor_field 2 U (\z u. lmetric2 G z u - lmetric2 G0 z u) /\
            (!u. smooth_map_on U
                   (\y. lift((\z u. lmetric2 G z u - lmetric2 G0 z u) y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field]]);;

let LCK_DIST2_PULLBACK = prove
 (`!k U U' (h:real^N->real^N) h' G0 G y.
        metric_field U G0 /\ metric_field U G /\
        diffeomorphism_on U' U h h' /\ y IN U'
        ==> lck_dist2 k (mpullback h G0) (mpullback h G) y = lck_dist2 k G0 G (h y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                 `\z u. lmetric2 (mpullback (h:real^N->real^N) G) z u -
                        lmetric2 (mpullback h G0) z u`]
         LRG_LNABLA_ITER_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `u:num->real^N`] THEN DISCH_TAC THEN
    REWRITE_TAC[ltpullback; lmetric2] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[LRG_MPULLBACK_DOT];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltnorm2 (2 + l) (mpullback (h:real^N->real^N) G0)
                (ltpullback h (lnabla_iter 2 l G0
                  (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC LTNORM2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
           LRG_LNABLA_ITER_FIELD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]]);;

let LRM_DERIV_NORM2_LOCAL = prove
 (`!l (G1:real^N->real^N^N) G2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> lrm_deriv_norm2 l G1 y = lrm_deriv_norm2 l G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
  MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`4`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `lrm4 (G1:real^N->real^N^N)`; `lrm4 (G2:real^N->real^N^N)`;
                 `s:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4] THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRIEMANN_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let LCK_DIST2_LOCAL = prove
 (`!k (G0:real^N->real^N^N) G0' G G' s y.
        open s /\ y IN s /\ (!z. z IN s ==> G0 z = G0' z /\ G z = G' z)
        ==> lck_dist2 k G0 G y = lck_dist2 k G0' G' y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`2`; `G0:real^N->real^N^N`; `G0':real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                 `\z u. lmetric2 (G':real^N->real^N^N) z u - lmetric2 G0' z u`;
                 `s:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[lmetric2]; ASM_SIMP_TAC[]]);;

let LRG_SMOOTH_LIFT_MUL_REAL = prove
 (`!s (f:real^M->real) g.
        open s /\ smooth_map_on s (\x. lift(f x)) /\
        smooth_map_on s (\x. lift(g x))
        ==> smooth_map_on s (\x. lift(f x * g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift((f:real^M->real) x)`;
                 `\x. lift((g:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let LRG_SMOOTH_LIFT_SUM_REAL = prove
 (`!s (f:A->real^M->real) k.
        open s /\ FINITE k /\ (!i. i IN k ==> smooth_map_on s (\x. lift(f i x)))
        ==> smooth_map_on s (\x. lift(sum k (\i. f i x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\i x. lift((f:A->real^M->real) i x)`;
                 `k:A->bool`] SMOOTH_MAP_ON_LIFT_SUM) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let LRG_SMOOTH_LIFT_PRODUCT_REAL = prove
 (`!s (f:A->real^M->real) k.
        open s /\ FINITE k /\ (!i. i IN k ==> smooth_map_on s (\x. lift(f i x)))
        ==> smooth_map_on s (\x. lift(product k (\i. f i x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\i x. lift((f:A->real^M->real) i x)`;
                 `k:A->bool`] SMOOTH_MAP_ON_LIFT_PRODUCT) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let LRG_LTNORM2_SMOOTH = prove
 (`!k U (G:real^N->real^N^N) tf.
        metric_field U G /\ (!u. smooth_map_on U (\y. lift(tf y u)))
        ==> smooth_map_on U (\y. lift(ltnorm2 k G tf y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> smooth_map_on U (\y. lift(matrix_inv((G:real^N->real^N^N) y)$a$b))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `\z. matrix_inv((G:real^N->real^N^N) z)`]
           LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    ALL_TAC] THEN
  REWRITE_TAC[ltnorm2] THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
  ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN X_GEN_TAC `i:num->num` THEN
  DISCH_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
  ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_PRODUCT_REAL THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let LRM_DERIV_NORM2_CONTINUOUS = prove
 (`!l U (G:real^N->real^N^N).
        metric_field U G ==> (\y. lift(lrm_deriv_norm2 l G y)) continuous_on U`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
  REWRITE_TAC[lrm_deriv_norm2] THEN MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The second Bianchi identity.  The covariant derivative of the curvature   *)
(* 4-tensor is expressed through the covariant derivative of the (1,3)       *)
(* tensor; pair symmetry moves the cyclic slots to the first pair; the       *)
(* classical identity in (1,3) form is a formal consequence of the           *)
(* symmetries of the Christoffel symbols and of their second derivatives.    *)
(* ========================================================================= *)

let LRG_DLRIEMANN = prove
 (`!U (G:real^N->real^N^N) y a b d e.
        metric_field U G /\ y IN U
        ==> frechet_derivative (\z. lriemann G z a b d) (at y) e =
            (frechet_derivative
               (\z. frechet_derivative (\x. christoffel G x b d) (at z) a) (at y) e -
             frechet_derivative
               (\z. frechet_derivative (\x. christoffel G x a d) (at z) b) (at y) e) +
            ((christoffel G y a (frechet_derivative (\z. christoffel G z b d) (at y) e) +
              frechet_derivative (\z. christoffel G z a (christoffel G y b d)) (at y) e) -
             (christoffel G y b (frechet_derivative (\z. christoffel G z a d) (at y) e) +
              frechet_derivative (\z. christoffel G z b (christoffel G y a d)) (at y) e))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lriemann (G:real^N->real^N^N) z a b d) =
    (\z. (frechet_derivative (\x. christoffel G x b d) (at z) a -
          frechet_derivative (\x. christoffel G x a d) (at z) b) +
         (christoffel G z a (christoffel G z b d) -
          christoffel G z b (christoffel G z a d)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lriemann] THEN GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q r. ((\z. christoffel (G:real^N->real^N^N) z p (christoffel G z q r))
             has_derivative
             (\e. christoffel G y p
                    (frechet_derivative (\z. christoffel G z q r) (at y) e) +
                  frechet_derivative (\z. christoffel G z p (christoffel G y q r))
                    (at y) e)) (at y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`christoffel (G:real^N->real^N^N)`;
                   `(\z. p):real^N->real^N`; `(\e. vec 0):real^N->real^N`;
                   `\z. christoffel (G:real^N->real^N^N) z q r`;
                   `frechet_derivative (\z. christoffel (G:real^N->real^N^N) z q r)
                                       (at y)`;
                   `U:real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_BILFAM) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real^N` THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP LINEAR_0 o SPEC
      `christoffel (G:real^N->real^N^N) y q r`) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q r. ((\z. frechet_derivative (\x. christoffel (G:real^N->real^N^N) x q r)
                                     (at z) p) has_derivative
             frechet_derivative
               (\z. frechet_derivative (\x. christoffel G x q r) (at z) p) (at y))
            (at y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. (frechet_derivative (\x. christoffel (G:real^N->real^N^N) x b d) (at z) a -
           frechet_derivative (\x. christoffel G x a d) (at z) b) +
          (christoffel G z a (christoffel G z b d) -
           christoffel G z b (christoffel G z a d))) has_derivative
     (\e. (frechet_derivative
             (\z. frechet_derivative (\x. christoffel G x b d) (at z) a) (at y) e -
           frechet_derivative
             (\z. frechet_derivative (\x. christoffel G x a d) (at z) b) (at y) e) +
          ((christoffel G y a (frechet_derivative (\z. christoffel G z b d) (at y) e) +
            frechet_derivative (\z. christoffel G z a (christoffel G y b d)) (at y) e) -
           (christoffel G y b (frechet_derivative (\z. christoffel G z a d) (at y) e) +
            frechet_derivative (\z. christoffel G z b (christoffel G y a d))
              (at y) e)))) (at y)`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[ETA_AX]);;

let LRG_LNABLA_LRM4 = prove
 (`!U (G:real^N->real^N^N) y u.
        metric_field U G /\ y IN U
        ==> lnabla 4 G (lrm4 G) y u =
            u 3 dot (G y **
              (frechet_derivative (\z. lriemann G z (u 1) (u 2) (u 4)) (at y) (u 5) +
               christoffel G y (u 5) (lriemann G y (u 1) (u 2) (u 4)) -
               lriemann G y (christoffel G y (u 5) (u 1)) (u 2) (u 4) -
               lriemann G y (u 1) (christoffel G y (u 5) (u 2)) (u 4) -
               lriemann G y (u 1) (u 2) (christoffel G y (u 5) (u 4))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[lnabla; lrm4; SUM_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`G:real^N->real^N^N`;
    `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         (G:real^N->real^N^N)) (at y)`;
    `(\z. (u:num->real^N) 3):real^N->real^N`; `(\h. vec 0):real^N->real^N`;
    `\z. lriemann (G:real^N->real^N^N) z ((u:num->real^N) 1) (u 2) (u 4)`;
    `frechet_derivative
       (\z. lriemann (G:real^N->real^N^N) z ((u:num->real^N) 1) (u 2) (u 4))
       (at y)`;
    `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[LRG_LRIEMANN_SMOOTH]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP; DOT_LZERO; REAL_ADD_LID; GSYM mderiv] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 3`; `(u:num->real^N) 5`;
                 `lriemann (G:real^N->real^N^N) y ((u:num->real^N) 1) (u 2) (u 4)`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y ((u:num->real^N) 5) (u 3)`;
                 `lriemann (G:real^N->real^N^N) y ((u:num->real^N) 1) (u 2) (u 4)`]
         LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_RADD; DOT_RSUB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  REAL_ARITH_TAC);;

let LRG_LNABLA_LRM4_PAIR = prove
 (`!U (G:real^N->real^N^N) y a b c d e.
        metric_field U G /\ y IN U
        ==> lnabla 4 G (lrm4 G) y
              (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c
                   else if m = 4 then d else e) =
            lnabla 4 G (lrm4 G) y
              (\m. if m = 1 then c else if m = 2 then d else if m = 3 then a
                   else if m = 4 then b else e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[lnabla; lrm4; SUM_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(c dot ((G:real^N->real^N^N) z ** lriemann G z a b d)))
                       (at y) =
    frechet_derivative (\z. lift(a dot (G z ** lriemann G z c d b))) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRIEMANN_PAIR_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y e a`; `b:real^N`; `d:real^N`;
                 `c:real^N`] LRIEMANN_PAIR_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:real^N`; `christoffel (G:real^N->real^N^N) y e b`; `d:real^N`;
                 `c:real^N`] LRIEMANN_PAIR_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:real^N`; `b:real^N`; `d:real^N`;
                 `christoffel (G:real^N->real^N^N) y e c`] LRIEMANN_PAIR_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:real^N`; `b:real^N`; `christoffel (G:real^N->real^N^N) y e d`;
                 `c:real^N`] LRIEMANN_PAIR_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LRG_BIANCHI2_13 = prove
 (`!U (G:real^N->real^N^N) y p q r s.
        metric_field U G /\ y IN U
        ==> (frechet_derivative (\z. lriemann G z p q s) (at y) r +
             christoffel G y r (lriemann G y p q s) -
             lriemann G y (christoffel G y r p) q s -
             lriemann G y p (christoffel G y r q) s -
             lriemann G y p q (christoffel G y r s)) +
            (frechet_derivative (\z. lriemann G z q r s) (at y) p +
             christoffel G y p (lriemann G y q r s) -
             lriemann G y (christoffel G y p q) r s -
             lriemann G y q (christoffel G y p r) s -
             lriemann G y q r (christoffel G y p s)) +
            (frechet_derivative (\z. lriemann G z r p s) (at y) q +
             christoffel G y q (lriemann G y r p s) -
             lriemann G y (christoffel G y q r) p s -
             lriemann G y r (christoffel G y q p) s -
             lriemann G y r p (christoffel G y q s)) = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_DLRIEMANN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[lriemann] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_SUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `r:real^N`; `p:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `r:real^N`; `q:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `q:real^N`; `p:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\x. christoffel (G:real^N->real^N^N) x q s`;
                 `y:real^N`; `r:real^N`; `p:real^N`]
         LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\x. christoffel (G:real^N->real^N^N) x p s`;
                 `y:real^N`; `r:real^N`; `q:real^N`]
         LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\x. christoffel (G:real^N->real^N^N) x r s`;
                 `y:real^N`; `q:real^N`; `p:real^N`]
         LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  VECTOR_ARITH_TAC);;

(* LRM4_BIANCHI2: the second Bianchi identity (MT Claim 1.5),                *)
(* R_ijkl,h + R_ijlh,k + R_ijhk,l = 0.                                       *)

let LRM4_BIANCHI2 = prove
 (`!U (G:real^N->real^N^N) y a b c d e.
        metric_field U G /\ y IN U
        ==> lnabla 4 G (lrm4 G) y
              (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c
                   else if m = 4 then d else e) +
            lnabla 4 G (lrm4 G) y
              (\m. if m = 1 then a else if m = 2 then b else if m = 3 then d
                   else if m = 4 then e else c) +
            lnabla 4 G (lrm4 G) y
              (\m. if m = 1 then a else if m = 2 then b else if m = 3 then e
                   else if m = 4 then c else d) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `c:real^N`; `d:real^N`; `e:real^N`]
         LRG_LNABLA_LRM4_PAIR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `d:real^N`; `e:real^N`; `c:real^N`]
         LRG_LNABLA_LRM4_PAIR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `e:real^N`; `c:real^N`; `d:real^N`]
         LRG_LNABLA_LRM4_PAIR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_LNABLA_LRM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DOT_RADD; GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `c:real^N`;
                 `d:real^N`; `e:real^N`; `b:real^N`] LRG_BIANCHI2_13) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]);;

