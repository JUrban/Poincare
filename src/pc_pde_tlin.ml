(* ========================================================================= *)
(* Unit pc_pde_tlin (the torus theory, first part): linear parabolic systems *)
(* with scalar principal part on the torus: the fixed-time energy            *)
(* inequalities (PDE_FT1, PDE_FT2, PDE_FT3), the time derivative of the      *)
(* energy, a weighted Gronwall inequality, the energy estimate               *)
(* PDE_TORUS_ENERGY and uniqueness PDE_TORUS_UNIQUE.  Existence by the       *)
(* continuity method (M4, PDE_TORUS_LIN_HOLDS) is the second part, unit      *)
(* pc_pde_texist.                                                            *)
(* ========================================================================= *)

needs "src/pc_pde_heat.ml";;
needs "src/pc_pde_rdt_symbol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Integrals of real functions over the unit cube (pde_cint), their algebra  *)
(* for smooth integrands, integration by parts for periodic maps, and        *)
(* ellipticity for gradients of R^K-valued maps.                             *)
(* ========================================================================= *)

let pde_cint = new_definition
 `pde_cint (f:real^N->real) = drop(integral (interval[vec 0,vec 1]) (\x. lift(f x)))`;;

let PDE_CINT_INTEGRABLE = prove
 (`!f:real^N->real.
     smooth_map_on (:real^N) (\x. lift(f x))
     ==> (\x. lift(f x)) integrable_on interval[vec 0,vec 1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]);;

let PDE_CINT_ADD = prove
 (`!f g:real^N->real.
     smooth_map_on (:real^N) (\x. lift(f x)) /\ smooth_map_on (:real^N) (\x. lift(g x))
     ==> pde_cint (\x. f x + g x) = pde_cint f + pde_cint g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint; LIFT_ADD] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; PDE_CINT_INTEGRABLE; DROP_ADD]);;

let PDE_CINT_SUB = prove
 (`!f g:real^N->real.
     smooth_map_on (:real^N) (\x. lift(f x)) /\ smooth_map_on (:real^N) (\x. lift(g x))
     ==> pde_cint (\x. f x - g x) = pde_cint f - pde_cint g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint; LIFT_SUB] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB; PDE_CINT_INTEGRABLE; DROP_SUB]);;

let PDE_CINT_CMUL = prove
 (`!c (f:real^N->real).
     smooth_map_on (:real^N) (\x. lift(f x))
     ==> pde_cint (\x. c * f x) = c * pde_cint f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; PDE_CINT_INTEGRABLE; DROP_CMUL]);;

let PDE_CINT_NEG = prove
 (`!f:real^N->real.
     smooth_map_on (:real^N) (\x. lift(f x))
     ==> pde_cint (\x. --(f x)) = --(pde_cint f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint; LIFT_NEG] THEN
  ASM_SIMP_TAC[INTEGRAL_NEG; PDE_CINT_INTEGRABLE; DROP_NEG]);;

let PDE_CINT_SUM = prove
 (`!(f:A->real^N->real) s.
     FINITE s /\ (!a. a IN s ==> smooth_map_on (:real^N) (\x. lift(f a x)))
     ==> pde_cint (\x. sum s (\a. f a x)) = sum s (\a. pde_cint (f a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint; LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\a x. lift((f:A->real^N->real) a x)`; `interval[vec 0:real^N,vec 1]`;
                 `s:A->bool`] INTEGRAL_VSUM) THEN
  ASM_SIMP_TAC[PDE_CINT_INTEGRABLE; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_VSUM; o_DEF]);;

let PDE_CINT_LE = prove
 (`!f g:real^N->real.
     smooth_map_on (:real^N) (\x. lift(f x)) /\ smooth_map_on (:real^N) (\x. lift(g x)) /\
     (!x. f x <= g x)
     ==> pde_cint f <= pde_cint g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[PDE_CINT_INTEGRABLE; LIFT_DROP]);;

let PDE_CINT_POS = prove
 (`!f:real^N->real.
     smooth_map_on (:real^N) (\x. lift(f x)) /\ (!x. &0 <= f x) ==> &0 <= pde_cint f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[PDE_CINT_INTEGRABLE; LIFT_DROP]);;

let PDE_HS2_CINT = prove
 (`!s (u:real^N->real^K).
     pde_hs2 s u = sum (pde_index_lists s (:N))
                       (\l. pde_cint (\x. norm(iterated_partial l u x) pow 2))`,
  REWRITE_TAC[pde_hs2; pde_cint]);;

(* Integration by parts. *)

let PDE_CINT_IBP = prove
 (`!(u:real^N->real^K) v j.
     smooth_map_on (:real^N) u /\ smooth_map_on (:real^N) v /\
     pde_zper u /\ pde_zper v /\ 1 <= j /\ j <= dimindex(:N)
     ==> pde_cint (\x. partial_derivative j u x dot v x) =
         --(pde_cint (\x. u x dot partial_derivative j v x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_cint] THEN
  ASM_SIMP_TAC[PDE_CUBE_IBP; DROP_NEG]);;

(* Smoothness of dot products and squared norms of smooth maps. *)

let PDE_SMOOTH_DOT = prove
 (`!(u:real^N->real^K) v.
     smooth_map_on (:real^N) u /\ smooth_map_on (:real^N) v
     ==> smooth_map_on (:real^N) (\x. lift(u x dot v x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_REWRITE_TAC[OPEN_UNIV]);;

let PDE_SMOOTH_SQNORM = prove
 (`!(u:real^N->real^K).
     smooth_map_on (:real^N) u ==> smooth_map_on (:real^N) (\x. lift(norm(u x) pow 2))`,
  REWRITE_TAC[PDE_SQNORM_SMOOTH]);;

(* Ellipticity for gradients of R^K-valued maps. *)

let PDE_ELLIPTIC_GRAD = prove
 (`!(A:real^N^N) lam (p:num->real^K).
     (!v. lam * norm v pow 2 <= v dot (A ** v))
     ==> lam * sum(1..dimindex(:N)) (\i. norm(p i) pow 2) <=
         sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * (p i dot p j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:K)
        ==> lam * sum(1..dimindex(:N)) (\i. ((p:num->real^K) i)$k pow 2) <=
            sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
              (\j. (A:real^N^N)$i$j * ((p i)$k * (p j)$k)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. ((p:num->real^K) i)$k):real^N`) THEN
    MATCH_MP_TAC(REAL_ARITH `a = c /\ b = d ==> a <= b ==> c <= d`) THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[NORM_POW_2; dot] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
      REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; LAMBDA_BETA; dot] THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K))
                (\k. lam * sum(1..dimindex(:N)) (\i. ((p:num->real^K) i)$k pow 2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    REWRITE_TAC[NORM_POW_2; dot] THEN GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K)) (\k. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                (\j. (A:real^N^N)$i$j * (((p:num->real^K) i)$k * (p j)$k))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[dot; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The operator at a fixed time (pde_lop0), bounded and admissible           *)
(* coefficient data at a fixed time (pde_fbnd, pde_fcoeff), entries and      *)
(* norms of matrix fields.                                                   *)
(* ========================================================================= *)

let pde_lop0 = new_definition
 `pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) (C:real^N->real^K^K)
           (w:real^N->real^K) (x:real^N) =
    vsum(1..dimindex(:N))
      (\i. vsum(1..dimindex(:N))
             (\j. A x$i$j % partial_derivative i (partial_derivative j w) x)) +
    vsum(1..dimindex(:N)) (\i. B x i ** partial_derivative i w x) +
    C x ** w x`;;

let PDE_LOP_LOP0 = prove
 (`!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc u t x.
     pde_lop aa bb cc u t x = pde_lop0 (aa t) (bb t) (cc t) (u t) x`,
  REWRITE_TAC[pde_lop; pde_lop0]);;

(* Bounded coefficient data at a fixed time: smooth, Z^N-periodic, jets of   *)
(* order <= p bounded by M (pde_fbnd); admissible data are in addition       *)
(* lam-elliptic (pde_fcoeff).                                                *)

let pde_fbnd = new_definition
 `pde_fbnd p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) (C:real^N->real^K^K) <=>
    &0 <= M /\
    smooth_map_on (:real^N) (\x. (vectorize:real^N^N->real^(N,N)finite_prod) (A x)) /\
    (!i. smooth_map_on (:real^N) (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (B x i))) /\
    smooth_map_on (:real^N) (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (C x)) /\
    pde_zper A /\ (!i. pde_zper (\x. B x i)) /\ pde_zper C /\
    (!l x. LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
           ==> norm(iterated_partial l
                      (\x. (vectorize:real^N^N->real^(N,N)finite_prod) (A x)) x) <= M /\
               (!i. 1 <= i /\ i <= dimindex(:N)
                    ==> norm(iterated_partial l
                              (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (B x i)) x)
                        <= M) /\
               norm(iterated_partial l
                      (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (C x)) x) <= M)`;;

let pde_fcoeff = new_definition
 `pde_fcoeff p M lam (A:real^N->real^N^N) (B:real^N->num->real^K^K) (C:real^N->real^K^K) <=>
    &0 < lam /\ pde_fbnd p M A B C /\ (!x v. lam * norm v pow 2 <= v dot (A x ** v))`;;

(* Entries of smooth matrix fields. *)

let PDE_ENTRY_ITERATED = prove
 (`!(A:real^N->real^M^M) l i j x.
     smooth_map_on (:real^N) (\x. (vectorize:real^M^M->real^(M,M)finite_prod) (A x))
     ==> iterated_partial l (\x. lift(A x$i$j)) x =
         lift((matrify(iterated_partial l
                 (\x. (vectorize:real^M^M->real^(M,M)finite_prod) (A x)) x):real^M^M)$i$j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `\v:real^(M,M)finite_prod. lift((matrify v:real^M^M)$i$j)`;
                 `\x. (vectorize:real^M^M->real^(M,M)finite_prod) ((A:real^N->real^M^M) x)`;
                 `(:real^N)`; `x:real^N`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; OPEN_UNIV; IN_UNIV; MATRIFY_VECTORIZE]);;

let PDE_ROW_LE_VECTORIZE = prove
 (`!(A:real^N^M) i. norm(A$i) <= norm(vectorize A)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NORM] THEN REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  REWRITE_TAC[NORM_VECTORIZE_POW_2] THEN
  MP_TAC(ISPECL [`\i. norm((A:real^N^M)$i) pow 2`; `1..dimindex(:M)`; `k:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> s = t - x ==> x <= t`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

let PDE_MATRIFY_ENTRY_LE = prove
 (`!(v:real^(M,M)finite_prod) i j. abs((matrify v:real^M^M)$i$j) <= norm v`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((matrify v:real^M^M)$i)` THEN REWRITE_TAC[COMPONENT_LE_NORM] THEN
  MP_TAC(ISPECL [`matrify v:real^M^M`; `i:num`] PDE_ROW_LE_VECTORIZE) THEN
  REWRITE_TAC[VECTORIZE_MATRIFY]);;

let PDE_MATRIFY_MUL_NORM = prove
 (`!(v:real^(K,K)finite_prod) (g:real^K). norm((matrify v:real^K^K) ** g) <= norm v * norm g`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`matrify v:real^K^K`; `g:real^K`]
    COMPATIBLE_NORM_VECTORIZE) THEN REWRITE_TAC[VECTORIZE_MATRIFY]);;

(* ========================================================================= *)
(* Smoothness and jet bounds of the pieces of pde_lop0, and the pointwise    *)
(* commutator structure of D^l (pde_lop0):                                   *)
(* D^l L w = sum_ij A_ij d_i d_j D^l w + R with |R| bounded by the jet of    *)
(* w of order |l| + 1 (PDE_LOP0_COMM).                                       *)
(* ========================================================================= *)

let PDE_ITERATED_PARTIAL_COMM1 = prove
 (`!(w:real^N->real^K) l i.
     smooth_map_on (:real^N) w /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     1 <= i /\ i <= dimindex(:N)
     ==> iterated_partial l (partial_derivative i w) =
         partial_derivative i (iterated_partial l w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`; `i:num`] TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let PDE_ITERATED_PARTIAL_COMM2 = prove
 (`!(w:real^N->real^K) l i j.
     smooth_map_on (:real^N) w /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> iterated_partial l (partial_derivative i (partial_derivative j w)) =
         partial_derivative i (partial_derivative j (iterated_partial l w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (partial_derivative j (w:real^N->real^K))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC[PDE_ITERATED_PARTIAL_COMM1]);;

(* Smoothness of scalar and matrix multiples. *)

let PDE_SMOOTH_SCALAR_MUL = prove
 (`!(a:real^N->real) (g:real^N->real^K).
     smooth_map_on (:real^N) (\x. lift(a x)) /\ smooth_map_on (:real^N) g
     ==> smooth_map_on (:real^N) (\x. a x % g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. lift((a:real^N->real) x)`; `g:real^N->real^K`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP]);;

let PDE_SMOOTH_MATRIX_MUL = prove
 (`!(Q:real^N->real^K^K) (g:real^N->real^K).
     smooth_map_on (:real^N) (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (Q x)) /\
     smooth_map_on (:real^N) g
     ==> smooth_map_on (:real^N) (\x. Q x ** g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`;
                 `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                 `\x. (vectorize:real^K^K->real^(K,K)finite_prod) ((Q:real^N->real^K^K) x)`;
                 `g:real^N->real^K`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE]);;

(* Smoothness and jet bounds of the coefficient pieces. *)

let PDE_FBND_SMOOTH = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C i j.
     pde_fbnd p M A B C
     ==> smooth_map_on (:real^N) (\x. lift(A x$i$j)) /\
         smooth_map_on (:real^N) (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (B x i)) /\
         smooth_map_on (:real^N) (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (C x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_fbnd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(:real^N)`;
                 `\x. (vectorize:real^N^N->real^(N,N)finite_prod) ((A:real^N->real^N^N) x)`;
                 `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)`]
                SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; LRG_LINEAR_MATRIFY_ENTRY; o_DEF; MATRIFY_VECTORIZE]);;

let PDE_FBND_AJET = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C i j l x.
     pde_fbnd p M A B C /\ LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l (\x. lift(A x$i$j)) x) <= M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_fbnd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `x:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[PDE_ENTRY_ITERATED; NORM_LIFT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(iterated_partial l
                (\x. (vectorize:real^N^N->real^(N,N)finite_prod) ((A:real^N->real^N^N) x)) x)` THEN
  ASM_REWRITE_TAC[PDE_MATRIFY_ENTRY_LE]);;

let PDE_FBND_BJET = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C i l x.
     pde_fbnd p M A B C /\ LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     1 <= i /\ i <= dimindex(:N)
     ==> norm(iterated_partial l
                (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (B x i)) x) <= M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_fbnd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `x:real^N`]) THEN ASM_SIMP_TAC[]);;

let PDE_FBND_CJET = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C l x.
     pde_fbnd p M A B C /\ LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l
                (\x. (vectorize:real^K^K->real^(K,K)finite_prod) (C x)) x) <= M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_fbnd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `x:real^N`]) THEN ASM_SIMP_TAC[]);;

(* The three kinds of terms of D^l (pde_lop0 A B C w). *)

let PDE_LOP0_ATERM = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) l i j x.
     pde_fbnd p M A B C /\ smooth_map_on (:real^N) w /\ LENGTH l <= p /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> norm(iterated_partial l
                (\x. A x$i$j % partial_derivative i (partial_derivative j w) x) x -
              A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l w)) x)
         <= &2 pow (LENGTH l) * M * pde_jetn (LENGTH l + 1) w x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL [ASM_MESON_TAC[pde_fbnd]; ALL_TAC] THEN
  ASM_CASES_TAC `l:num list = []` THENL
   [ASM_REWRITE_TAC[iterated_partial; VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[PDE_JETN_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(a:real^1) (v:real^K). drop a % v`; `&1`; `M:real`]
                PDE_COMMUTATOR_BOUND) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; NORM_MUL; GSYM NORM_1; REAL_MUL_LID; REAL_LE_REFL;
              REAL_POS] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `\x:real^N. lift((A:real^N->real^N^N) x$i$j)`;
                             `partial_derivative i (partial_derivative j (w:real^N->real^K))`;
                             `x:real^N`]) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_FBND_SMOOTH) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FBND_AJET THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `B:real^N->num->real^K^K`; `C:real^N->real^K^K`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[PDE_ITERATED_PARTIAL_COMM2] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn (SUC(PRE(LENGTH(l:num list))))
                       (partial_derivative j (w:real^N->real^K)) x` THEN
  ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn (SUC(SUC(PRE(LENGTH(l:num list))))) (w:real^N->real^K) x` THEN
  ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN
  MATCH_MP_TAC PDE_JETN_MONO THEN
  UNDISCH_TAC `~(l:num list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC);;

let PDE_LOP0_BTERM = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) l i x.
     pde_fbnd p M A B C /\ smooth_map_on (:real^N) w /\ LENGTH l <= p /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ 1 <= i /\ i <= dimindex(:N)
     ==> norm(iterated_partial l (\x. B x i ** partial_derivative i w x) x)
         <= &2 pow (LENGTH l) * M * pde_jetn (LENGTH l + 1) w x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL [ASM_MESON_TAC[pde_fbnd]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                 `&1`; `M:real`] PDE_LEIBNIZ_BOUND) THEN
  REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; REAL_MUL_LID; PDE_MATRIFY_MUL_NORM; REAL_POS] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`l:num list`;
     `\x. (vectorize:real^K^K->real^(K,K)finite_prod) ((B:real^N->num->real^K^K) x i)`;
     `partial_derivative i (w:real^N->real^K)`; `x:real^N`]) THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN ANTS_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_FBND_SMOOTH) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FBND_BJET THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `A:real^N->real^N^N`; `C:real^N->real^K^K`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1] THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL]);;

let PDE_LOP0_CTERM = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) l x.
     pde_fbnd p M A B C /\ smooth_map_on (:real^N) w /\ LENGTH l <= p /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l (\x. C x ** w x) x)
         <= &2 pow (LENGTH l) * M * pde_jetn (LENGTH l + 1) w x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL [ASM_MESON_TAC[pde_fbnd]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                 `&1`; `M:real`] PDE_LEIBNIZ_BOUND) THEN
  REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; REAL_MUL_LID; PDE_MATRIFY_MUL_NORM; REAL_POS] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`l:num list`;
     `\x. (vectorize:real^K^K->real^(K,K)finite_prod) ((C:real^N->real^K^K) x)`;
     `w:real^N->real^K`; `x:real^N`]) THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN ANTS_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_FBND_SMOOTH) THEN
    ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FBND_CJET THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC);;

(* D^l distributes over the terms of pde_lop0. *)

let PDE_LOP0_PIECES_SMOOTH = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) i j.
     pde_fbnd p M A B C /\ smooth_map_on (:real^N) w
     ==> smooth_map_on (:real^N)
           (\x. A x$i$j % partial_derivative i (partial_derivative j w) x) /\
         smooth_map_on (:real^N) (\x. B x i ** partial_derivative i w x) /\
         smooth_map_on (:real^N) (\x. C x ** w x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_FBND_SMOOTH) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_SMOOTH_SCALAR_MUL; MATCH_MP_TAC PDE_SMOOTH_MATRIX_MUL;
    MATCH_MP_TAC PDE_SMOOTH_MATRIX_MUL] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; ETA_AX]);;

let PDE_LOP0_SMOOTH = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K).
     pde_fbnd p M A B C /\ smooth_map_on (:real^N) w
     ==> smooth_map_on (:real^N) (pde_lop0 A B C w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`; `w:real^N->real^K`] PDE_LOP0_PIECES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) =
                (\x. vsum(1..dimindex(:N))
                       (\i. vsum(1..dimindex(:N))
                              (\j. A x$i$j % partial_derivative i (partial_derivative j w) x)) +
                     (vsum(1..dimindex(:N)) (\i. B x i ** partial_derivative i w x) +
                      C x ** w x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_lop0]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
         REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG] THEN GEN_TAC THEN DISCH_TAC) THEN
  ASM_REWRITE_TAC[]);;

let PDE_LOP0_ITERATED = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) l x.
     pde_fbnd p M A B C /\ smooth_map_on (:real^N) w
     ==> iterated_partial l (pde_lop0 A B C w) x =
         vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
              (\j. iterated_partial l
                     (\x. A x$i$j % partial_derivative i (partial_derivative j w) x) x)) +
         vsum(1..dimindex(:N))
           (\i. iterated_partial l (\x. B x i ** partial_derivative i w x) x) +
         iterated_partial l (\x. C x ** w x) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`; `w:real^N->real^K`] PDE_LOP0_PIECES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) =
                (\x. vsum(1..dimindex(:N))
                       (\i. vsum(1..dimindex(:N))
                              (\j. A x$i$j % partial_derivative i (partial_derivative j w) x)) +
                     (vsum(1..dimindex(:N)) (\i. B x i ** partial_derivative i w x) +
                      C x ** w x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_lop0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on (:real^N)
          (\x. vsum(1..dimindex(:N))
                 (\j. (A:real^N->real^N^N) x$i$j %
                      partial_derivative i (partial_derivative j (w:real^N->real^K)) x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N)
      (\x. vsum(1..dimindex(:N))
             (\i. vsum(1..dimindex(:N))
                    (\j. (A:real^N->real^N^N) x$i$j %
                         partial_derivative i (partial_derivative j (w:real^N->real^K)) x))) /\
    smooth_map_on (:real^N)
      (\x. vsum(1..dimindex(:N))
             (\i. (B:real^N->num->real^K^K) x i ** partial_derivative i w x)) /\
    smooth_map_on (:real^N) (\x. (C:real^N->real^K^K) x ** w x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`l:num list`; `(:real^N)`;
    `\x. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. (A:real^N->real^N^N) x$i$j %
                       partial_derivative i (partial_derivative j (w:real^N->real^K)) x))`;
    `\x. vsum(1..dimindex(:N))
           (\i. (B:real^N->num->real^K^K) x i ** partial_derivative i (w:real^N->real^K) x) +
         (C:real^N->real^K^K) x ** w x`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`l:num list`; `(:real^N)`;
    `\x. vsum(1..dimindex(:N))
           (\i. (B:real^N->num->real^K^K) x i ** partial_derivative i (w:real^N->real^K) x)`;
    `\x. (C:real^N->real^K^K) x ** (w:real^N->real^K) x`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`l:num list`; `(:real^N)`;
    `\i x. (B:real^N->num->real^K^K) x i ** partial_derivative i (w:real^N->real^K) x`;
    `1..dimindex(:N)`] PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_UNIV; ETA_AX] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL
   [`l:num list`; `(:real^N)`;
    `\i x. vsum(1..dimindex(:N))
             (\j. (A:real^N->real^N^N) x$i$j %
                  partial_derivative i (partial_derivative j (w:real^N->real^K)) x)`;
    `1..dimindex(:N)`] PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_UNIV; ETA_AX] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  MP_TAC(ISPECL
   [`l:num list`; `(:real^N)`;
    `\j x. (A:real^N->real^N^N) x$i$j %
           partial_derivative i (partial_derivative j (w:real^N->real^K)) x`;
    `1..dimindex(:N)`] PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_UNIV; ETA_AX] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* The commutator structure. *)

let PDE_LOP0_COMM = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K) l x.
     pde_fbnd p M A B C /\ smooth_map_on (:real^N) w /\ LENGTH l <= p /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l (pde_lop0 A B C w) x -
              vsum(1..dimindex(:N))
                (\i. vsum(1..dimindex(:N))
                       (\j. A x$i$j % partial_derivative i
                                        (partial_derivative j (iterated_partial l w)) x)))
         <= &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) *
            &2 pow (LENGTH l) * M * pde_jetn (LENGTH l + 1) w x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`; `w:real^N->real^K`; `l:num list`; `x:real^N`]
                PDE_LOP0_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `c = &2 pow (LENGTH(l:num list)) * M * pde_jetn (LENGTH l + 1)
                                                      (w:real^N->real^K) x` THEN
  SUBGOAL_THEN
   `norm(vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
              (\j. iterated_partial l
                     (\x. (A:real^N->real^N^N) x$i$j %
                          partial_derivative i (partial_derivative j (w:real^N->real^K)) x)
                     x)) -
         vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
              (\j. A x$i$j % partial_derivative i
                               (partial_derivative j (iterated_partial l w)) x)))
    <= &(dimindex(:N) * dimindex(:N)) * c`
  ASSUME_TAC THENL
   [SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. c:real))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN EXPAND_TAC "c" THEN
      MATCH_MP_TAC PDE_LOP0_ATERM THEN
      MAP_EVERY EXISTS_TAC [`p:num`; `B:real^N->num->real^K^K`; `C:real^N->real^K^K`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum(1..dimindex(:N))
           (\i. iterated_partial l
                  (\x. (B:real^N->num->real^K^K) x i **
                       partial_derivative i (w:real^N->real^K) x) x))
    <= &(dimindex(:N)) * c`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. c:real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "c" THEN
      MATCH_MP_TAC PDE_LOP0_BTERM THEN
      MAP_EVERY EXISTS_TAC [`p:num`; `A:real^N->real^N^N`; `C:real^N->real^K^K`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(iterated_partial l (\x. (C:real^N->real^K^K) x ** (w:real^N->real^K) x) x) <= c`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC PDE_LOP0_CTERM THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N) * dimindex(:N)) * c + &(dimindex(:N)) * c + c` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(a1 - a2) <= x /\ norm(b1) <= y /\ norm(c1) <= z
      ==> norm((a1 + (b1 + c1)) - a2:real^K) <= x + y + z`) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A smoothness tactic for real integrands, AM-GM, the pointwise             *)
(* inequalities behind the energy estimates (ellipticity and the coupling of *)
(* gradients through a matrix), and integration by parts for                 *)
(* a scalar-coefficient second-order term.                                   *)
(* ========================================================================= *)

(* Smoothness on (:real^N) of real integrands built from dot products,       *)
(* squared norms, sums, products, differences and negations, and of vector   *)
(* maps built from vsums, sums, differences, negations, scalar and matrix    *)
(* multiples; atoms are closed by the assumptions and the partial-derivative *)
(* closure lemmas.                                                           *)

let rec PDE_TL_SMOOTH_TAC g =
  (REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
   FIRST
    [MATCH_ACCEPT_TAC SMOOTH_MAP_ON_CONST;
     ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; SMOOTH_MAP_ON_ITERATED_PARTIAL;
                  OPEN_UNIV; ETA_AX] THEN NO_TAC;
     MATCH_MP_TAC PDE_SMOOTH_DOT THEN CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC PDE_SMOOTH_SQNORM THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC PDE_SMOOTH_SCALAR_MUL THEN CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
     REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN
     REPEAT STRIP_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN REWRITE_TAC[OPEN_UNIV] THEN
     CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC PDE_SMOOTH_LIFT_ADD_REAL THEN REWRITE_TAC[OPEN_UNIV] THEN
     CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC PDE_SMOOTH_LIFT_SUB_REAL THEN REWRITE_TAC[OPEN_UNIV] THEN
     CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC PDE_SMOOTH_LIFT_NEG_REAL THEN REWRITE_TAC[OPEN_UNIV] THEN
     PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
     REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN
     REPEAT STRIP_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
     CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
     CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
     PDE_TL_SMOOTH_TAC;
     MATCH_MP_TAC PDE_SMOOTH_MATRIX_MUL THEN CONJ_TAC THEN PDE_TL_SMOOTH_TAC]) g;;

let PDE_AMGM = prove
 (`!a b d. &0 < d ==> &2 * a * b <= d * a pow 2 + b pow 2 / d`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  SUBGOAL_THEN `(d * a pow 2 + b pow 2 / d) - &2 * a * b = (d * a - b) pow 2 / d`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2]]);;

(* The first-order coefficient terms after integration by parts.           *)

let PDE_DA_POINTWISE = prove
 (`!(dA:num->num->real) M delta (v:real^K) (q:num->real^K).
     &0 <= M /\ &0 < delta /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> abs(dA i j) <= M)
     ==> &2 * abs(sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. dA i j * (v dot q j))))
         <= delta * sum(1..dimindex(:N)) (\i. norm(q i) pow 2) +
            (&(dimindex(:N)) pow 3 * M pow 2 / delta) * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `abs(sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
          (\j. (dA:num->num->real) i j * ((v:real^K) dot (q:num->real^K) j))))
    <= &(dimindex(:N)) * sum(1..dimindex(:N)) (\j. M * norm v * norm(q j))`
  (LABEL_TAC "e2") THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                  (\j. M * norm(v:real^K) * norm((q:num->real^K) j)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs(sum(1..dimindex(:N))
                    (\j. (dA:num->num->real) i j * ((v:real^K) dot (q:num->real^K) j))))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\j. abs((dA:num->num->real) i j *
                                              ((v:real^K) dot (q:num->real^K) j)))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; NORM_CAUCHY_SCHWARZ_ABS];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (&(dimindex(:N)) * sum(1..dimindex(:N))
            (\j. M * norm(v:real^K) * norm((q:num->real^K) j)))
    <= delta * sum(1..dimindex(:N)) (\i. norm(q i) pow 2) +
       (&(dimindex(:N)) pow 3 * M pow 2 / delta) * norm v pow 2`
  (LABEL_TAC "e3") THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. delta * norm((q:num->real^K) i) pow 2 +
                  (&(dimindex(:N)) * M * norm(v:real^K)) pow 2 / delta)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`norm((q:num->real^K) j)`; `&(dimindex(:N)) * M * norm(v:real^K)`;
                     `delta:real`] PDE_AMGM) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG; ADD_SUB] THEN
      REWRITE_TAC[real_div; REAL_POW_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "e2" MP_TAC THEN REMOVE_THEN "e3" MP_TAC THEN REAL_ARITH_TAC);;

(* The pointwise form of the principal part after integration by parts.    *)

let PDE_PRINC_POINTWISE = prove
 (`!(A:real^N^N) (dA:num->num->real) lam M delta (v:real^K) (p:num->real^K).
     (!w. lam * norm w pow 2 <= w dot (A ** w)) /\ &0 <= M /\ &0 < delta /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> abs(dA i j) <= M)
     ==> --(&2) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * (p i dot p j))) -
         &2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. dA i j * (v dot p j)))
         <= (delta - &2 * lam) * sum(1..dimindex(:N)) (\i. norm(p i) pow 2) +
            (&(dimindex(:N)) pow 3 * M pow 2 / delta) * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N^N`; `lam:real`; `p:num->real^K`] PDE_ELLIPTIC_GRAD) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`dA:num->num->real`; `M:real`; `delta:real`; `v:real^K`; `p:num->real^K`]
                PDE_DA_POINTWISE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Gradients coupled through a matrix: the Frobenius norm controls the      *)
(* bilinear form on families of vectors, in AM-GM form.                      *)

let PDE_SUM_LAMBDA_NORM = prove
 (`!(p:num->real^K).
     sum(1..dimindex(:K)) (\k. norm((lambda i. (p i)$k):real^N) pow 2) =
     sum(1..dimindex(:N)) (\i. norm(p i) pow 2)`,
  GEN_TAC THEN REWRITE_TAC[NORM_POW_2; dot] THEN
  SUBGOAL_THEN
   `!k. sum(1..dimindex(:N)) (\i. ((lambda i. ((p:num->real^K) i)$k):real^N)$i *
                                   ((lambda i. (p i)$k):real^N)$i) =
        sum(1..dimindex(:N)) (\i. (p i)$k * (p i)$k)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let PDE_BILIN_GRAD = prove
 (`!(A:real^N^N) theta (p:num->real^K) q.
     &0 < theta
     ==> &2 * abs(sum(1..dimindex(:N))
                    (\i. sum(1..dimindex(:N)) (\j. A$i$j * (p i dot q j))))
         <= theta * sum(1..dimindex(:N)) (\i. norm(p i) pow 2) +
            (norm(vectorize A) pow 2 / theta) * sum(1..dimindex(:N)) (\i. norm(q i) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. ((lambda i. ((p:num->real^K) i)$k):real^N) dot
        ((A:real^N^N) ** ((lambda j. ((q:num->real^K) j)$k):real^N)) =
        sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * ((p i)$k * (q j)$k)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [dot] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N)) (\j. (A:real^N^N)$i$j * ((p:num->real^K) i dot q j))) =
    sum(1..dimindex(:K))
      (\k. ((lambda i. (p i)$k):real^N) dot (A ** ((lambda j. ((q:num->real^K) j)$k):real^N)))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[dot; GSYM SUM_LMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:K))
      (\k. theta * norm((lambda i. ((p:num->real^K) i)$k):real^N) pow 2 +
           (norm(vectorize(A:real^N^N)) pow 2 / theta) *
           norm((lambda j. ((q:num->real^K) j)$k):real^N) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&2 * sum(1..dimindex(:K))
             (\k. abs(((lambda i. ((p:num->real^K) i)$k):real^N) dot
                      ((A:real^N^N) ** ((lambda j. ((q:num->real^K) j)$k):real^N))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[SUM_ABS_NUMSEG] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ABBREV_TAC `P = (lambda i. ((p:num->real^K) i)$k):real^N` THEN
    ABBREV_TAC `Q = (lambda j. ((q:num->real^K) j)$k):real^N` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * norm(P:real^N) * (norm(vectorize(A:real^N^N)) * norm(Q:real^N))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(P:real^N) * norm((A:real^N^N) ** (Q:real^N))` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE];
      MP_TAC(ISPECL [`norm(P:real^N)`; `norm(vectorize(A:real^N^N)) * norm(Q:real^N)`;
                     `theta:real`] PDE_AMGM) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; REAL_POW_MUL] THEN REAL_ARITH_TAC];
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; PDE_SUM_LAMBDA_NORM] THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

(* Integration by parts for v . (a d_i d_j z), a scalar.                     *)

let PDE_CINT_IBP_SCALAR = prove
 (`!(a:real^N->real) (v:real^N->real^K) z i j.
     smooth_map_on (:real^N) (\x. lift(a x)) /\ pde_zper a /\
     smooth_map_on (:real^N) v /\ pde_zper v /\
     smooth_map_on (:real^N) z /\ pde_zper z /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> pde_cint (\x. v x dot (a x % partial_derivative i (partial_derivative j z) x)) =
         --(pde_cint (\x. a x * (partial_derivative i v x dot partial_derivative j z x))) -
         pde_cint (\x. drop(partial_derivative i (\x. lift(a x)) x) *
                       (v x dot partial_derivative j z x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. (a:real^N->real) x % (v:real^N->real^K) x)`
  ASSUME_TAC THENL [MATCH_MP_TAC PDE_SMOOTH_SCALAR_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_zper (\x. (a:real^N->real) x % (v:real^N->real^K) x)` ASSUME_TAC THENL
   [UNDISCH_TAC `pde_zper (a:real^N->real)` THEN UNDISCH_TAC `pde_zper (v:real^N->real^K)` THEN
    REWRITE_TAC[pde_zper] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. partial_derivative i (\x. (a:real^N->real) x % (v:real^N->real^K) x) x =
        a x % partial_derivative i v x + drop(partial_derivative i (\x. lift(a x)) x) % v x`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`i:num`; `\x. lift((a:real^N->real) x)`; `v:real^N->real^K`; `x:real^N`]
                  PARTIAL_DERIVATIVE_MUL) THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`partial_derivative j (z:real^N->real^K)`;
                 `\x. (a:real^N->real) x % (v:real^N->real^K) x`; `i:num`] PDE_CINT_IBP) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; PDE_ZPER_PARTIAL] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. (v:real^N->real^K) x dot
         ((a:real^N->real) x % partial_derivative i (partial_derivative j (z:real^N->real^K)) x)) =
    (\x. partial_derivative i (partial_derivative j z) x dot (a x % v x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DOT_RMUL] THEN GEN_TAC THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. partial_derivative j (z:real^N->real^K) x dot
         ((a:real^N->real) x % partial_derivative i (v:real^N->real^K) x +
          drop(partial_derivative i (\x. lift(a x)) x) % v x)) =
    (\x. a x * (partial_derivative i v x dot partial_derivative j z x) +
         drop(partial_derivative i (\x. lift(a x)) x) * (v x dot partial_derivative j z x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DOT_RADD; DOT_RMUL] THEN GEN_TAC THEN
    BINOP_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. (a:real^N->real) x * (partial_derivative i (v:real^N->real^K) x dot
                               partial_derivative j (z:real^N->real^K) x)`;
    `\x. drop(partial_derivative i (\x. lift((a:real^N->real) x)) x) *
         ((v:real^N->real^K) x dot partial_derivative j (z:real^N->real^K) x)`] PDE_CINT_ADD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The integrated principal part and the fixed-time energy inequality for    *)
(* the operator itself (PDE_FT1):                                            *)
(*   sum_l 2 int D^l u . D^l(L u) <= -(3/2) lam G_m(u) + K E_m(u).          *)
(* ========================================================================= *)

let PDE_FBND_AZPER = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C i j.
     pde_fbnd p M A B C ==> pde_zper (\x. A x$i$j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_fbnd; pde_zper] THEN SIMP_TAC[]);;

let PDE_FBND_ADJET = prove
 (`!p M (A:real^N->real^N^N) (B:real^N->num->real^K^K) C i j k x.
     pde_fbnd p M A B C /\ 1 <= p /\ 1 <= k /\ k <= dimindex(:N)
     ==> abs(drop(partial_derivative k (\x. lift(A x$i$j)) x)) <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`; `i:num`; `j:num`; `[k:num]`; `x:real^N`]
                PDE_FBND_AJET) THEN
  ASM_REWRITE_TAC[LENGTH; ALL; iterated_partial; GSYM NORM_1; GSYM ONE]);;

let PDE_CINT_SUM2 = prove
 (`!(f:num->num->real^N->real) n.
     (!i j. smooth_map_on (:real^N) (\x. lift(f i j x)))
     ==> pde_cint (\x. sum(1..n) (\i. sum(1..n) (\j. f i j x))) =
         sum(1..n) (\i. sum(1..n) (\j. pde_cint (f i j)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i x. sum(1..n) (\j. (f:num->num->real^N->real) i j x)`; `1..n`]
                PDE_CINT_SUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
    ASM_REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\j x. (f:num->num->real^N->real) i j x`; `1..n`] PDE_CINT_SUM) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; ETA_AX]);;

(* Integration by parts of the second-order term against v. *)

let PDE_SECOND_IBP_ID = prove
 (`!(A:real^N->real^N^N) (v:real^N->real^K) z.
     (!i j. smooth_map_on (:real^N) (\x. lift(A x$i$j)) /\ pde_zper (\x. A x$i$j)) /\
     smooth_map_on (:real^N) v /\ pde_zper v /\ smooth_map_on (:real^N) z /\ pde_zper z
     ==> pde_cint (\x. &2 * (v x dot
                     vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                       (\j. A x$i$j % partial_derivative i (partial_derivative j z) x)))) =
         pde_cint (\x. --(&2) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                         (\j. A x$i$j * (partial_derivative i v x dot partial_derivative j z x))) -
                       &2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                         (\j. drop(partial_derivative i (\x. lift(A x$i$j)) x) *
                              (v x dot partial_derivative j z x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. &2 * ((v:real^N->real^K) x dot
         vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
           (\j. (A:real^N->real^N^N) x$i$j %
                partial_derivative i (partial_derivative j (z:real^N->real^K)) x)))) =
    (\x. &2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
           (\j. v x dot (A x$i$j % partial_derivative i (partial_derivative j z) x))))`
  SUBST1_TAC THENL [SIMP_TAC[FUN_EQ_THM; DOT_RSUM; FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. smooth_map_on (:real^N)
            (\x. lift((v:real^N->real^K) x dot
                      ((A:real^N->real^N^N) x$i$j %
                       partial_derivative i (partial_derivative j (z:real^N->real^K)) x)))`
  ASSUME_TAC THENL [REPEAT GEN_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`&2`; `\x. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                 (\j. (v:real^N->real^K) x dot ((A:real^N->real^N^N) x$i$j %
                      partial_derivative i (partial_derivative j (z:real^N->real^K)) x)))`]
   PDE_CINT_CMUL) THEN
  ANTS_TAC THENL [PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\i j x. (v:real^N->real^K) x dot ((A:real^N->real^N^N) x$i$j %
             partial_derivative i (partial_derivative j (z:real^N->real^K)) x)`;
    `dimindex(:N)`] PDE_CINT_SUM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      pde_cint (\x. (v:real^N->real^K) x dot ((A:real^N->real^N^N) x$i$j %
                    partial_derivative i (partial_derivative j (z:real^N->real^K)) x)))) =
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      --(pde_cint (\x. A x$i$j * (partial_derivative i v x dot partial_derivative j z x))) -
      pde_cint (\x. drop(partial_derivative i (\x. lift(A x$i$j)) x) *
                    (v x dot partial_derivative j z x))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_CINT_IBP_SCALAR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. smooth_map_on (:real^N) (\x. lift((A:real^N->real^N^N) x$i$j *
             (partial_derivative i (v:real^N->real^K) x dot
              partial_derivative j (z:real^N->real^K) x))) /\
          smooth_map_on (:real^N) (\x. lift(drop(partial_derivative i (\x. lift(A x$i$j)) x) *
             (v x dot partial_derivative j z x)))`
  ASSUME_TAC THENL [REPEAT GEN_TAC THEN CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. --(&2) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
           (\j. (A:real^N->real^N^N) x$i$j *
                (partial_derivative i (v:real^N->real^K) x dot
                 partial_derivative j (z:real^N->real^K) x)))`;
    `\x. &2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
           (\j. drop(partial_derivative i (\x. lift((A:real^N->real^N^N) x$i$j)) x) *
                ((v:real^N->real^K) x dot partial_derivative j (z:real^N->real^K) x)))`]
   PDE_CINT_SUB) THEN
  ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`--(&2)`;
    `\x. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
           (\j. (A:real^N->real^N^N) x$i$j *
                (partial_derivative i (v:real^N->real^K) x dot
                 partial_derivative j (z:real^N->real^K) x)))`]
   PDE_CINT_CMUL) THEN
  ANTS_TAC THENL [PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`&2`;
    `\x. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
           (\j. drop(partial_derivative i (\x. lift((A:real^N->real^N^N) x$i$j)) x) *
                ((v:real^N->real^K) x dot partial_derivative j (z:real^N->real^K) x)))`]
   PDE_CINT_CMUL) THEN
  ANTS_TAC THENL [PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\i j x. (A:real^N->real^N^N) x$i$j *
             (partial_derivative i (v:real^N->real^K) x dot
              partial_derivative j (z:real^N->real^K) x)`;
    `dimindex(:N)`] PDE_CINT_SUM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\i j x. drop(partial_derivative i (\x. lift((A:real^N->real^N^N) x$i$j)) x) *
             ((v:real^N->real^K) x dot partial_derivative j (z:real^N->real^K) x)`;
    `dimindex(:N)`] PDE_CINT_SUM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_NEG] THEN REAL_ARITH_TAC);;

(* The principal part, integrated by parts and estimated. *)

let PDE_PRINC_INT = prove
 (`!p M lam (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (v:real^N->real^K) delta.
     pde_fcoeff p M lam A B C /\ 1 <= p /\ smooth_map_on (:real^N) v /\ pde_zper v /\
     &0 < delta
     ==> pde_cint (\x. &2 * (v x dot
                     vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                       (\j. A x$i$j % partial_derivative i (partial_derivative j v) x))))
         <= (delta - &2 * lam) *
            pde_cint (\x. sum(1..dimindex(:N)) (\i. norm(partial_derivative i v x) pow 2)) +
            (&(dimindex(:N)) pow 3 * M pow 2 / delta) * pde_cint (\x. norm(v x) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_fcoeff] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL [ASM_MESON_TAC[pde_fbnd]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`] PDE_FBND_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`] PDE_FBND_AZPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`A:real^N->real^N^N`; `v:real^N->real^K`; `v:real^N->real^K`]
                PDE_SECOND_IBP_ID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_cint (\x. (delta - &2 * lam) *
                  sum(1..dimindex(:N)) (\i. norm(partial_derivative i (v:real^N->real^K) x) pow 2) +
                  (&(dimindex(:N)) pow 3 * M pow 2 / delta) * norm(v x) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_CINT_LE THEN REPEAT CONJ_TAC THENL
     [PDE_TL_SMOOTH_TAC; PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_PRINC_POINTWISE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FBND_ADJET THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `B:real^N->num->real^K^K`; `C:real^N->real^K^K`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL
     [`\x. (delta - &2 * lam) *
           sum(1..dimindex(:N)) (\i. norm(partial_derivative i (v:real^N->real^K) x) pow 2)`;
      `\x. (&(dimindex(:N)) pow 3 * M pow 2 / delta) * norm((v:real^N->real^K) x) pow 2`]
     PDE_CINT_ADD) THEN
    ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    BINOP_TAC THEN MATCH_MP_TAC PDE_CINT_CMUL THEN PDE_TL_SMOOTH_TAC]);;

(* The remainder against the jet, in AM-GM form. *)

let PDE_JET_AMGM = prove
 (`!(u:real^N->real^K) (v:real^K) (r:real^K) c eta k x.
     &0 <= c /\ &0 < eta /\ norm r <= c * pde_jetn k u x
     ==> &2 * (v dot r) <=
         eta * sum (pde_index_lists k (:N)) (\l. norm(iterated_partial l u x) pow 2) +
         &(CARD(pde_index_lists k (:N))) * (c pow 2 / eta) * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * norm(v:real^K) * (c * pde_jetn k (u:real^N->real^K) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(v:real^K) * norm(r:real^K)` THEN
    CONJ_TAC THENL
     [MESON_TAC[REAL_ABS_LE; NORM_CAUCHY_SCHWARZ_ABS; REAL_LE_TRANS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[pde_jetn] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists k (:N))
                (\l. eta * norm(iterated_partial l (u:real^N->real^K) x) pow 2 +
                     (c * norm(v:real^K)) pow 2 / eta)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`norm(iterated_partial l (u:real^N->real^K) x)`; `c * norm(v:real^K)`;
                   `eta:real`] PDE_AMGM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN
    REWRITE_TAC[real_div; REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

(* One index list. *)

let PDE_FT1_L = prove
 (`!m M lam (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K) l theta eta.
     pde_fcoeff (m + 1) M lam A B C /\ smooth_map_on (:real^N) u /\ pde_zper u /\
     l IN pde_index_lists m (:N) /\ &0 < theta /\ &0 < eta
     ==> pde_cint (\x. &2 * (iterated_partial l u x dot
                             iterated_partial l (pde_lop0 A B C u) x))
         <= (theta - &2 * lam) *
            pde_cint (\x. sum(1..dimindex(:N))
                            (\i. norm(partial_derivative i (iterated_partial l u) x) pow 2)) +
            (&(dimindex(:N)) pow 3 * M pow 2 / theta +
             &(CARD(pde_index_lists (m + 1) (:N))) *
             (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta) *
            pde_cint (\x. norm(iterated_partial l u x) pow 2) +
            eta * pde_hs2 (m + 1) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_fcoeff]) THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL [ASM_MESON_TAC[pde_fbnd]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(l:num list) <= m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:num list) IN pde_index_lists m (:N)` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (iterated_partial l (u:real^N->real^K)) /\
    pde_zper (iterated_partial l u) /\
    smooth_map_on (:real^N)
      (iterated_partial l (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C u))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_UNIV; PDE_ZPER_ITERATED_PARTIAL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC PDE_LOP0_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`m + 1`; `M:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_FBND_SMOOTH) THEN
  SUBGOAL_THEN
   `(\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
               iterated_partial l (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C u)
                 x)) =
    (\x. &2 * (iterated_partial l u x dot
               vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u))
                                  x))) +
         &2 * (iterated_partial l u x dot
               (iterated_partial l (pde_lop0 A B C u) x -
                vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u))
                                  x)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_ADD_LDISTRIB; GSYM DOT_RADD] THEN
    REWRITE_TAC[VECTOR_ARITH `(p:real^K) + (a - p) = a`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
               vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. (A:real^N->real^N^N) x$i$j %
                      partial_derivative i (partial_derivative j (iterated_partial l u)) x)))`;
    `\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
               (iterated_partial l
                  (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C u) x -
                vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u))
                                  x))))`]
   PDE_CINT_ADD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!a a' b b' c:real. a <= a' /\ b <= b' /\ a' + b' = c ==> a + b <= c`) THEN
  EXISTS_TAC
   `(theta - &2 * lam) *
    pde_cint (\x. sum(1..dimindex(:N))
                    (\i. norm(partial_derivative i (iterated_partial l (u:real^N->real^K)) x)
                         pow 2)) +
    (&(dimindex(:N)) pow 3 * M pow 2 / theta) * pde_cint (\x. norm(iterated_partial l u x) pow 2)` THEN
  EXISTS_TAC
   `eta * pde_hs2 (m + 1) (u:real^N->real^K) +
    &(CARD(pde_index_lists (m + 1) (:N))) *
    (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta *
    pde_cint (\x. norm(iterated_partial l u x) pow 2)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_PRINC_INT THEN
    MAP_EVERY EXISTS_TAC [`m + 1`; `B:real^N->num->real^K^K`; `C:real^N->real^K^K`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC;
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_cint (\x. eta * sum (pde_index_lists (m + 1) (:N))
                             (\l'. norm(iterated_partial l' (u:real^N->real^K) x) pow 2) +
                  &(CARD(pde_index_lists (m + 1) (:N))) *
                  (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta *
                  norm(iterated_partial l u x) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_CINT_LE THEN REPEAT CONJ_TAC THENL
     [PDE_TL_SMOOTH_TAC; PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_JET_AMGM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) *
                &2 pow (LENGTH(l:num list)) * M *
                pde_jetn (LENGTH l + 1) (u:real^N->real^K) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_LOP0_COMM THEN EXISTS_TAC `m + 1` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[PDE_JETN_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MP_TAC(ISPECL
   [`\x. eta * sum (pde_index_lists (m + 1) (:N))
                   (\l'. norm(iterated_partial l' (u:real^N->real^K) x) pow 2)`;
    `\x. &(CARD(pde_index_lists (m + 1) (:N))) *
         (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta *
         norm(iterated_partial l (u:real^N->real^K) x) pow 2`] PDE_CINT_ADD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THENL
   [MP_TAC(ISPECL
     [`eta:real`; `\x. sum (pde_index_lists (m + 1) (:N))
                          (\l'. norm(iterated_partial l' (u:real^N->real^K) x) pow 2)`]
     PDE_CINT_CMUL) THEN
    ANTS_TAC THENL [PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\l' x. norm(iterated_partial l' (u:real^N->real^K) x) pow 2`;
                   `pde_index_lists (m + 1) (:N)`] PDE_CINT_SUM) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN REPEAT STRIP_TAC THEN PDE_TL_SMOOTH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PDE_HS2_CINT];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC PDE_CINT_CMUL THEN PDE_TL_SMOOTH_TAC]);;

(* Sums of the squared gradients of D^l u are the G_m norm. *)

let PDE_GSQ_SUM = prove
 (`!m (u:real^N->real^K).
     smooth_map_on (:real^N) u
     ==> sum (pde_index_lists m (:N))
             (\l. pde_cint (\x. sum(1..dimindex(:N))
                     (\i. norm(partial_derivative i (iterated_partial l u) x) pow 2))) =
         sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i u))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_HS2_CINT] THEN
  SUBGOAL_THEN
   `!l. l IN pde_index_lists m (:N)
        ==> pde_cint (\x. sum(1..dimindex(:N))
               (\i. norm(partial_derivative i (iterated_partial l (u:real^N->real^K)) x)
                    pow 2)) =
            sum(1..dimindex(:N))
               (\i. pde_cint (\x. norm(iterated_partial l (partial_derivative i u) x) pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\i x. norm(partial_derivative i (iterated_partial l (u:real^N->real^K)) x) pow 2`;
      `1..dimindex(:N)`] PDE_CINT_SUM) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM PDE_ITERATED_PARTIAL_COMM1];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists m (:N))
                (\l. sum(1..dimindex(:N))
                  (\i. pde_cint (\x. norm(iterated_partial l
                         (partial_derivative i (u:real^N->real^K)) x) pow 2)))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\l i. pde_cint (\x. norm(iterated_partial l
                         (partial_derivative i (u:real^N->real^K)) x) pow 2)`;
                 `pde_index_lists m (:N)`; `1..dimindex(:N)`] SUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;

(* FT1: the energy inequality for the operator, summed over the lists. *)

let PDE_FT1 = prove
 (`!m M lam.
     &0 < lam
     ==> ?K. !(A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K).
               pde_fcoeff (m + 1) M lam A B C /\ smooth_map_on (:real^N) u /\ pde_zper u
               ==> sum (pde_index_lists m (:N))
                       (\l. pde_cint (\x. &2 * (iterated_partial l u x dot
                                               iterated_partial l (pde_lop0 A B C u) x)))
                   <= --(&3 / &2 * lam) *
                      sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i u)) +
                      K * pde_hs2 m u`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `nm = &(CARD(pde_index_lists m (:N)))` THEN
  SUBGOAL_THEN `&0 < nm` ASSUME_TAC THENL
   [EXPAND_TAC "nm" THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
    SIMP_TAC[CARD_EQ_0; PDE_INDEX_LISTS_FINITE] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `[]:num list` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0];
    ALL_TAC] THEN
  EXISTS_TAC `(&(dimindex(:N)) pow 3 * M pow 2 / (lam / &4) +
               &(CARD(pde_index_lists (m + 1) (:N))) *
               (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 /
               (lam / &4 / nm)) + lam / &4` THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists m (:N))
      (\l. (lam / &4 - &2 * lam) *
           pde_cint (\x. sum(1..dimindex(:N))
             (\i. norm(partial_derivative i (iterated_partial l (u:real^N->real^K)) x)
                  pow 2)) +
           (&(dimindex(:N)) pow 3 * M pow 2 / (lam / &4) +
            &(CARD(pde_index_lists (m + 1) (:N))) *
            (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 /
            (lam / &4 / nm)) *
           pde_cint (\x. norm(iterated_partial l u x) pow 2) +
           lam / &4 / nm * pde_hs2 (m + 1) u)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_FT1_L THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; PDE_INDEX_LISTS_FINITE] THEN
  SIMP_TAC[SUM_LMUL] THEN
  SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN
  ASM_SIMP_TAC[PDE_GSQ_SUM] THEN
  REWRITE_TAC[GSYM PDE_HS2_CINT] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lam / &4 / nm * nm * pde_hs2 (m + 1) (u:real^N->real^K) =
                lam / &4 * pde_hs2 (m + 1) u` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < nm` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM ADD1; PDE_HS2_SUC] THEN
  MP_TAC(ISPECL [`0`; `m:num`; `u:real^N->real^K`] PDE_HS2_MONO) THEN
  ASM_REWRITE_TAC[LE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lam / &4 * pde_hs2 0 (u:real^N->real^K) <= lam / &4 * pde_hs2 m u`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The fixed-time energy inequalities for a second operator applied to       *)
(* another map (PDE_FT2; its principal part only through the sup of the      *)
(* Frobenius norm of its matrix) and for a forcing term, with the gain of    *)
(* one derivative (PDE_FT3).                                                 *)
(* ========================================================================= *)

let PDE_COUPLE_POINTWISE = prove
 (`!(A:real^N^N) (dA:num->num->real) a2 M theta eps (v:real^K) (p:num->real^K) q.
     norm(vectorize A) <= a2 /\ &0 <= M /\ &0 < theta /\ &0 < eps /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> abs(dA i j) <= M)
     ==> --(&2) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * (p i dot q j))) -
         &2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. dA i j * (v dot q j)))
         <= theta * sum(1..dimindex(:N)) (\i. norm(p i) pow 2) +
            (a2 pow 2 / theta + eps) * sum(1..dimindex(:N)) (\i. norm(q i) pow 2) +
            (&(dimindex(:N)) pow 3 * M pow 2 / eps) * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N^N`; `theta:real`; `p:num->real^K`; `q:num->real^K`]
                PDE_BILIN_GRAD) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`dA:num->num->real`; `M:real`; `eps:real`; `v:real^K`; `q:num->real^K`]
                PDE_DA_POINTWISE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `norm(vectorize(A:real^N^N)) pow 2 / theta *
    sum(1..dimindex(:N)) (\i. norm((q:num->real^K) i) pow 2) <=
    a2 pow 2 / theta * sum(1..dimindex(:N)) (\i. norm(q i) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let PDE_COUPLE_INT = prove
 (`!p M a2 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (v:real^N->real^K) z theta eps.
     pde_fbnd p M A B C /\ 1 <= p /\ (!x. norm(vectorize(A x)) <= a2) /\
     smooth_map_on (:real^N) v /\ pde_zper v /\ smooth_map_on (:real^N) z /\ pde_zper z /\
     &0 < theta /\ &0 < eps
     ==> pde_cint (\x. &2 * (v x dot
                     vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                       (\j. A x$i$j % partial_derivative i (partial_derivative j z) x))))
         <= theta *
            pde_cint (\x. sum(1..dimindex(:N)) (\i. norm(partial_derivative i v x) pow 2)) +
            (a2 pow 2 / theta + eps) *
            pde_cint (\x. sum(1..dimindex(:N)) (\i. norm(partial_derivative i z x) pow 2)) +
            (&(dimindex(:N)) pow 3 * M pow 2 / eps) * pde_cint (\x. norm(v x) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL [ASM_MESON_TAC[pde_fbnd]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`] PDE_FBND_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:num`; `M:real`; `A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                 `C:real^N->real^K^K`] PDE_FBND_AZPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`A:real^N->real^N^N`; `v:real^N->real^K`; `z:real^N->real^K`]
                PDE_SECOND_IBP_ID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_cint (\x. theta *
                  sum(1..dimindex(:N)) (\i. norm(partial_derivative i (v:real^N->real^K) x) pow 2) +
                  (a2 pow 2 / theta + eps) *
                  sum(1..dimindex(:N)) (\i. norm(partial_derivative i (z:real^N->real^K) x) pow 2) +
                  (&(dimindex(:N)) pow 3 * M pow 2 / eps) * norm(v x) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_CINT_LE THEN REPEAT CONJ_TAC THENL
     [PDE_TL_SMOOTH_TAC; PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_COUPLE_POINTWISE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FBND_ADJET THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `B:real^N->num->real^K^K`; `C:real^N->real^K^K`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL
     [`\x. theta *
           sum(1..dimindex(:N)) (\i. norm(partial_derivative i (v:real^N->real^K) x) pow 2)`;
      `\x. (a2 pow 2 / theta + eps) *
           sum(1..dimindex(:N)) (\i. norm(partial_derivative i (z:real^N->real^K) x) pow 2) +
           (&(dimindex(:N)) pow 3 * M pow 2 / eps) * norm((v:real^N->real^K) x) pow 2`]
     PDE_CINT_ADD) THEN
    ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL
     [`\x. (a2 pow 2 / theta + eps) *
           sum(1..dimindex(:N)) (\i. norm(partial_derivative i (z:real^N->real^K) x) pow 2)`;
      `\x. (&(dimindex(:N)) pow 3 * M pow 2 / eps) * norm((v:real^N->real^K) x) pow 2`]
     PDE_CINT_ADD) THEN
    ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN
    MATCH_MP_TAC PDE_CINT_CMUL THEN PDE_TL_SMOOTH_TAC]);;

(* One index list, and the sum over the lists. *)

let PDE_FT2_L = prove
 (`!m M a2 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K) w l
    theta eps eta.
     pde_fbnd (m + 1) M A B C /\ (!x. norm(vectorize(A x)) <= a2) /\
     smooth_map_on (:real^N) u /\ pde_zper u /\ smooth_map_on (:real^N) w /\ pde_zper w /\
     l IN pde_index_lists m (:N) /\ &0 < theta /\ &0 < eps /\ &0 < eta
     ==> pde_cint (\x. &2 * (iterated_partial l u x dot
                             iterated_partial l (pde_lop0 A B C w) x))
         <= theta *
            pde_cint (\x. sum(1..dimindex(:N))
                            (\i. norm(partial_derivative i (iterated_partial l u) x) pow 2)) +
            (a2 pow 2 / theta + eps) *
            pde_cint (\x. sum(1..dimindex(:N))
                            (\i. norm(partial_derivative i (iterated_partial l w) x) pow 2)) +
            (&(dimindex(:N)) pow 3 * M pow 2 / eps +
             &(CARD(pde_index_lists (m + 1) (:N))) *
             (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta) *
            pde_cint (\x. norm(iterated_partial l u x) pow 2) +
            eta * pde_hs2 (m + 1) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL [ASM_MESON_TAC[pde_fbnd]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(l:num list) <= m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:num list) IN pde_index_lists m (:N)` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (iterated_partial l (u:real^N->real^K)) /\
    pde_zper (iterated_partial l u) /\
    smooth_map_on (:real^N) (iterated_partial l (w:real^N->real^K)) /\
    pde_zper (iterated_partial l w) /\
    smooth_map_on (:real^N)
      (iterated_partial l (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C w))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_UNIV; PDE_ZPER_ITERATED_PARTIAL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC PDE_LOP0_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`m + 1`; `M:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_FBND_SMOOTH) THEN
  SUBGOAL_THEN
   `(\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
               iterated_partial l (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C
                                     (w:real^N->real^K)) x)) =
    (\x. &2 * (iterated_partial l u x dot
               vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l w))
                                  x))) +
         &2 * (iterated_partial l u x dot
               (iterated_partial l (pde_lop0 A B C w) x -
                vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l w))
                                  x)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_ADD_LDISTRIB; GSYM DOT_RADD] THEN
    REWRITE_TAC[VECTOR_ARITH `(p:real^K) + (a - p) = a`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
               vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. (A:real^N->real^N^N) x$i$j %
                      partial_derivative i (partial_derivative j
                        (iterated_partial l (w:real^N->real^K))) x)))`;
    `\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
               (iterated_partial l
                  (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C
                            (w:real^N->real^K)) x -
                vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                 (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l w))
                                  x))))`]
   PDE_CINT_ADD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a a' b b' c:real. a <= a' /\ b <= b' /\ a' + b' = c ==> a + b <= c`) THEN
  EXISTS_TAC
   `theta *
    pde_cint (\x. sum(1..dimindex(:N))
                    (\i. norm(partial_derivative i (iterated_partial l (u:real^N->real^K)) x)
                         pow 2)) +
    (a2 pow 2 / theta + eps) *
    pde_cint (\x. sum(1..dimindex(:N))
                    (\i. norm(partial_derivative i (iterated_partial l (w:real^N->real^K)) x)
                         pow 2)) +
    (&(dimindex(:N)) pow 3 * M pow 2 / eps) *
    pde_cint (\x. norm(iterated_partial l u x) pow 2)` THEN
  EXISTS_TAC
   `eta * pde_hs2 (m + 1) (w:real^N->real^K) +
    &(CARD(pde_index_lists (m + 1) (:N))) *
    (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta *
    pde_cint (\x. norm(iterated_partial l (u:real^N->real^K) x) pow 2)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_COUPLE_INT THEN
    MAP_EVERY EXISTS_TAC [`m + 1`; `B:real^N->num->real^K^K`; `C:real^N->real^K^K`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC;
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_cint (\x. eta * sum (pde_index_lists (m + 1) (:N))
                             (\l'. norm(iterated_partial l' (w:real^N->real^K) x) pow 2) +
                  &(CARD(pde_index_lists (m + 1) (:N))) *
                  (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta *
                  norm(iterated_partial l (u:real^N->real^K) x) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_CINT_LE THEN REPEAT CONJ_TAC THENL
     [PDE_TL_SMOOTH_TAC; PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_JET_AMGM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) *
                &2 pow (LENGTH(l:num list)) * M *
                pde_jetn (LENGTH l + 1) (w:real^N->real^K) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_LOP0_COMM THEN EXISTS_TAC `m + 1` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[PDE_JETN_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MP_TAC(ISPECL
   [`\x. eta * sum (pde_index_lists (m + 1) (:N))
                   (\l'. norm(iterated_partial l' (w:real^N->real^K) x) pow 2)`;
    `\x. &(CARD(pde_index_lists (m + 1) (:N))) *
         (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 / eta *
         norm(iterated_partial l (u:real^N->real^K) x) pow 2`] PDE_CINT_ADD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THENL
   [MP_TAC(ISPECL
     [`eta:real`; `\x. sum (pde_index_lists (m + 1) (:N))
                          (\l'. norm(iterated_partial l' (w:real^N->real^K) x) pow 2)`]
     PDE_CINT_CMUL) THEN
    ANTS_TAC THENL [PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\l' x. norm(iterated_partial l' (w:real^N->real^K) x) pow 2`;
                   `pde_index_lists (m + 1) (:N)`] PDE_CINT_SUM) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN REPEAT STRIP_TAC THEN PDE_TL_SMOOTH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PDE_HS2_CINT];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC PDE_CINT_CMUL THEN PDE_TL_SMOOTH_TAC]);;

let PDE_FT2 = prove
 (`!m M a2 theta eps.
     &0 < theta /\ &0 < eps
     ==> ?K. !(A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K) w.
               pde_fbnd (m + 1) M A B C /\ (!x. norm(vectorize(A x)) <= a2) /\
               smooth_map_on (:real^N) u /\ pde_zper u /\
               smooth_map_on (:real^N) w /\ pde_zper w
               ==> sum (pde_index_lists m (:N))
                       (\l. pde_cint (\x. &2 * (iterated_partial l u x dot
                                               iterated_partial l (pde_lop0 A B C w) x)))
                   <= theta * sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i u)) +
                      (a2 pow 2 / theta + eps) *
                      sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i w)) +
                      K * (pde_hs2 m u + pde_hs2 m w)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `nm = &(CARD(pde_index_lists m (:N)))` THEN
  SUBGOAL_THEN `&0 < nm` ASSUME_TAC THENL
   [EXPAND_TAC "nm" THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
    SIMP_TAC[CARD_EQ_0; PDE_INDEX_LISTS_FINITE] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `[]:num list` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0];
    ALL_TAC] THEN
  ABBREV_TAC
   `K1 = &(dimindex(:N)) pow 3 * M pow 2 / (eps / &2) +
         &(CARD(pde_index_lists (m + 1) (:N))) *
         (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * &2 pow m * M) pow 2 /
         (eps / &2 / nm)` THEN
  EXISTS_TAC `abs K1 + eps / &2` THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists m (:N))
      (\l. theta *
           pde_cint (\x. sum(1..dimindex(:N))
             (\i. norm(partial_derivative i (iterated_partial l (u:real^N->real^K)) x)
                  pow 2)) +
           (a2 pow 2 / theta + eps / &2) *
           pde_cint (\x. sum(1..dimindex(:N))
             (\i. norm(partial_derivative i (iterated_partial l (w:real^N->real^K)) x)
                  pow 2)) +
           K1 * pde_cint (\x. norm(iterated_partial l u x) pow 2) +
           eps / &2 / nm * pde_hs2 (m + 1) w)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "K1" THEN
    MATCH_MP_TAC PDE_FT2_L THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; PDE_INDEX_LISTS_FINITE] THEN
  SIMP_TAC[SUM_LMUL] THEN
  SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN
  ASM_SIMP_TAC[PDE_GSQ_SUM] THEN
  REWRITE_TAC[GSYM PDE_HS2_CINT] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `eps / &2 / nm * nm * pde_hs2 (m + 1) (w:real^N->real^K) =
                eps / &2 * pde_hs2 (m + 1) w` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < nm` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM ADD1; PDE_HS2_SUC] THEN
  MP_TAC(ISPECL [`0`; `m:num`; `w:real^N->real^K`] PDE_HS2_MONO) THEN
  ASM_REWRITE_TAC[LE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= pde_hs2 m (u:real^N->real^K) /\ &0 <= pde_hs2 m (w:real^N->real^K)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[PDE_HS2_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `K1 * pde_hs2 m (u:real^N->real^K) <= abs K1 * pde_hs2 m u` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs K1 * pde_hs2 m (w:real^N->real^K)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `eps / &2 * pde_hs2 0 (w:real^N->real^K) <= eps / &2 * pde_hs2 m w` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps / &2 * pde_hs2 m (u:real^N->real^K)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Sums over the index lists of length at most SUC s. *)

let PDE_SUM_INDEX_LISTS_SUC = prove
 (`!s (f:num list->real).
     sum (pde_index_lists (SUC s) (:N)) f =
     f [] + sum(1..dimindex(:N)) (\i. sum (pde_index_lists s (:N)) (\l. f (APPEND l [i])))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PDE_INDEX_LISTS_SUC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_IMAGE; FINITE_CROSS; FINITE_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN
  REWRITE_TAC[IN_IMAGE; prove(`!(l:num list) i. ~([] = APPEND l [i])`,
                               MESON_TAC[APPEND_EQ_NIL; NOT_CONS_NIL])] THEN
  AP_TERM_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) SUM_IMAGE (lhand w))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; FST; SND; PDE_APPEND_SING_INJ; PAIR_EQ] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN
  REWRITE_TAC[GSYM CROSS] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let PDE_SQ_TERM_LE = prove
 (`!(p:num->real^K) i.
     1 <= i /\ i <= dimindex(:N)
     ==> norm(p i) pow 2 <= sum(1..dimindex(:N)) (\k. norm(p k) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. norm((p:num->real^K) k) pow 2`;
                 `sum(1..dimindex(:N)) (\k. norm((p:num->real^K) k) pow 2)`;
                 `1..dimindex(:N)`] SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; REAL_LE_POW_2; IN_NUMSEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The forcing against a list ending with i: one derivative moves over.    *)

let PDE_FT3_TERM = prove
 (`!(u:real^N->real^K) ff l i theta.
     smooth_map_on (:real^N) u /\ pde_zper u /\ smooth_map_on (:real^N) ff /\ pde_zper ff /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ 1 <= i /\ i <= dimindex(:N) /\ &0 < theta
     ==> pde_cint (\x. &2 * (iterated_partial (APPEND l [i]) u x dot
                             iterated_partial (APPEND l [i]) ff x))
         <= theta * pde_cint (\x. sum(1..dimindex(:N))
                    (\k. norm(partial_derivative k (iterated_partial (APPEND l [i]) u) x)
                         pow 2)) +
            inv theta * pde_cint (\x. norm(iterated_partial l ff x) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `iterated_partial (APPEND l [i]) (ff:real^N->real^K) =
                partial_derivative i (iterated_partial l ff)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    MATCH_MP_TAC PDE_ITERATED_PARTIAL_COMM1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = iterated_partial (APPEND l [i]) (u:real^N->real^K)` THEN
  ABBREV_TAC `Y = iterated_partial l (ff:real^N->real^K)` THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (X:real^N->real^K) /\ pde_zper X /\
    smooth_map_on (:real^N) (Y:real^N->real^K) /\ pde_zper Y`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_UNIV; PDE_ZPER_ITERATED_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_cint (\x. &2 * ((X:real^N->real^K) x dot partial_derivative i (Y:real^N->real^K) x)) =
    pde_cint (\x. --(&2) * (Y x dot partial_derivative i X x))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`Y:real^N->real^K`; `X:real^N->real^K`; `i:num`] PDE_CINT_IBP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\x. &2 * ((X:real^N->real^K) x dot partial_derivative i (Y:real^N->real^K) x)) =
      (\x. &2 * (partial_derivative i Y x dot X x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC DOT_SYM;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`&2`; `\x. partial_derivative i (Y:real^N->real^K) x dot
                              (X:real^N->real^K) x`] PDE_CINT_CMUL) THEN
    ANTS_TAC THENL [PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`--(&2)`; `\x. (Y:real^N->real^K) x dot
                                 partial_derivative i (X:real^N->real^K) x`] PDE_CINT_CMUL) THEN
    ANTS_TAC THENL [PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_cint (\x. theta * sum(1..dimindex(:N))
                    (\k. norm(partial_derivative k (X:real^N->real^K) x) pow 2) +
                  inv theta * norm((Y:real^N->real^K) x) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_CINT_LE THEN REPEAT CONJ_TAC THENL
     [PDE_TL_SMOOTH_TAC; PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`norm(partial_derivative i (X:real^N->real^K) x)`;
                   `norm((Y:real^N->real^K) x)`; `theta:real`] PDE_AMGM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `theta * norm(partial_derivative i (X:real^N->real^K) x) pow 2 <=
      theta * sum(1..dimindex(:N)) (\k. norm(partial_derivative k X x) pow 2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MP_TAC(ISPECL [`\k. partial_derivative k (X:real^N->real^K) x`; `i:num`]
                    PDE_SQ_TERM_LE) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(Y:real^N->real^K) x`; `partial_derivative i (X:real^N->real^K) x`]
                  NORM_CAUCHY_SCHWARZ_ABS) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL
     [`\x. theta * sum(1..dimindex(:N))
             (\k. norm(partial_derivative k (X:real^N->real^K) x) pow 2)`;
      `\x. inv theta * norm((Y:real^N->real^K) x) pow 2`] PDE_CINT_ADD) THEN
    ANTS_TAC THENL [CONJ_TAC THEN PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    BINOP_TAC THEN MATCH_MP_TAC PDE_CINT_CMUL THEN PDE_TL_SMOOTH_TAC]);;

(* FT3: the forcing, with the gain of one derivative. *)

let PDE_FT3 = prove
 (`!m theta.
     &0 < theta
     ==> ?K. !(u:real^N->real^K) ff.
               smooth_map_on (:real^N) u /\ pde_zper u /\
               smooth_map_on (:real^N) ff /\ pde_zper ff
               ==> sum (pde_index_lists (SUC m) (:N))
                       (\l. pde_cint (\x. &2 * (iterated_partial l u x dot
                                               iterated_partial l ff x)))
                   <= theta *
                      sum(1..dimindex(:N)) (\i. pde_hs2 (SUC m) (partial_derivative i u)) +
                      K * (pde_hs2 (SUC m) u + pde_hs2 m ff)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `&1 + &(dimindex(:N)) / theta` THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PDE_SUM_INDEX_LISTS_SUC] THEN
  SUBGOAL_THEN
   `pde_cint (\x. &2 * (iterated_partial [] (u:real^N->real^K) x dot
                        iterated_partial [] (ff:real^N->real^K) x))
    <= pde_hs2 0 u + pde_hs2 0 ff`
  (LABEL_TAC "t0") THENL
   [REWRITE_TAC[iterated_partial; PDE_HS2_0; GSYM pde_cint] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_cint (\x. norm((u:real^N->real^K) x) pow 2 +
                              norm((ff:real^N->real^K) x) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_CINT_LE THEN REPEAT CONJ_TAC THENL
       [PDE_TL_SMOOTH_TAC; PDE_TL_SMOOTH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`norm((u:real^N->real^K) x)`; `norm((ff:real^N->real^K) x)`; `&1`]
                    PDE_AMGM) THEN
      MP_TAC(ISPECL [`(u:real^N->real^K) x`; `(ff:real^N->real^K) x`]
                    NORM_CAUCHY_SCHWARZ_ABS) THEN
      REWRITE_TAC[REAL_DIV_1; REAL_MUL_LID; REAL_LT_01] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PDE_CINT_ADD THEN
      CONJ_TAC THEN PDE_TL_SMOOTH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum (pde_index_lists m (:N)) (\l.
      pde_cint (\x. &2 * (iterated_partial (APPEND l [i]) (u:real^N->real^K) x dot
                          iterated_partial (APPEND l [i]) (ff:real^N->real^K) x))))
    <= theta * (sum(1..dimindex(:N)) (\i. pde_hs2 (SUC m) (partial_derivative i u)) -
                pde_cint (\x. sum(1..dimindex(:N))
                                (\k. norm(partial_derivative k u x) pow 2))) +
       inv theta * (&(dimindex(:N)) * pde_hs2 m ff)`
  (LABEL_TAC "t1") THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:N)) (\i. sum (pde_index_lists m (:N)) (\l.
        theta * pde_cint (\x. sum(1..dimindex(:N))
                  (\k. norm(partial_derivative k
                         (iterated_partial (APPEND l [i]) (u:real^N->real^K)) x) pow 2)) +
        inv theta * pde_cint (\x. norm(iterated_partial l (ff:real^N->real^K) x) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
      X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC PDE_FT3_TERM THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[SUM_ADD; SUM_ADD_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN
    SIMP_TAC[SUM_LMUL] THEN
    REWRITE_TAC[GSYM PDE_HS2_CINT; SUM_CONST_NUMSEG; ADD_SUB] THEN
    MP_TAC(ISPECL
     [`m:num`;
      `\l. pde_cint (\x. sum(1..dimindex(:N))
             (\k. norm(partial_derivative k (iterated_partial l (u:real^N->real^K)) x)
                  pow 2))`] PDE_SUM_INDEX_LISTS_SUC) THEN
    REWRITE_TAC[iterated_partial] THEN
    MP_TAC(ISPECL [`SUC m`; `u:real^N->real^K`] PDE_GSQ_SUM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH `!a b c:real. a = b + c ==> c = a - b`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= pde_cint (\x. sum(1..dimindex(:N))
                         (\k. norm(partial_derivative k (u:real^N->real^K) x) pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_CINT_POS THEN CONJ_TAC THENL
     [PDE_TL_SMOOTH_TAC;
      GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `SUC m`; `u:real^N->real^K`] PDE_HS2_MONO) THEN
  MP_TAC(ISPECL [`0`; `m:num`; `ff:real^N->real^K`] PDE_HS2_MONO) THEN
  ASM_REWRITE_TAC[LE_0] THEN
  SUBGOAL_THEN `&0 <= &(dimindex(:N)) * inv theta * pde_hs2 (SUC m) (u:real^N->real^K)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; PDE_HS2_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= theta * pde_cint (\x. sum(1..dimindex(:N))
                     (\k. norm(partial_derivative k (u:real^N->real^K) x) pow 2))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REMOVE_THEN "t0" MP_TAC THEN REMOVE_THEN "t1" MP_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The time derivative of the H^m energy of the slices of a smooth           *)
(* space-time map, and the time partial of a smooth periodic solution.       *)
(* ========================================================================= *)

let PDE_MAP_SUC_RANGE = prove
 (`!l. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
       ==> ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) (MAP (\k. 1 + k) l)`,
  GEN_TAC THEN REWRITE_TAC[ALL_MAP; o_DEF; PDE_HEAT_DIMINDEX_ST] THEN
  MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN REWRITE_TAC[] THEN ARITH_TAC);;

(* The slices of the time partial and of the space-time iterated partials.  *)

let PDE_SLAB_SLICE_ITERATED = prove
 (`!(FU:real^(1,N)finite_sum->real^K) a b l t y.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) FU /\ a < t /\ t < b /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> iterated_partial l (\y. FU(pastecart (lift t) y)) y =
         iterated_partial (MAP (\k. 1 + k) l) FU (pastecart (lift t) y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ST_SLICE_ITERATED THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
               LIFT_DROP; IN_UNIV]);;

let PDE_HS2_SLICE_DERIV = prove
 (`!(FU:real^(1,N)finite_sum->real^K) a b m t.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) FU /\ a < t /\ t < b
     ==> ((\r. pde_hs2 m (\y. FU(pastecart (lift r) y))) has_real_derivative
          sum (pde_index_lists m (:N))
            (\l. pde_cint (\y. &2 * (iterated_partial l (\y. FU(pastecart (lift t) y)) y dot
                    iterated_partial l (\y. partial_derivative 1 FU (pastecart (lift t) y))
                      y))))
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (:real^N)` THEN
  SUBGOAL_THEN `open (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!w (y:real^N). w IN interval(lift a,lift b) ==> pastecart w y IN S`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[PDE_HS2_CINT] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `L = MAP (\k. 1 + k) (l:num list)` THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) (L:num list)`
  ASSUME_TAC THENL [EXPAND_TAC "L" THEN ASM_SIMP_TAC[PDE_MAP_SUC_RANGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (iterated_partial L (FU:real^(1,N)finite_sum->real^K)) /\
    smooth_map_on S (partial_derivative 1 (FU:real^(1,N)finite_sum->real^K))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  ABBREV_TAC `G = \z. lift(norm(iterated_partial L (FU:real^(1,N)finite_sum->real^K) z) pow 2)` THEN
  SUBGOAL_THEN `smooth_map_on S (G:real^(1,N)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `S:real^(1,N)finite_sum->bool`;
                 `vec 0:real^N`; `vec 1:real^N`; `G:real^(1,N)finite_sum->real^1`]
                NS_PARAM_INTEGRAL_SMOOTH) THEN
  ASM_SIMP_TAC[OPEN_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lift t IN interval(lift a,lift b)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. integral (interval[vec 0,vec 1])
            (\x. (G:real^(1,N)finite_sum->real^1)(pastecart w x))) has_vector_derivative
     partial_derivative 1 (\w. integral (interval[vec 0,vec 1]) (\x. G(pastecart w x)))
       (lift t)) (at (lift t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_HEAT_VDERIV1 THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b)` THEN ASM_REWRITE_TAC[OPEN_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. partial_derivative 1 (G:real^(1,N)finite_sum->real^1) (pastecart (lift t) x) =
               lift(&2 * (iterated_partial L (FU:real^(1,N)finite_sum->real^K)
                            (pastecart (lift t) x) dot
                          partial_derivative 1 (iterated_partial L FU) (pastecart (lift t) x)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[NORM_POW_2] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PDE_PARTIAL_DOT o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[ETA_AX];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ; ETA_AX] THEN
    MP_TAC(ISPECL [`partial_derivative 1 (iterated_partial L (FU:real^(1,N)finite_sum->real^K))
                      (pastecart (lift t) x)`;
                   `iterated_partial L (FU:real^(1,N)finite_sum->real^K) (pastecart (lift t) x)`]
                  DOT_SYM) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\r. drop(integral (interval[vec 0,vec 1])
                        (\x. (G:real^(1,N)finite_sum->real^1)(pastecart (lift r) x)))` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[pde_cint] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN EXPAND_TAC "L" THEN
    MATCH_MP_TAC PDE_SLAB_SLICE_ITERATED THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`abs(r - t) < min (t - a) (b - t)`; `a < t`; `t < b`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `lift o (\r. drop(integral (interval[vec 0,vec 1])
                       (\x. (G:real^(1,N)finite_sum->real^1)(pastecart (lift r) x)))) o drop =
    (\w. integral (interval[vec 0,vec 1]) (\x. G(pastecart w x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative 1
      (\w. integral (interval[vec 0,vec 1])
             (\x. (G:real^(1,N)finite_sum->real^1)(pastecart w x))) (lift t) =
    lift(pde_cint (\y. &2 * (iterated_partial l
                                (\y. (FU:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)) y dot
                             iterated_partial l
                                (\y. partial_derivative 1 FU (pastecart (lift t) y)) y)))`
  (SUBST1_TAC o SYM) THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[pde_cint; LIFT_DROP] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:real^(1,N)finite_sum->real^1`; `lift t`; `x:real^N`]
                PDE_HEAT_TIME_SLICE_PARTIAL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "L" THEN MATCH_MP_TAC PDE_SLAB_SLICE_ITERATED THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `FU:real^(1,N)finite_sum->real^K`; `1`]
                TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `L:num list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (x:real^N)`) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN EXPAND_TAC "L" THEN
  MATCH_MP_TAC PDE_SLAB_SLICE_ITERATED THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[]);;

(* The time partial of the extension of a solution is the equation. *)

let PDE_TSOL_TIME_PARTIAL = prove
 (`!tmax (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f u0 u
    (FU:real^(1,N)finite_sum->real^K) e t y.
     pde_tsol tmax aa bb cc f u0 u /\ &0 < e /\
     smooth_map_on (interval(lift(&0 - e),lift tmax) PCROSS (:real^N)) FU /\
     (!t y. &0 <= t /\ t < tmax ==> FU(pastecart (lift t) y) = u t y) /\
     &0 < t /\ t < tmax
     ==> partial_derivative 1 FU (pastecart (lift t) y) = pde_lop aa bb cc u t y + f t y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pde_tsol]) THEN STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\s. (u:real->real^N->real^K) (drop s) y` THEN EXISTS_TAC `lift t` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\r. (FU:real^(1,N)finite_sum->real^K)(pastecart r y)` THEN
  EXISTS_TAC `min t (tmax - t)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real^1` THEN REWRITE_TAC[dist; NORM_1; DROP_SUB; LIFT_DROP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= drop r /\ drop r < tmax` STRIP_ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < tmax`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_MESON_TAC[LIFT_DROP];
    MATCH_MP_TAC PDE_ST_TIME_DERIV THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift(&0 - e),lift tmax) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP; IN_UNIV] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < tmax`; `&0 < e`] THEN REAL_ARITH_TAC]);;

(* Slices of maps smooth up to t = 0. *)

let PDE_UPTO_SLICE_SMOOTH = prove
 (`!tmax (g:real->real^N->real^K) t.
     pde_upto (&0) tmax (:real^N) g /\ &0 <= t /\ t < tmax
     ==> smooth_map_on (:real^N) (g t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FG:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:real->real^N->real^K) t = (\y. FG(pastecart (lift t) y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_HEAT_SLICE_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`&0 - e`; `tmax:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 <= t`] THEN REAL_ARITH_TAC);;

let PDE_UPTO_JET_BOUND = prove
 (`!tmax (g:real->real^N->real^K) T1 p.
     pde_upto (&0) tmax (:real^N) g /\ (!t. pde_zper (g t)) /\ &0 <= T1 /\ T1 < tmax
     ==> ?A. &0 <= A /\
             !t l y. &0 <= t /\ t <= T1 /\ LENGTH l <= p /\
                     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                     ==> norm(iterated_partial l (g t) y) <= A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pde_upto]) THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < tmax` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= T1`; `T1 < tmax`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`FG:real^(1,N)finite_sum->real^K`; `g:real->real^N->real^K`; `e:real`;
                 `tmax:real`] PDE_HEAT_EXT_ZPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`FG:real^(1,N)finite_sum->real^K`; `e:real`; `tmax:real`; `T1:real`; `p:num`]
                PDE_HEAT_SLAB_JET_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real->real^N->real^K) t = (\y. FG(pastecart (lift t) y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= t`; `t <= T1`; `T1 < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FG:real^(1,N)finite_sum->real^K`; `&0 - e`; `tmax:real`; `l:num list`;
                 `t:real`; `y:real^N`] PDE_SLAB_SLICE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 <= t`; `t <= T1`; `T1 < tmax`] THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[LENGTH_MAP; PDE_MAP_SUC_RANGE]);;

(* Admissible time-dependent coefficients give admissible fixed-time data,  *)
(* uniformly on compact time intervals.                                      *)

let PDE_TCOEFF_FCOEFF = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T1 p.
     pde_tcoeff tmax lam aa bb cc /\ &0 <= T1 /\ T1 < tmax
     ==> ?M. !t. &0 <= t /\ t <= T1 ==> pde_fcoeff p M lam (aa t) (bb t) (cc t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tcoeff] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`;
                 `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((aa:real->real^N->real^N^N) t y)`;
                 `T1:real`; `p:num`] PDE_UPTO_JET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `MA:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tmax:real`;
                 `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                          ((cc:real->real^N->real^K^K) t y)`;
                 `T1:real`; `p:num`] PDE_UPTO_JET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `MC:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. ?A. &0 <= A /\
            !t l y. &0 <= t /\ t <= T1 /\ LENGTH l <= p /\
                    ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                    ==> norm(iterated_partial l
                          (\y. (vectorize:real^K^K->real^(K,K)finite_prod)
                                 ((bb:real->real^N->num->real^K^K) t y i)) y) <= A`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((bb:real->real^N->num->real^K^K) t y i)`;
                   `T1:real`; `p:num`] PDE_UPTO_JET_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
    MP_TAC(ISPECL [`\y. (bb:real->real^N->num->real^K^K) t y i`;
                   `vectorize:real^K^K->real^(K,K)finite_prod`] PDE_ZPER_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `MB:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MA + sum(1..dimindex(:N)) MB + MC` THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) MB` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t < tmax` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`t <= T1`; `T1 < tmax`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pde_fcoeff; pde_fbnd] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= MA`; `&0 <= MC`; `&0 <= sum(1..dimindex(:N)) MB`] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((aa:real->real^N->real^N^N) t y)`; `t:real`]
                  PDE_UPTO_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((bb:real->real^N->num->real^K^K) t y i)`; `t:real`]
                  PDE_UPTO_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX];
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((cc:real->real^N->real^K^K) t y)`; `t:real`]
                  PDE_UPTO_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX];
    MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^N`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `MA:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `l:num list`; `x:real^N`] o
          check (fun th -> can (find_term ((=) `MA:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX];
        MAP_EVERY UNDISCH_TAC [`&0 <= MC`; `&0 <= sum(1..dimindex(:N)) MB`] THEN
        REAL_ARITH_TAC];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(MB:num->real) i` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`MB:num->real`; `sum(1..dimindex(:N)) MB`; `1..dimindex(:N)`]
                      SUM_POS_BOUND) THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`&0 <= MA`; `&0 <= MC`] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `MC:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `l:num list`; `x:real^N`] o
          check (fun th -> can (find_term ((=) `MC:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX];
        MAP_EVERY UNDISCH_TAC [`&0 <= MA`; `&0 <= sum(1..dimindex(:N)) MB`] THEN
        REAL_ARITH_TAC]];
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Real-variable tools: integrals with a variable upper limit, and           *)
(* a weighted Gronwall inequality with forcing (PDE_GRONWALL_W).             *)
(* ========================================================================= *)

let PDE_RINT_CONT = prove
 (`!(h:real->real) T1.
     h real_continuous_on real_interval[&0,T1]
     ==> (\s. real_integral (real_interval[&0,s]) h) real_continuous_on
         real_interval[&0,T1]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
  EXISTS_TAC `(h:real->real) s` THEN
  MP_TAC(ISPECL [`h:real->real`; `&0`; `T1:real`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_SIMP_TAC[]);;

let PDE_RINT_DERIV = prove
 (`!(h:real->real) T1 s.
     h real_continuous_on real_interval[&0,T1] /\ s IN real_interval(&0,T1)
     ==> ((\s. real_integral (real_interval[&0,s]) h) has_real_derivative h s) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real->real`; `&0`; `T1:real`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `real_interval(&0,T1)` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    HAS_REAL_DERIVATIVE_WITHIN_SUBSET)) THEN
  REWRITE_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL]);;

let PDE_EXP_WEIGHT_CONT = prove
 (`!mu s. (\r. exp(--(mu * r))) real_continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\r. exp(--(mu * r))) = exp o (\r. --mu * r)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EXP] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID]);;

(* Weighted Gronwall: if e(0) = 0 and e' + a <= b + K e on (0,T1), then    *)
(* e^(-mu t) e(t) + int_0^t e^(-mu r) (a + (mu - K) e) <= int_0^t e^(-mu r) b. *)

let PDE_GRONWALL_W = prove
 (`!(e:real->real) e' a b K mu T1.
     e(&0) = &0 /\
     e real_continuous_on real_interval[&0,T1] /\
     a real_continuous_on real_interval[&0,T1] /\
     b real_continuous_on real_interval[&0,T1] /\
     (!t. t IN real_interval(&0,T1)
          ==> (e has_real_derivative e' t) (atreal t) /\ e' t + a t <= b t + K * e t)
     ==> !t. t IN real_interval[&0,T1]
             ==> exp(--(mu * t)) * e t +
                 real_integral (real_interval[&0,t])
                   (\r. exp(--(mu * r)) * (a r + (mu - K) * e r))
                 <= real_integral (real_interval[&0,t]) (\r. exp(--(mu * r)) * b r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  ABBREV_TAC `h1 = \r. exp(--(mu * r)) * ((a:real->real) r + (mu - K) * (e:real->real) r)` THEN
  ABBREV_TAC `h2 = \r. exp(--(mu * r)) * (b:real->real) r` THEN
  SUBGOAL_THEN
   `(h1:real->real) real_continuous_on real_interval[&0,T1] /\
    (h2:real->real) real_continuous_on real_interval[&0,T1]`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN REWRITE_TAC[PDE_EXP_WEIGHT_CONT] THEN
    TRY(MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= t`; `~(t = &0)`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. exp(--(mu * s)) * (e:real->real) s +
         real_integral (real_interval[&0,s]) (h1:real->real) -
         real_integral (real_interval[&0,s]) (h2:real->real)`;
    `\s. exp(--(mu * s)) * ((e':real->real) s + (a:real->real) s - K * (e:real->real) s -
                           (b:real->real) s)`;
    `&0`; `t:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,T1]` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[PDE_EXP_WEIGHT_CONT];
          MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN ASM_SIMP_TAC[PDE_RINT_CONT]];
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        MAP_EVERY UNDISCH_TAC [`t <= T1`] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `x IN real_interval(&0,T1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < x`; `x < t`; `t <= T1`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h1:real->real`; `T1:real`; `x:real`] PDE_RINT_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h2:real->real`; `T1:real`; `x:real`] PDE_RINT_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    NSPU_DIFF_TAC
     [ASSUME `((e:real->real) has_real_derivative (e':real->real) x) (atreal x)`;
      ASSUME `((\s. real_integral (real_interval[&0,s]) (h1:real->real)) has_real_derivative
               h1 x) (atreal x)`;
      ASSUME `((\s. real_integral (real_interval[&0,s]) (h2:real->real)) has_real_derivative
               h2 x) (atreal x)`] THEN
    MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[IN_REAL_INTERVAL]) (MP_TAC o BETA_RULE))) THEN
  SUBGOAL_THEN `x IN real_interval(&0,T1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < x`; `x < t`; `t <= T1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= exp(--(mu * x)) * --((e':real->real) x + (a:real->real) x - K * (e:real->real) x -
                              (b:real->real) x) * t`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    MAP_EVERY UNDISCH_TAC
     [`(e':real->real) x + (a:real->real) x <= (b:real->real) x + K * (e:real->real) x`;
      `&0 < t`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_MUL_RZERO] THEN
  MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The energy of a solution along time (continuity and derivative), the      *)
(* combined fixed-time inequality, and the energy estimate PDE_TORUS_ENERGY. *)
(* ========================================================================= *)

let PDE_HS2_ZERO = prove
 (`!m. pde_hs2 m (\y:real^N. vec 0:real^K) = &0`,
  REWRITE_TAC[pde_hs2; TEXT_ITERATED_PARTIAL_ZERO; NORM_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[LIFT_NUM; INTEGRAL_0; DROP_VEC; SUM_0]);;

(* Continuity in time of the energy of a map smooth up to t = 0. *)

let PDE_UPTO_HS2_CONT = prove
 (`!tmax (g:real->real^N->real^K) T1 m.
     pde_upto (&0) tmax (:real^N) g /\ T1 < tmax
     ==> (\r. pde_hs2 m (g r)) real_continuous_on real_interval[&0,T1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pde_upto]) THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\r. pde_hs2 m (\y. (FG:real^(1,N)finite_sum->real^K)(pastecart (lift r) y))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= r`; `r <= T1`; `T1 < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
  MP_TAC(ISPECL [`FG:real^(1,N)finite_sum->real^K`; `&0 - e`; `tmax:real`; `m:num`; `r:real`]
                PDE_HS2_SLICE_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 <= r`; `r <= T1`; `T1 < tmax`] THEN REAL_ARITH_TAC;
    MESON_TAC[]]);;

(* The derivative of the energy of a solution. *)

let PDE_TSOL_ENERGY_DERIV = prove
 (`!tmax (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f u0 u m t.
     pde_tsol tmax aa bb cc f u0 u /\ &0 < t /\ t < tmax
     ==> ((\r. pde_hs2 m (u r)) has_real_derivative
          sum (pde_index_lists m (:N))
            (\l. pde_cint (\y. &2 * (iterated_partial l (u t) y dot
                    iterated_partial l (\y. pde_lop0 (aa t) (bb t) (cc t) (u t) y + f t y) y))))
         (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_tsol]) THEN
  REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FU:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r < tmax
                    ==> (u:real->real^N->real^K) r =
                        (\y. (FU:real^(1,N)finite_sum->real^K)(pastecart (lift r) y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\r. pde_hs2 m (\y. (FU:real^(1,N)finite_sum->real^K)(pastecart (lift r) y))` THEN
  EXISTS_TAC `min t (tmax - t)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM MP_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FU:real^(1,N)finite_sum->real^K`; `&0 - e`; `tmax:real`; `m:num`; `t:real`]
                PDE_HS2_SLICE_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 < t`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!f' f''. f' = f'' ==> (f has_real_derivative f') net
                                 ==> (f has_real_derivative f'') net`) THEN
  SUBGOAL_THEN `(\y. (FU:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)) =
                (u:real->real^N->real^K) t`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. partial_derivative 1 (FU:real^(1,N)finite_sum->real^K) (pastecart (lift t) y)) =
    (\y. pde_lop0 ((aa:real->real^N->real^N^N) t) ((bb:real->real^N->num->real^K^K) t)
                  ((cc:real->real^N->real^K^K) t) ((u:real->real^N->real^K) t) y +
         (f:real->real^N->real^K) t y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM PDE_LOP_LOP0] THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC PDE_TSOL_TIME_PARTIAL THEN
    MAP_EVERY EXISTS_TAC [`tmax:real`; `u0:real^N->real^K`; `e:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* FT1 and FT3 together: the energy inequality for L u + F at a fixed time. *)

let PDE_ENERGY_FT13 = prove
 (`!s M lam.
     &0 < lam
     ==> ?K. &0 <= K /\
             !(A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K) ff.
               pde_fcoeff ((s + 1) + 1) M lam A B C /\
               smooth_map_on (:real^N) u /\ pde_zper u /\
               smooth_map_on (:real^N) ff /\ pde_zper ff
               ==> sum (pde_index_lists (s + 1) (:N))
                       (\l. pde_cint (\x. &2 * (iterated_partial l u x dot
                                 iterated_partial l (\x. pde_lop0 A B C u x + ff x) x)))
                   <= K * pde_hs2 (s + 1) u + K * pde_hs2 s ff`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s + 1`; `M:real`; `lam:real`] PDE_FT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K1:real`) THEN
  MP_TAC(ISPECL [`s:num`; `lam:real`] PDE_FT3) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K3:real`) THEN
  EXISTS_TAC `abs K1 + abs K3` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N)
                  (pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_LOP0_SMOOTH THEN MAP_EVERY EXISTS_TAC [`(s + 1) + 1`; `M:real`] THEN
    ASM_MESON_TAC[pde_fcoeff];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists (s + 1) (:N))
      (\l. pde_cint (\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
                    iterated_partial l (pde_lop0 (A:real^N->real^N^N)
                                         (B:real^N->num->real^K^K) C u) x))) +
    sum (pde_index_lists (s + 1) (:N))
      (\l. pde_cint (\x. &2 * (iterated_partial l u x dot
                    iterated_partial l (ff:real^N->real^K) x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN SIMP_TAC[GSYM SUM_ADD; PDE_INDEX_LISTS_FINITE] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!x. iterated_partial l
            (\x. pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C
                          (u:real^N->real^K) x + (ff:real^N->real^K) x) x =
          iterated_partial l (pde_lop0 A B C u) x + iterated_partial l ff x`
    (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPECL [`l:num list`; `(:real^N)`;
                     `pde_lop0 (A:real^N->real^N^N) (B:real^N->num->real^K^K) C
                               (u:real^N->real^K)`;
                     `ff:real^N->real^K`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[DOT_RADD; REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC PDE_CINT_ADD THEN CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->real^K`; `ff:real^N->real^K`]) THEN
  ASM_REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`A:real^N->real^N^N`; `B:real^N->num->real^K^K`;
                                `C:real^N->real^K^K`; `u:real^N->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= pde_hs2 (s + 1) (u:real^N->real^K) /\ &0 <= pde_hs2 s (ff:real^N->real^K) /\
    &0 <= sum(1..dimindex(:N)) (\i. pde_hs2 (s + 1) (partial_derivative i u))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PDE_HS2_POS] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_SIMP_TAC[PDE_HS2_POS; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K1:real`; `abs K1`; `pde_hs2 (s + 1) (u:real^N->real^K)`] REAL_LE_RMUL) THEN
  MP_TAC(ISPECL [`K3:real`; `abs K3`; `pde_hs2 (s + 1) (u:real^N->real^K)`] REAL_LE_RMUL) THEN
  MP_TAC(ISPECL [`K3:real`; `abs K3`; `pde_hs2 s (ff:real^N->real^K)`] REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_LE] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= abs K1 * pde_hs2 s (ff:real^N->real^K) /\
                &0 <= lam * sum(1..dimindex(:N)) (\i. pde_hs2 (s + 1)
                                                         (partial_derivative i (u:real^N->real^K)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The energy estimate for zero initial data (the gain of one derivative).  *)

let PDE_TORUS_ENERGY = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc t1 s.
        &0 < tmax /\ pde_tcoeff tmax lam aa bb cc /\ &0 < t1 /\ t1 < tmax
        ==> ?C. !f u. pde_upto (&0) tmax (:real^N) f /\ (!t. pde_zper (f t)) /\
                      pde_tsol tmax aa bb cc f (\y. vec 0) u
                      ==> !t. &0 <= t /\ t <= t1
                              ==> pde_hs2 (s + 1) (u t) <=
                                  C * real_integral (real_interval[&0,t])
                                                    (\r. pde_hs2 s (f r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam:real`; `aa:real->real^N->real^N^N`;
                 `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`;
                 `t1:real`; `(s + 1) + 1`] PDE_TCOEFF_FCOEFF) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_MESON_TAC[pde_tcoeff]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:num`; `M:real`; `lam:real`] PDE_ENERGY_FT13) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `exp(K * t1) * K` THEN
  MAP_EVERY X_GEN_TAC [`f:real->real^N->real^K`; `u:real->real^N->real^K`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_tsol]) THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < tmax
        ==> smooth_map_on (:real^N) ((u:real->real^N->real^K) t) /\
            smooth_map_on (:real^N) ((f:real->real^N->real^K) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN
    EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. pde_hs2 (s + 1) ((u:real->real^N->real^K) r)`;
    `\r. sum (pde_index_lists (s + 1) (:N))
           (\l. pde_cint (\x. &2 * (iterated_partial l ((u:real->real^N->real^K) r) x dot
                  iterated_partial l (\x. pde_lop0 ((aa:real->real^N->real^N^N) r)
                                            ((bb:real->real^N->num->real^K^K) r)
                                            ((cc:real->real^N->real^K^K) r) (u r) x +
                                          (f:real->real^N->real^K) r x) x)))`;
    `\r:real. &0`;
    `\r. K * pde_hs2 s ((f:real->real^N->real^K) r)`;
    `K:real`; `K:real`; `t1:real`] PDE_GRONWALL_W) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(u:real->real^N->real^K) (&0) = (\y. vec 0)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; REWRITE_TAC[PDE_HS2_ZERO]];
      MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN
      EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PDE_TSOL_ENERGY_DERIV THEN
        MAP_EVERY EXISTS_TAC [`tmax:real`; `\y:real^N. vec 0:real^K`] THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`r < t1`; `t1 < tmax`] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= r /\ r <= t1 /\ r < tmax` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&0 < r`; `r < t1`; `t1 < tmax`] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`(aa:real->real^N->real^N^N) r`; `(bb:real->real^N->num->real^K^K) r`;
        `(cc:real->real^N->real^K^K) r`; `(u:real->real^N->real^K) r`;
        `(f:real->real^N->real^K) r`] o
       check (fun th -> is_forall(concl th) &&
                        can (find_term ((=) `pde_lop0:(real^N->real^N^N)->(real^N->num->real^K^K)->(real^N->real^K^K)->(real^N->real^K)->real^N->real^K`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "gw") THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REMOVE_THEN "gw" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_RZERO; REAL_INTEGRAL_0;
              REAL_ADD_RID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(\r. (f:real->real^N->real^K) r) = f`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. pde_hs2 s ((f:real->real^N->real^K) r)) real_continuous_on real_interval[&0,t]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`t <= t1`; `t1 < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= real_integral (real_interval[&0,t]) (\r. pde_hs2 s ((f:real->real^N->real^K) r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_HS2_POS THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `smooth_map_on:(real^N->bool)->(real^N->real^K)->bool`))
                           (concl th))) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 <= r`; `r <= t`; `t <= t1`; `t1 < tmax`] THEN REAL_ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,t])
      (\r. exp(--(K * r)) * K * pde_hs2 s ((f:real->real^N->real^K) r)) <=
    K * real_integral (real_interval[&0,t]) (\r. pde_hs2 s (f r))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_CONTINUOUS] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_MUL;
                 PDE_EXP_WEIGHT_CONT] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= K * pde_hs2 s ((f:real->real^N->real^K) r)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_HS2_POS THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `smooth_map_on:(real^N->bool)->(real^N->real^K)->bool`))
                             (concl th))) THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&0 <= r`; `r <= t`; `t <= t1`; `t1 < tmax`] THEN
        REAL_ARITH_TAC;
        MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(K * r)) <= &1` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      REWRITE_TAC[REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`exp(--(K * r))`; `&1`; `K * pde_hs2 s ((f:real->real^N->real^K) r)`]
                  REAL_LE_RMUL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(K * t) <= exp(K * t1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_hs2 (s + 1) ((u:real->real^N->real^K) t) =
                exp(K * t) * (exp(--(K * t)) * pde_hs2 (s + 1) (u t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(K * t) * (K * real_integral (real_interval[&0,t])
                                  (\r. pde_hs2 s ((f:real->real^N->real^K) r)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Linearity of the operator, of smoothness up to t = 0 and of solutions;    *)
(* uniqueness (PDE_TORUS_UNIQUE).                                            *)
(* ========================================================================= *)

let PDE_PARTIAL_LIN2 = prove
 (`!(u:real^N->real^K) v a b i.
     smooth_map_on (:real^N) u /\ smooth_map_on (:real^N) v
     ==> partial_derivative i (\y. a % u y + b % v y) =
         (\y. a % partial_derivative i u y + b % partial_derivative i v y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
  SUBGOAL_THEN `(u:real^N->real^K) differentiable (at y) /\ (v:real^N->real^K) differentiable (at y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_ADD o lhand o snd) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_CMUL]);;

let PDE_LOP0_LIN = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K) v a b x.
     smooth_map_on (:real^N) u /\ smooth_map_on (:real^N) v
     ==> pde_lop0 A B C (\y. a % u y + b % v y) x =
         a % pde_lop0 A B C u x + b % pde_lop0 A B C v x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lop0] THEN
  ASM_SIMP_TAC[PDE_PARTIAL_LIN2; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
  SUBGOAL_THEN
   `!i j. partial_derivative i (\y. a % partial_derivative j (u:real^N->real^K) y +
                                    b % partial_derivative j (v:real^N->real^K) y) =
          (\y. a % partial_derivative i (partial_derivative j u) y +
               b % partial_derivative i (partial_derivative j v) y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_PARTIAL_LIN2 THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  REWRITE_TAC[VECTOR_ARITH `(c:real) % (a % P + b % Q):real^K = a % (c % P) + b % (c % Q)`] THEN
  REWRITE_TAC[VSUM_ADD_NUMSEG; VSUM_LMUL] THEN VECTOR_ARITH_TAC);;

(* Smoothness up to t = 0, and solutions, are closed under linear           *)
(* combinations.                                                             *)

let PDE_UPTO_LIN2 = prove
 (`!a0 b0 (u:real->real^N->real^K) v a b.
     pde_upto a0 b0 (:real^N) u /\ pde_upto a0 b0 (:real^N) v
     ==> pde_upto a0 b0 (:real^N) (\t y. a % u t y + b % v t y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `F1:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `F2:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `min e1 e2` THEN
  EXISTS_TAC `\z. a % (F1:real^(1,N)finite_sum->real^K) z +
                  b % (F2:real^(1,N)finite_sum->real^K) z` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `interval(lift(a0 - e1),lift b0) PCROSS (:real^N)`;
      EXISTS_TAC `interval(lift(a0 - e2),lift b0) PCROSS (:real^N)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN BINOP_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PDE_UPTO_CONST = prove
 (`!a0 b0 (c:real^K). pde_upto a0 b0 (:real^N) (\t y. c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  MAP_EVERY EXISTS_TAC [`&1`; `\z:real^(1,N)finite_sum. (c:real^K)`] THEN
  REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST]);;

let PDE_TSOL_LIN2 = prove
 (`!tmax (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f g u0 v0 u v a b.
     pde_tsol tmax aa bb cc f u0 u /\ pde_tsol tmax aa bb cc g v0 v
     ==> pde_tsol tmax aa bb cc (\t y. a % f t y + b % g t y) (\y. a % u0 y + b % v0 y)
                  (\t y. a % u t y + b % v t y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tsol] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_LIN2 THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `pde_zper ((u:real->real^N->real^K) t) /\ pde_zper ((v:real->real^N->real^K) t)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[pde_zper] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `pde_lop aa bb cc (\t y. a % (u:real->real^N->real^K) t y + b % (v:real->real^N->real^K) t y)
              t y =
      a % pde_lop (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc u t y +
      b % pde_lop aa bb cc v t y`
    SUBST1_TAC THENL
     [REWRITE_TAC[PDE_LOP_LOP0] THEN MATCH_MP_TAC PDE_LOP0_LIN THEN
      CONJ_TAC THEN MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN EXISTS_TAC `tmax:real` THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`&0 < t`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(a % pde_lop (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc
             (u:real->real^N->real^K) t y +
       b % pde_lop aa bb cc (v:real->real^N->real^K) t y) +
      (a % (f:real->real^N->real^K) t y + b % (g:real->real^N->real^K) t y) =
      a % (pde_lop aa bb cc u t y + f t y) + b % (pde_lop aa bb cc v t y + g t y)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[]]);;

(* Zero H^0 energy forces a smooth periodic map to vanish. *)

let PDE_HS2_0_EQ_0 = prove
 (`!(w:real^N->real^K).
     smooth_map_on (:real^N) w /\ pde_zper w /\ pde_hs2 0 w <= &0 ==> !y. w y = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN interval[vec 0,vec 1] ==> (w:real^N->real^K) y = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPEC `\x. norm((w:real^N->real^K) x) pow 2` NSPU_INTEGRAL_EQ_0_CONTINUOUS) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF] THEN
        MATCH_MP_TAC PDE_SMOOTH_CONTINUOUS_AT THEN ASM_SIMP_TAC[PDE_SMOOTH_SQNORM];
        REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= &0 /\ &0 <= x ==> x = &0`) THEN
        ASM_REWRITE_TAC[GSYM PDE_HS2_0] THEN ASM_SIMP_TAC[PDE_HS2_POS]];
      SIMP_TAC[REAL_POW_EQ_0; NORM_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N->real^K`; `y:real^N`] PDE_ZPER_CUBE) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Uniqueness. *)

let PDE_TORUS_UNIQUE = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f u0 u v.
        &0 < tmax /\ pde_tcoeff tmax lam aa bb cc /\
        pde_tsol tmax aa bb cc f u0 u /\ pde_tsol tmax aa bb cc f u0 v
        ==> !t y. &0 <= t /\ t < tmax ==> u t y = v t y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_MESON_TAC[pde_tsol]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= t`; `~(t = &0)`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`tmax:real`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `f:real->real^N->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `u0:real^N->real^K`;
                 `u:real->real^N->real^K`; `v:real->real^N->real^K`; `&1`; `--(&1)`]
                PDE_TSOL_LIN2) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `&1 % (x:real^K) + --(&1) % x = vec 0`] THEN
  REWRITE_TAC[VECTOR_ARITH `&1 % (x:real^K) + --(&1) % y = x - y`] THEN
  ABBREV_TAC `w = \t y. (u:real->real^N->real^K) t y - (v:real->real^N->real^K) t y` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam:real`; `aa:real->real^N->real^N^N`;
                 `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`;
                 `t:real`; `0`] PDE_TORUS_ENERGY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (MP_TAC o SPECL
    [`\t:real y:real^N. vec 0:real^K`; `w:real->real^N->real^K`])) THEN
  ASM_REWRITE_TAC[PDE_UPTO_CONST; PDE_ZPER_CONST; PDE_HS2_ZERO; REAL_INTEGRAL_0;
                  REAL_MUL_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) ((w:real->real^N->real^K) t) /\ pde_zper (w t)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_tsol]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN EXISTS_TAC `tmax:real` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(w:real->real^N->real^K) t` PDE_HS2_0_EQ_0) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_hs2 1 ((w:real->real^N->real^K) t)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_HS2_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN EXPAND_TAC "w" THEN
  REWRITE_TAC[VECTOR_SUB_EQ]);;

