(* ========================================================================= *)
(* Unit pc_p2c_cgemb (Part 2C, used in the pc_p2c_cg route): embeddings of   *)
(* the exhaustion of the glued Cheeger-Gromov limit into the sequence.  For  *)
(* each level j, patching the inverse normal charts of the sequence over the *)
(* limit charts at level j + 2 with smooth cutoffs gives, for all large n, a *)
(* diffeomorphism F of W j onto an open subset of the manifold sq n with F   *)
(* xl = x (sq n) whose pulled-back metrics converge to the limit metric in   *)
(* every C^m.                                                                *)
(* ========================================================================= *)

needs "src/pc_p2c_cgcomp.ml";;
needs "src/pc_p2c_cgcinf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Euclidean facts.  An injective smooth map with invertible                 *)
(* derivative on an open set is a diffeomorphism onto its open image; maps   *)
(* converging to the identity in C-infinity near z0 are eventually such      *)
(* diffeomorphisms on a ball around z0, with |x - y| <= 2 |R x - R y|.       *)
(* ------------------------------------------------------------------------- *)

let P2CE_ENTRY_LE_VECTORIZE = prove
 (`!(A:real^N^N) i j.
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> abs(A$i$j) <= norm((vectorize:real^N^N->real^(N,N)finite_prod) A)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(vectorize:real^N^N->real^(N,N)finite_prod) A`; `i:num`; `j:num`]
                MATRIFY_COMPONENT) THEN
  ASM_REWRITE_TAC[MATRIFY_VECTORIZE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPONENT_LE_NORM]);;

let P2CE_MATRIX_HALF = prove
 (`!(A:real^N^N) v.
     norm(vectorize A - vectorize(mat 1:real^N^N)) <
     inv(&2 * &(dimindex(:N)) * &(dimindex(:N)))
     ==> norm(A ** v - v) <= inv(&2) * norm v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A - mat 1:real^N^N`;
                 `inv(&2 * &(dimindex(:N)) * &(dimindex(:N)))`]
                ONORM_LE_MATRIX_COMPONENT) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^N^N->real^(N,N)finite_prod) (A - mat 1))` THEN
    ASM_SIMP_TAC[P2CE_ENTRY_LE_VECTORIZE; VECTORIZE_SUB; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(dimindex(:N)) * &(dimindex(:N)) * inv(&2 * &(dimindex(:N)) * &(dimindex(:N))) =
                inv(&2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &(dimindex(:N))` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `\x:real^N. (A - mat 1:real^N^N) ** x` ONORM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c /\ x = y ==> x <= b ==> y <= c`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID]]);;

let P2CE_INJ_DIFFEO = prove
 (`!(f:real^N->real^N) s.
     open s /\ smooth_map_on s f /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     (!x. x IN s ==> ~(det(matrix(frechet_derivative f (at x))) = &0))
     ==> ?g. diffeomorphism_on s (IMAGE f s) f g`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\y:real^N. @x. x IN s /\ (f:real^N->real^N) x = y` THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> (@x'. x' IN s /\ (f:real^N->real^N) x' = f x) = x`
  (LABEL_TAC "inv") THENL
   [REPEAT STRIP_TAC THEN SELECT_ELIM_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> ((f:real^N->real^N) has_derivative
                                         frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:real^N->real^N) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_OPEN_MAP THEN
    EXISTS_TAC `\x:real^N. frechet_derivative (f:real^N->real^N) (at x)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "inv" (fun th -> ASM_SIMP_TAC[th]);
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(f:real^N->real^N) x` THEN
      USE_THEN "inv" (fun th -> ASM_SIMP_TAC[th]) THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "inv" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`; `a:real^N`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g0:real^N->real^N` THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g0:real^N->real^N) y IN s /\ (f:real^N->real^N)(g0 y) = y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `diffeomorphism_on t u (f:real^N->real^N) g0` THEN
      REWRITE_TAC[diffeomorphism_on] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "inv" (MP_TAC o C MP (ASSUME `(g0:real^N->real^N) y IN s`) o
                    SPEC `(g0:real^N->real^N) y`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `diffeomorphism_on t u (f:real^N->real^N) g0` THEN
    SIMP_TAC[diffeomorphism_on]]);;

let P2CE_NEAR_ID_INJ = prove
 (`!(z0:real^N) (Rs:num->real^N->real^N).
     p2ci_near z0 Rs (\z. z)
     ==> ?r N. &0 < r /\
               !n. N <= n
                   ==> smooth_map_on (ball(z0,r)) (Rs n) /\
                       (!x y. x IN ball(z0,r) /\ y IN ball(z0,r)
                              ==> norm(x - y) <= &2 * norm(Rs n x - Rs n y)) /\
                       (!x. x IN ball(z0,r)
                            ==> ~(det(matrix(frechet_derivative (Rs n) (at x))) = &0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2CI_NEAR_JACOBIAN) THEN
  SUBGOAL_THEN `!z:real^N. matrix(frechet_derivative (\z:real^N. z) (at z)) = mat 1`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MP_TAC(ISPEC `at (z:real^N)` HAS_DERIVATIVE_ID) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    REWRITE_TAC[MATRIX_ID];
    ALL_TAC] THEN
  REWRITE_TAC[p2ci_near; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "jc")))))) THEN
  UNDISCH_TAC `p2ci_near (z0:real^N) (Rs:num->real^N->real^N) (\z. z)` THEN
  REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`) (K ALL_TAC)))) THEN
  SUBGOAL_THEN `&0 < inv(&2 * &(dimindex(:N)) * &(dimindex(:N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN
    SUBGOAL_THEN `&0 < &(dimindex(:N))` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`];
      ALL_TAC] THEN
    SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  USE_THEN "jc" (MP_TAC o C MP (ASSUME `&0 < inv(&2 * &(dimindex(:N)) * &(dimindex(:N)))`) o
                 SPEC `inv(&2 * &(dimindex(:N)) * &(dimindex(:N)))`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MAP_EVERY EXISTS_TAC [`min r0 r1`; `N0 + N1:num`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ball(z0:real^N,min r0 r1) SUBSET ball(z0,r0) /\
                ball(z0:real^N,min r0 r1) SUBSET ball(z0,r1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(z0:real^N,min r0 r1)) ((Rs:num->real^N->real^N) n)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^N,r0)` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN ball(z0,min r0 r1)
               ==> ((Rs:num->real^N->real^N) n has_derivative
                    frechet_derivative (Rs n) (at x)) (at x) /\
                   !v. norm(frechet_derivative (Rs n) (at x) v - v) <= inv(&2) * norm v`
  (LABEL_TAC "der") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Rs:num->real^N->real^N) n differentiable (at x)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(z0:real^N,min r0 r1)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN X_GEN_TAC `v:real^N` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    MATCH_MP_TAC P2CE_MATRIX_HALF THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `N1:num`)) (concl th))) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\z:real^N. (Rs:num->real^N->real^N) n z - z`;
                   `\z:real^N. \v:real^N. frechet_derivative ((Rs:num->real^N->real^N) n) (at z) v - v`;
                   `ball(z0:real^N,min r0 r1)`; `inv(&2)`] DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        REWRITE_TAC[HAS_DERIVATIVE_ID; ETA_AX] THEN USE_THEN "der" (MP_TAC o SPEC `w:real^N`) THEN
        ASM_SIMP_TAC[];
        MP_TAC(ISPEC `\v:real^N. frechet_derivative ((Rs:num->real^N->real^N) n) (at w) v - v`
                     ONORM) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[LINEAR_ID; ETA_AX] THEN
          MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
          MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
          EXISTS_TAC `ball(z0:real^N,min r0 r1)` THEN ASM_REWRITE_TAC[OPEN_BALL];
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
          USE_THEN "der" (MP_TAC o SPEC `w:real^N`) THEN ASM_SIMP_TAC[]]];
      DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`x - y:real^N`; `(Rs:num->real^N->real^N) n x - Rs n y`]
                    NORM_TRIANGLE_SUB) THEN
      SUBGOAL_THEN `norm((x - y) - ((Rs:num->real^N->real^N) n x - Rs n y)) =
                    norm((Rs n x - x) - (Rs n y - y))` SUBST1_TAC THENL
       [MATCH_MP_TAC(MESON[NORM_NEG] `!a b:real^N. a = --b ==> norm a = norm b`) THEN
        VECTOR_ARITH_TAC;
        REAL_ARITH_TAC]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "der" (MP_TAC o SPEC `v:real^N` o CONJUNCT2 o
                    C MP (ASSUME `(x:real^N) IN ball(z0,min r0 r1)`) o SPEC `x:real^N`) THEN
    SUBGOAL_THEN `(Rs:num->real^N->real^N) n differentiable (at x)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(z0:real^N,min r0 r1)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_LZERO; NORM_NEG] THEN
    UNDISCH_TAC `~(v:real^N = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
    REAL_ARITH_TAC]);;

let P2CE_NEAR_ID_DIFFEO = prove
 (`!(z0:real^N) (Rs:num->real^N->real^N).
     p2ci_near z0 Rs (\z. z)
     ==> ?r N. &0 < r /\
               !n s. N <= n /\ open s /\ s SUBSET ball(z0,r)
                     ==> ?Ri. diffeomorphism_on s (IMAGE (Rs n) s) (Rs n) Ri`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2CE_NEAR_ID_INJ) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real^N->bool`] THEN STRIP_TAC THEN
  USE_THEN "inj" (STRIP_ASSUME_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
  MATCH_MP_TAC P2CE_INJ_DIFFEO THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^N,r)` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`] o
      check (fun th -> can (find_term ((=) `&2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_MUL_RZERO] THEN
    REWRITE_TAC[NORM_LE_0; VECTOR_SUB_EQ];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o
      check (fun th -> can (find_term ((=) `det:real^N^N->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The normal charts of the sequence.  From the index                        *)
(* p2cg_nv a on, the normal map p2cg_nch k a is a parametrization on         *)
(* ball(0,rho_a); p2ce_L k a is its inverse, the transitions are             *)
(* p2cg_T k a b = p2ce_L k b o p2cg_nch k a, and the exp metric p2cg_G k a   *)
(* is the pullback of h k by the normal map.                                 *)
(* ------------------------------------------------------------------------- *)

let p2ce_L = new_definition
 `p2ce_L (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
         (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real) k a (p:A) =
    @w:real^3. w IN ball(vec 0,rho(NUMFST a)) /\ p2cg_nch top atlas h yc k a w = p`;;

let P2CE_T_L = prove
 (`!top atlas (h:num->A->real^3^3) yc rho k a b z.
     p2cg_T top atlas h yc rho k a b z =
     p2ce_L top atlas h yc rho k b (p2cg_nch top atlas h yc k a z)`,
  REWRITE_TAC[p2cg_T; p2cg_trans; p2ce_L; p2cg_nch]);;

let P2CE_SEQ_MFD = prove
 (`!top atlas (h:num->A->real^3^3) x k.
     p2cu_seq top atlas h x
     ==> hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
         riemannian_metric (atlas k) (h k)`,
  REWRITE_TAC[p2cu_seq] THEN MESON_TAC[]);;

let P2CE_NCH_EQ = prove
 (`!top atlas (h:num->A->real^3^3) yc k a.
     p2cg_nch top atlas h yc k a =
     (\w. mfd_exp (top k,atlas k) (h k) (p2cg_ctr yc k a) (p2cg_frm h yc k a ** w))`,
  REWRITE_TAC[FUN_EQ_THM; p2cg_nch]);;

let P2CE_NCH_PARAM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> mfd_param (top k) (atlas k) (ball(vec 0,rho(NUMFST a)))
                   (p2cg_nch top atlas h yc k a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2CE_SEQ_MFD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) yc k a`; `(rho:num->real)(NUMFST a)`]
                GEON_NORMAL_PARAM) THEN
  ASM_REWRITE_TAC[P2CE_NCH_EQ] THEN SIMP_TAC[]);;

let P2CE_L_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> (!w. w IN ball(vec 0,rho(NUMFST a))
              ==> p2ce_L top atlas h yc rho k a (p2cg_nch top atlas h yc k a w) = w) /\
         (!p. p IN IMAGE (p2cg_nch top atlas h yc k a) (ball(vec 0,rho(NUMFST a)))
              ==> p2ce_L top atlas h yc rho k a p IN ball(vec 0,rho(NUMFST a)) /\
                  p2cg_nch top atlas h yc k a (p2ce_L top atlas h yc rho k a p) = p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2CE_NCH_PARAM) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2CE_SEQ_MFD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `p2cg_nch top atlas (h:num->A->real^3^3) yc k a`;
                 `ball(vec 0:real^3,rho(NUMFST a))`] GEON_PARAM_CHART_FACTS) THEN
  ASM_REWRITE_TAC[p2ce_L] THEN SIMP_TAC[]);;

let P2CE_G_RFS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ w IN ball(vec 0,rho(NUMFST a))
     ==> p2cg_G top atlas h yc k a w =
         rfs_pullback (atlas k) (p2cg_nch top atlas h yc k a) (h k) w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2CE_SEQ_MFD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `NUMFST a` o CONJUNCT1 o REWRITE_RULE[p2cg_levels]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) yc k a`; `(rho:num->real)(NUMFST a)`;
                 `(K:num->real)(NUMFST a)`] P2CU_EXPMETRIC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[p2cg_G; rfs_pullback; P2CE_NCH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Transitions near a point w0 of an overlap Om b c.  On a ball              *)
(* around w0 the transitions p2cg_T (sq n) b c eventually land in            *)
(* ball(0,rho_c/2) and intertwine the normal maps, and they converge to the  *)
(* limit transition p2cg_tr b c in C-infinity near w0.                       *)
(* ------------------------------------------------------------------------- *)

let P2CE_T_NEAR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl b c w0.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\ w0 IN p2cg_om rho D b c
     ==> ?r N. &0 < r /\ ball(w0,r) SUBSET p2cg_om rho D b c /\
               (!n v. N <= n /\ v IN ball(w0,r)
                      ==> p2cg_T top atlas h yc rho (sq n) b c v IN
                          ball(vec 0,rho(NUMFST c) / &2) /\
                          p2cg_nch top atlas h yc (sq n) c
                            (p2cg_T top atlas h yc rho (sq n) b c v) =
                          p2cg_nch top atlas h yc (sq n) b v) /\
               p2ci_near w0 (\n. p2cg_T top atlas h yc rho (sq n) b c) (p2cg_tr rho D b c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `c:num`; `w0:real^3`] o
    check (fun th -> can (find_term ((=) `iterated_partial:(num)list->(real^3->real^3)->real^3->real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rT:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tc")))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `c:num`; `w0:real^3`]) P2CG_GOOD_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nq:num` (X_CHOOSE_THEN `pq:num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `q = p2cg_qv nq` THEN ABBREV_TAC `rq = inv(&2 pow pq)` THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `c:num`; `q:real^3`; `rq:real`;
                             `p2cg_nv N0 Nn b + p2cg_nv N0 Nn c`]) P2CG_GOOD_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `NG:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_good]) THEN
  SUBGOAL_THEN
   `!n:num. NG <= n
        ==> smooth_map_on (ball(q,&2 * rq))
              (p2cg_T (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
                      (h:num->A->real^3^3) (yc:num->num->num->A) rho (sq n) b c) /\
            (!v. v IN ball(q,&2 * rq)
                 ==> p2cg_T top atlas h yc rho (sq n) b c v IN
                     ball(vec 0,rho(NUMFST c) / &2) /\
                     p2cg_nch top atlas h yc (sq n) c
                       (p2cg_T top atlas h yc rho (sq n) b c v) =
                     p2cg_nch top atlas h yc (sq n) b v)`
  (LABEL_TAC "tg") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term ((=) `NG:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `c:num`; `q:real^3`; `rq:real`; `(sq:num->num) n`])
                  P2CG_T_GOOD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `Ti:real^3->real^3` MP_TAC) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s t x. IMAGE f s SUBSET t /\ x IN s ==> f x IN t`) THEN
    EXISTS_TAC `ball(q:real^3,&2 * rq)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rq - dist(q:real^3,w0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w0:real^3) IN ball(q,rq)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = min rT (rq - dist(q:real^3,w0))` THEN
  SUBGOAL_THEN `&0 < r /\ ball(w0:real^3,r) SUBSET ball(w0,rT) /\
                ball(w0:real^3,r) SUBSET ball(q,&2 * rq)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN
      MP_TAC(ISPECL [`q:real^3`; `w0:real^3`; `y:real^3`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `NG:num`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w0:real^3,rT)` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "tg" (MP_TAC o C MP (ASSUME `NG:num <= n`) o SPEC `n:num`) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(v:real^3) IN ball(w0,r)` THEN
    UNDISCH_TAC `ball(w0:real^3,r) SUBSET ball(q,&2 * rq)` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `NG:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(q:real^3,&2 * rq)` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "tg" (MP_TAC o C MP (ASSUME `NG:num <= n`) o SPEC `n:num`) THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `p2cg_om rho D b c` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w0:real^3,rT)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
      REWRITE_TAC[p2cl_system] THEN SIMP_TAC[]];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "tc" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                   C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:3)) l`) o SPEC `l:num list`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kn:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN ball(w0,r)` THEN
    UNDISCH_TAC `ball(w0:real^3,r) SUBSET ball(w0,rT)` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Good maps near a point of a chart.  p2ce_good Fs c z0: on a               *)
(* ball around z0 in the domain of the limit chart c, the maps Fs n          *)
(* (n large) land in the normal chart c of the manifold sq n, and in these   *)
(* coordinates they converge to the identity in C-infinity near z0.  The     *)
(* property is local in the maps (P2CE_GOOD_EQ) and does not depend on the   *)
(* chart (P2CE_GOOD_CHART: R^c = T(b,c) o R^b o Tr(c,b) near z0).            *)
(* ------------------------------------------------------------------------- *)

let p2ce_ctx = new_definition
 `p2ce_ctx (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
           (h:num->A->real^3^3) (x:num->A) (rho:num->real) (K:num->real)
           (N0:num->num) (B:num->num->real) (NB:num->num->num) (P:num->num)
           (Nn:num->num) (yc:num->num->num->A) (sq:num->num)
           (D:num#num->real^(3,3)finite_sum->real^1) (Gl:num->real^3->real^3^3)
           (kp:num->real^3->real^3) <=>
    p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
    p2cg_limit top atlas h yc rho sq D Gl /\
    p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp`;;

let p2ce_std = p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                           `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`];;

let P2CE_CTX_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
         p2cg_limit top atlas h yc rho sq D Gl /\
         p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
         p2cg_dsys top atlas h yc rho sq D /\
         p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) /\
         (!n. n <= sq n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ce_ctx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
  UNDISCH_TAC `p2cg_dsys (top:num->A topology) atlas h yc rho sq D` THEN
  REWRITE_TAC[p2cg_dsys] THEN SIMP_TAC[]);;

let P2CE_CONT_BALL = prove
 (`!(f:real^N->real^N) s z0 e.
     open s /\ z0 IN s /\ smooth_map_on s f /\ &0 < e
     ==> ?d. &0 < d /\ ball(z0,d) SUBSET s /\
             !z. z IN ball(z0,d) ==> dist(f z,f z0) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^N) continuous (at z0)` MP_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `z0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^N,d2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC]);;

let p2ce_good = new_definition
 `p2ce_good (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
            (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real)
            (kp:num->real^3->real^3) (sq:num->num) (Fs:num->real^3->A) c (z0:real^3) <=>
    ?r. &0 < r /\ ball(z0,r) SUBSET p2cg_dm rho c /\
        (?N. !n z. N <= n /\ z IN ball(z0,r)
                   ==> Fs n (kp c z) IN IMAGE (p2cg_nch top atlas h yc (sq n) c)
                                              (ball(vec 0,rho(NUMFST c)))) /\
        p2ci_near z0 (\n z. p2ce_L top atlas h yc rho (sq n) c (Fs n (kp c z))) (\z. z)`;;

let P2CE_GOOD_EQ = prove
 (`!top atlas (h:num->A->real^3^3) yc rho kp sq (Fs:num->real^3->A) Fs' c z0.
     p2ce_good top atlas h yc rho kp sq Fs c z0 /\
     (?r N. &0 < r /\
            !n z. N <= n /\ z IN ball(z0,r) ==> Fs' n (kp c z) = Fs n (kp c z))
     ==> p2ce_good top atlas h yc rho kp sq Fs' c z0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N1:num`) ASSUME_TAC))))
    (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `min r1 r2` THEN
  SUBGOAL_THEN `ball(z0:real^3,min r1 r2) SUBSET ball(z0,r1) /\
                ball(z0:real^3,min r1 r2) SUBSET ball(z0,r2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^3,r1)` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `N1 + N2:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Fs':num->real^3->A) n ((kp:num->real^3->real^3) c z) = Fs n (kp c z)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]];
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    EXISTS_TAC `\n z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) c
                        ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) c z))` THEN
    MAP_EVERY EXISTS_TAC [`\z:real^3. z`; `r2:real`; `N2:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

(* The chart change. *)

let P2CE_GOOD_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fs:num->real^3->A) b c w0 z0.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     p2ce_good top atlas h yc rho kp sq Fs b w0 /\
     w0 IN p2cg_dm rho b /\ z0 IN p2cg_dm rho c /\ kp b w0 = kp c z0
     ==> p2ce_good top atlas h yc rho kp sq Fs c z0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS)
    (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `Nb:num` (LABEL_TAC "lb")) (LABEL_TAC "nb"))))) THEN
  (* gluing *)
  SUBGOAL_THEN `w0 IN p2cg_om rho D b c /\ p2cg_tr rho D b c w0 = z0 /\
                z0 IN p2cg_om rho D c b /\ p2cg_tr rho D c b z0 = w0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[p2cl_glue] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`b:num`; `c:num`; `w0:real^3`; `z0:real^3`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:num`; `b:num`; `z0:real^3`; `w0:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the transitions near w0 *)
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `b:num`; `c:num`; `w0:real^3`])
                P2CE_T_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rT:real` (X_CHOOSE_THEN `NT:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "tf") (LABEL_TAC "tn")))))) THEN
  (* uniform closeness of R^b to the identity near w0 *)
  USE_THEN "nb" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `rT / &2`)))))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nu:num` (LABEL_TAC "nu")) THEN
  (* a ball around z0 mapped by Tr c b close to w0 *)
  SUBGOAL_THEN `open(p2cg_om rho D c b) /\
                smooth_map_on (p2cg_om rho D c b) (p2cg_tr rho D c b)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
    REWRITE_TAC[p2cl_system] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_tr rho D c b`; `p2cg_om rho D c b`; `z0:real^3`;
                 `min rb (min ru (rT / &2))`] P2CE_CONT_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dc")))) THEN
  SUBGOAL_THEN `p2cg_om rho D c b SUBSET p2cg_dm rho c /\
                (!z. z IN p2cg_om rho D c b
                     ==> p2cg_tr rho D c b z IN p2cg_om rho D b c /\
                         p2cg_tr rho D b c (p2cg_tr rho D c b z) = z) /\
                p2cg_om rho D b c SUBSET p2cg_dm rho b`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tr") ASSUME_TAC)) THENL
   [UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
    REWRITE_TAC[p2cl_system] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the pointwise facts for large n *)
  SUBGOAL_THEN
   `!n z. Nb + Nu + NT + p2cg_nv N0 Nn b + p2cg_nv N0 Nn c <= n /\ z IN ball(z0,d)
          ==> (Fs:num->real^3->A) n (kp c z) =
              p2cg_nch top atlas h yc (sq n) c
                (p2cg_T top atlas h yc rho (sq n) b c
                   (p2ce_L top atlas h yc rho (sq n) b (Fs n (kp b (p2cg_tr rho D c b z))))) /\
              p2cg_T top atlas h yc rho (sq n) b c
                (p2ce_L top atlas h yc rho (sq n) b (Fs n (kp b (p2cg_tr rho D c b z))))
              IN ball(vec 0,rho(NUMFST c) / &2)`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN p2cg_om rho D c b` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(z0,d)` THEN
      UNDISCH_TAC `ball(z0:real^3,d) SUBSET p2cg_om rho D c b` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_tr rho D c b z IN p2cg_om rho D b c` ASSUME_TAC THENL
     [USE_THEN "tr" (MP_TAC o C MP (ASSUME `(z:real^3) IN p2cg_om rho D c b`) o
                     SPEC `z:real^3`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(p2cg_tr rho D c b z,w0) < min rb (min ru (rT / &2))` ASSUME_TAC THENL
     [USE_THEN "dc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) c z = kp b (p2cg_tr rho D c b z)` SUBST1_TAC THENL
     [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) (kp:num->real^3->real^3)` THEN
      REWRITE_TAC[p2cl_glue] THEN
      DISCH_THEN(MP_TAC o SPECL [`c:num`; `b:num`; `z:real^3`; `p2cg_tr rho D c b z`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`)
        THENL [EXISTS_TAC `p2cg_om rho D c b`; EXISTS_TAC `p2cg_om rho D b c`] THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_tr rho D c b z IN ball(w0,rb) /\ p2cg_tr rho D c b z IN ball(w0,ru) /\
                  p2cg_tr rho D c b z IN ball(w0,rT / &2)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn b <= (sq:num->num) n /\ p2cg_nv N0 Nn c <= sq n`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `u = p2ce_L top atlas h yc rho ((sq:num->num) n) b
                      ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                         (p2cg_tr rho D c b z)))` THEN
    SUBGOAL_THEN `p2cg_nch top atlas h yc ((sq:num->num) n) b u =
                  (Fs:num->real^3->A) n ((kp:num->real^3->real^3) b (p2cg_tr rho D c b z))`
    ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN
      MP_TAC(ISPECL (p2cg_std @ [`b:num`; `(sq:num->num) n`]) P2CE_L_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `(Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                                  (p2cg_tr rho D c b z))` o CONJUNCT2) THEN
      ANTS_TAC THENL
       [USE_THEN "lb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^3) IN ball(w0,rT)` ASSUME_TAC THENL
     [USE_THEN "nu" (MP_TAC o SPECL [`n:num`; `p2cg_tr rho D c b z`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2cg_tr rho D c b z IN ball(w0,rT / &2)` THEN REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(ISPECL [`w0 - u:real^3`; `w0 - p2cg_tr rho D c b z`] NORM_TRIANGLE_SUB) THEN
      MP_TAC(ISPECL [`u:real^3`; `p2cg_tr rho D c b z`] NORM_SUB) THEN
      REWRITE_TAC[VECTOR_ARITH `(w0 - u) - (w0 - v):real^3 = v - u`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "tf" (MP_TAC o SPECL [`n:num`; `u:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `p2cg_om rho D c b` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `Nb + Nu + NT + p2cg_nv N0 Nn b + p2cg_nv N0 Nn c` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `p2cg_T top atlas (h:num->A->real^3^3) yc rho (sq n) b c
                   (p2ce_L top atlas h yc rho (sq n) b
                      ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                        (p2cg_tr rho D c b z)))) IN ball(vec 0,rho(NUMFST c) / &2)` THEN
    REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST c`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the convergence: compose and identify *)
  SUBGOAL_THEN `p2ci_near z0 (\n:num. p2cg_tr rho D c b) (p2cg_tr rho D c b)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `p2cg_om rho D c b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^3`; `\n:num. p2cg_tr rho D c b`; `p2cg_tr rho D c b`;
                 `\n z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) b
                          ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b z))`;
                 `\z:real^3. z`] P2CI_NEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^3`;
                 `\n:num. (\z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                 (sq n) b ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b z))) o
                          p2cg_tr rho D c b`;
                 `(\z:real^3. z) o p2cg_tr rho D c b`;
                 `\n:num. p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) b c`;
                 `p2cg_tr rho D b c`] P2CI_NEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  EXISTS_TAC `\n:num. p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) b c o
                      ((\z. p2ce_L top atlas h yc rho (sq n) b
                              ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b z))) o
                       p2cg_tr rho D c b)` THEN
  EXISTS_TAC `p2cg_tr rho D b c o ((\z:real^3. z) o p2cg_tr rho D c b)` THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `Nb + Nu + NT + p2cg_nv N0 Nn b + p2cg_nv N0 Nn c`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn c <= (sq:num->num) n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL (p2cg_std @ [`c:num`; `(sq:num->num) n`]) P2CE_L_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `p2cg_T top atlas (h:num->A->real^3^3) yc rho (sq n) b c
                   (p2ce_L top atlas h yc rho (sq n) b
                      ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                        (p2cg_tr rho D c b z)))) IN ball(vec 0,rho(NUMFST c) / &2)` THEN
    REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST c`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "tr" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(z0,d)` THEN
      UNDISCH_TAC `ball(z0:real^3,d) SUBSET p2cg_om rho D c b` THEN SET_TAC[];
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The patched maps.  Over a list cs of limit charts, step l                 *)
(* blends the previous map, read in the normal chart cs l, with the chart    *)
(* map itself by the cutoff p2ce_mu (1 on cball(0,rho/7), 0 off              *)
(* ball(0,rho/6)).  Goodness survives a step near points of the chart where  *)
(* it held (P2CE_GOOD_BLEND), holds after the step where the cutoff is 1     *)
(* (P2CE_GOOD_RESET), and is unaffected away from the closed patch           *)
(* (P2CE_GOOD_FAR).                                                          *)
(* ------------------------------------------------------------------------- *)

let p2ce_mu = new_definition
 `p2ce_mu (rho:num->real) b (w:real^3) =
    smooth_bump (rho(NUMFST b) / &7) (rho(NUMFST b) / &6) w`;;

let p2ce_step = new_definition
 `p2ce_step (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
            (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real)
            (kp:num->real^3->real^3) (cs:num->num) k l (G:real^3->A) (p:real^3) =
    if p IN IMAGE (kp (cs l)) (ball(vec 0,rho(NUMFST(cs l)) / &6))
    then p2cg_nch top atlas h yc k (cs l)
           ((&1 - p2ce_mu rho (cs l) (SND(p2cl_chart (p2cg_dm rho) kp (cs l)) p)) %
            p2ce_L top atlas h yc rho k (cs l) (G p) +
            p2ce_mu rho (cs l) (SND(p2cl_chart (p2cg_dm rho) kp (cs l)) p) %
            SND(p2cl_chart (p2cg_dm rho) kp (cs l)) p)
    else G p`;;

let p2ce_F = new_recursive_definition num_RECURSION
 `(p2ce_F (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
          (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real)
          (kp:num->real^3->real^3) (cs:num->num) k 0 =
      \p:real^3. p2cg_nch top atlas h yc k (cs 0) (vec 0)) /\
  (p2ce_F top atlas h yc rho kp cs k (SUC l) =
      p2ce_step top atlas h yc rho kp cs k l (p2ce_F top atlas h yc rho kp cs k l))`;;

let P2CE_F_SUC = prove
 (`!top atlas (h:num->A->real^3^3) yc rho kp cs k l p.
     p2ce_F top atlas h yc rho kp cs k (SUC l) p =
     if p IN IMAGE (kp (cs l)) (ball(vec 0,rho(NUMFST(cs l)) / &6))
     then p2cg_nch top atlas h yc k (cs l)
            ((&1 - p2ce_mu rho (cs l) (SND(p2cl_chart (p2cg_dm rho) kp (cs l)) p)) %
             p2ce_L top atlas h yc rho k (cs l) (p2ce_F top atlas h yc rho kp cs k l p) +
             p2ce_mu rho (cs l) (SND(p2cl_chart (p2cg_dm rho) kp (cs l)) p) %
             SND(p2cl_chart (p2cg_dm rho) kp (cs l)) p)
     else p2ce_F top atlas h yc rho kp cs k l p`,
  REWRITE_TAC[p2ce_F; p2ce_step]);;

let p2ce_om = new_definition
 `p2ce_om (rho:num->real) (kp:num->real^3->real^3) (cs:num->num) l =
    UNIONS {IMAGE (kp (cs i)) (ball(vec 0,rho(NUMFST(cs i)) / &7)) | i < l}`;;

let P2CE_MU_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc b.
     p2cg_levels top atlas h x rho K N0 B NB P Nn yc
     ==> smooth_map_on (:real^3) (\w. lift(p2ce_mu rho b w)) /\
         (!w. norm w <= rho(NUMFST b) / &7 ==> p2ce_mu rho b w = &1) /\
         (!w. rho(NUMFST b) / &6 <= norm w ==> p2ce_mu rho b w = &0) /\
         (!w. &0 <= p2ce_mu rho b w /\ p2ce_mu rho b w <= &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST b`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rho(NUMFST b) / &7 /\ rho(NUMFST b) / &7 < rho(NUMFST b) / &6`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[p2ce_mu; SMOOTH_BUMP_SMOOTH; SMOOTH_BUMP_1; SMOOTH_BUMP_0;
               SMOOTH_BUMP_BOUNDS]);;

let P2CE_KP_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> (!i z. z IN p2cg_dm rho i ==> SND(p2cl_chart (p2cg_dm rho) kp i) (kp i z) = z) /\
         (!i z z'. z IN p2cg_dm rho i /\ z' IN p2cg_dm rho i /\ kp i z = kp i z'
                   ==> z = z')`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`;
                         `kp:num->real^3->real^3`; `i:num`; `z:real^3`; `z':real^3`]
                        P2CL_KP_INJ) THEN
    ASM_REWRITE_TAC[]]);;

let P2CE_F_SUC_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs k l z.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z IN p2cg_dm rho (cs l)
     ==> p2ce_F top atlas h yc rho kp cs k (SUC l) (kp (cs l) z) =
         if norm z < rho(NUMFST(cs l)) / &6
         then p2cg_nch top atlas h yc k (cs l)
                ((&1 - p2ce_mu rho (cs l) z) %
                 p2ce_L top atlas h yc rho k (cs l)
                   (p2ce_F top atlas h yc rho kp cs k l (kp (cs l) z)) +
                 p2ce_mu rho (cs l) z % z)
         else p2ce_F top atlas h yc rho kp cs k l (kp (cs l) z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2CE_KP_FACTS th) THEN
                       STRIP_ASSUME_TAC(MATCH_MP P2CE_CTX_FACTS th)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2CG_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(kp:num->real^3->real^3) (cs l) z IN
                IMAGE (kp (cs l)) (ball(vec 0,rho(NUMFST((cs:num->num) l)) / &6)) <=>
                norm z < rho(NUMFST(cs l)) / &6`
  ASSUME_TAC THENL
   [EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^3 = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(cs:num->num) l` THEN
      ASM_REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  REWRITE_TAC[P2CE_F_SUC] THEN ASM_SIMP_TAC[]);;

(* The blend step near a point of the chart where the previous map is good. *)

let P2CE_GOOD_BLEND = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs l w0.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     w0 IN p2cg_dm rho (cs l) /\
     p2ce_good top atlas h yc rho kp sq (\n. p2ce_F top atlas h yc rho kp cs (sq n) l)
               (cs l) w0
     ==> p2ce_good top atlas h yc rho kp sq
           (\n. p2ce_F top atlas h yc rho kp cs (sq n) (SUC l)) (cs l) w0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_KP_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`]) P2CE_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2CG_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N1:num` (LABEL_TAC "ld")) (LABEL_TAC "nr"))))) THEN
  SUBGOAL_THEN
   `smooth_map_on (ball(w0:real^3,&1)) (\z. lift(p2ce_mu rho ((cs:num->num) l) z)) /\
    smooth_map_on (ball(w0:real^3,&1)) (\z. lift(&1 - p2ce_mu rho ((cs:num->num) l) z))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      DISCH_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ci_near w0
      (\n:num z. (&1 - p2ce_mu rho (cs l) z) %
             p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) (cs l)
               (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l (kp (cs l) z)) +
             p2ce_mu rho (cs l) z % z)
      (\z:real^3. z)`
  (LABEL_TAC "nb") THENL
   [MP_TAC(ISPECL [`w0:real^3`;
                   `\n:num z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n)
                            (cs l) (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l
                                      (kp (cs l) z))`;
                   `\z:real^3. z`; `\z. lift(&1 - p2ce_mu rho ((cs:num->num) l) z)`; `&1`]
                  P2CI_NEAR_SMUL) THEN
    ASM_REWRITE_TAC[REAL_LT_01; LIFT_DROP] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w0:real^3`; `\n:num z:real^3. z`; `\z:real^3. z`;
                   `\z. lift(p2ce_mu rho ((cs:num->num) l) z)`; `&1`] P2CI_NEAR_SMUL) THEN
    ASM_REWRITE_TAC[REAL_LT_01; LIFT_DROP] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_ID];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`w0:real^3`;
                   `\n:num z. (&1 - p2ce_mu rho ((cs:num->num) l) z) %
                          p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n)
                            (cs l) (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l
                                      (kp (cs l) z))`;
                   `\z:real^3. (&1 - p2ce_mu rho ((cs:num->num) l) z) % z`;
                   `\n:num z:real^3. p2ce_mu rho ((cs:num->num) l) z % z`;
                   `\z:real^3. p2ce_mu rho ((cs:num->num) l) z % z`] P2CI_NEAR_ADD) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_ARITH `(&1 - m) % z + m % z:real^3 = z`];
    ALL_TAC] THEN
  USE_THEN "nb" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `rho(NUMFST((cs:num->num) l)) / &8`)))))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "nu")) THEN
  SUBGOAL_THEN
   `!n z. N1 + N2 + p2cg_nv N0 Nn ((cs:num->num) l) <= n /\ z IN ball(w0,min r ru)
          ==> p2ce_F top atlas h yc rho kp cs (sq n) (SUC l) (kp (cs l) z) =
              p2cg_nch top atlas h yc (sq n) (cs l)
                ((&1 - p2ce_mu rho (cs l) z) %
                 p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) (cs l)
                   (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l
                      (kp (cs l) z)) +
                 p2ce_mu rho (cs l) z % z) /\
              (&1 - p2ce_mu rho (cs l) z) %
                 p2ce_L top atlas h yc rho (sq n) (cs l)
                   (p2ce_F top atlas h yc rho kp cs (sq n) l (kp (cs l) z)) +
              p2ce_mu rho (cs l) z % z IN ball(vec 0,rho(NUMFST(cs l)))`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN ball(w0,r) /\ z IN ball(w0,ru)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(w0,min r ru)` THEN REWRITE_TAC[IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN p2cg_dm rho ((cs:num->num) l)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(w0,r)` THEN
      UNDISCH_TAC `ball(w0:real^3,r) SUBSET p2cg_dm rho ((cs:num->num) l)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn ((cs:num->num) l) <= (sq:num->num) n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `(sq:num->num) n`; `l:num`; `z:real^3`])
                    P2CE_F_SUC_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `p2ce_mu rho ((cs:num->num) l) z = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `&0`))
                        (rand(concl th)) && is_forall(concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`; `(sq:num->num) n`]) P2CE_L_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `p2ce_F top atlas (h:num->A->real^3^3) yc rho
                                  (kp:num->real^3->real^3) cs ((sq:num->num) n) l
                                  (kp (cs l) z)` o
                 CONJUNCT2) THEN
      ANTS_TAC THENL
       [USE_THEN "ld" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "nu" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_BALL_0] THEN
      MATCH_MP_TAC(NORM_ARITH `norm(z:real^3) < r / &4 /\ &0 < r
                               ==> norm(b - z) < r / &8 ==> norm b < r`) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN p2cg_dm rho ((cs:num->num) l)` THEN
      REWRITE_TAC[p2cg_dm; IN_BALL_0]];
    ALL_TAC] THEN
  EXISTS_TAC `min r ru` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w0:real^3,r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    EXISTS_TAC `N1 + N2 + p2cg_nv N0 Nn ((cs:num->num) l)` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    EXISTS_TAC
     `\n:num z. (&1 - p2ce_mu rho ((cs:num->num) l) z) %
            p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) (cs l)
              (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l (kp (cs l) z)) +
            p2ce_mu rho (cs l) z % z` THEN
    EXISTS_TAC `\z:real^3. z` THEN
    MAP_EVERY EXISTS_TAC [`min r ru`; `N1 + N2 + p2cg_nv N0 Nn ((cs:num->num) l)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn ((cs:num->num) l) <= (sq:num->num) n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`; `(sq:num->num) n`]) P2CE_L_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]]);;

(* Where the cutoff is 1 the patched map is the normal chart map. *)

let P2CE_GOOD_RESET = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs l w0.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     norm w0 < rho(NUMFST(cs l)) / &7
     ==> p2ce_good top atlas h yc rho kp sq
           (\n. p2ce_F top atlas h yc rho kp cs (sq n) (SUC l)) (cs l) w0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`]) P2CE_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mu1")
    (CONJUNCTS_THEN2 (LABEL_TAC "mu0") ASSUME_TAC))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2CG_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho(NUMFST((cs:num->num) l)) / &7 - norm(w0:real^3) /\
                !z:real^3. z IN ball(w0,rho(NUMFST(cs l)) / &7 - norm w0)
                           ==> norm z < rho(NUMFST(cs l)) / &7`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`z:real^3`; `w0:real^3`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`z:real^3`; `w0:real^3`] NORM_SUB) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n z. p2cg_nv N0 Nn ((cs:num->num) l) <= n /\
          z IN ball(w0,rho(NUMFST(cs l)) / &7 - norm(w0:real^3))
          ==> p2ce_F top atlas h yc rho kp cs ((sq:num->num) n) (SUC l)
                ((kp:num->real^3->real^3) (cs l) z) =
              p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3) yc (sq n) (cs l) z /\
              z IN ball(vec 0,rho(NUMFST(cs l))) /\
              p2cg_nv N0 Nn (cs l) <= sq n`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST((cs:num->num) l)) / &7` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&7`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `(sq:num->num) n`; `l:num`; `z:real^3`])
                    P2CE_F_SUC_CHART) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST((cs:num->num) l)) / &6 /\
                    p2ce_mu rho (cs l) z = &1` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "mu1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
      REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2ce_good] THEN
  EXISTS_TAC `rho(NUMFST((cs:num->num) l)) / &7 - norm(w0:real^3)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; p2cg_dm; IN_BALL_0] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x < r / &7 /\ &0 < r ==> x < r / &4`) THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `p2cg_nv N0 Nn ((cs:num->num) l)` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    MAP_EVERY EXISTS_TAC [`\n:num z:real^3. z`; `\z:real^3. z`;
                          `rho(NUMFST((cs:num->num) l)) / &7 - norm(w0:real^3)`;
                          `p2cg_nv N0 Nn ((cs:num->num) l)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_ID];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`; `(sq:num->num) n`]) P2CE_L_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]]);;

(* Away from the closed patch kp b (cball(0,rho/6)) a step changes nothing. *)

let P2CE_FAR_BALL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp b c z0.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z0 IN p2cg_dm rho c /\
     ~(kp c z0 IN IMAGE (kp b) (cball(vec 0,rho(NUMFST b) / &6)))
     ==> ?r. &0 < r /\
             !z. z IN ball(z0,r)
                 ==> ~(kp c z IN IMAGE (kp b) (cball(vec 0,rho(NUMFST b) / &6)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2CC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(b:num)`]) P2CG_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE ((kp:num->real^3->real^3) b) (cball(vec 0,rho(NUMFST(b:num)) / &6))` THEN
  SUBGOAL_THEN `closed_in (p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) S` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (p2cg_dm rho (b:num))` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
      REWRITE_TAC[SUBSET; p2cg_dm; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CC_KP_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | z IN p2cg_dm rho c /\
              (kp:num->real^3->real^3) c z IN
              topspace(p2cl_top (p2cg_dm rho) kp) DIFF S}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `p2cg_dm rho c` THEN
    REWRITE_TAC[p2cg_dm; OPEN_BALL] THEN
    MP_TAC(ISPECL [`(kp:num->real^3->real^3) c`;
                   `subtopology euclidean (p2cg_dm rho c)`;
                   `p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) DIFF S`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; p2cg_dm] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM p2cg_dm] THEN MATCH_MP_TAC P2CC_KP_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `c:num` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC `ball(z0:real^3,r) SUBSET
               {z | z IN p2cg_dm rho c /\
                    (kp:num->real^3->real^3) c z IN
                    topspace(p2cl_top (p2cg_dm rho) kp) DIFF S}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN ASM_MESON_TAC[]);;

let P2CE_GOOD_FAR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs l c z0.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z0 IN p2cg_dm rho c /\
     ~(kp c z0 IN IMAGE (kp (cs l)) (cball(vec 0,rho(NUMFST(cs l)) / &6))) /\
     p2ce_good top atlas h yc rho kp sq (\n. p2ce_F top atlas h yc rho kp cs (sq n) l) c z0
     ==> p2ce_good top atlas h yc rho kp sq
           (\n. p2ce_F top atlas h yc rho kp cs (sq n) (SUC l)) c z0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MATCH_MP_TAC P2CE_GOOD_EQ THEN
  EXISTS_TAC `\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                         (kp:num->real^3->real^3) cs ((sq:num->num) n) l` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (p2ce_std @ [`(cs:num->num) l`; `c:num`; `z0:real^3`]) P2CE_FAR_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `0`] THEN ASM_REWRITE_TAC[LE_0] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN DISCH_TAC THEN
  REWRITE_TAC[P2CE_F_SUC] THEN
  SUBGOAL_THEN `~((kp:num->real^3->real^3) c z IN
                  IMAGE (kp ((cs:num->num) l)) (ball(vec 0,rho(NUMFST(cs l)) / &6)))`
  (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(SET_RULE `!f:real^3->real^3 s t. s SUBSET t ==> x IN IMAGE f s ==> x IN IMAGE f t`) THEN
  REWRITE_TAC[BALL_SUBSET_CBALL]);;

(* ------------------------------------------------------------------------- *)
(* The induction over the patches, the covering of the closure               *)
(* of W j by the patches at level j + 2, and the base point.  With the chart *)
(* list p2ce_cs P j (the charts (j + 2, i), i < P (j + 2), in decreasing     *)
(* order, so that the last patch is the chart (j + 2, 0) centred at x k),    *)
(* the final patched map is good in every chart at every point of the        *)
(* closure of W j, and sends the base point xl to x (sq n).                  *)
(* ------------------------------------------------------------------------- *)

let P2CE_OM_SUC = prove
 (`!rho (kp:num->real^3->real^3) cs l.
     p2ce_om rho kp cs (SUC l) =
     p2ce_om rho kp cs l UNION IMAGE (kp (cs l)) (ball(vec 0,rho(NUMFST(cs l)) / &7))`,
  REWRITE_TAC[EXTENSION; p2ce_om; IN_UNION; IN_UNIONS; IN_ELIM_THM; LT] THEN
  MESON_TAC[]);;

let P2CE_INV = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> !l c z0. z0 IN p2cg_dm rho c /\ kp c z0 IN p2ce_om rho kp cs l
                  ==> p2ce_good top atlas h yc rho kp sq
                        (\n. p2ce_F top atlas h yc rho kp cs (sq n) l) c z0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_KP_FACTS) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[p2ce_om; IN_UNIONS; IN_ELIM_THM; LT]; ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN MAP_EVERY X_GEN_TAC [`c:num`; `z0:real^3`] THEN
  REWRITE_TAC[P2CE_OM_SUC; IN_UNION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "or")) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2CG_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(kp:num->real^3->real^3) c z0 IN
                 IMAGE (kp ((cs:num->num) l)) (cball(vec 0,rho(NUMFST(cs l)) / &6))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    SUBGOAL_THEN `(w0:real^3) IN p2cg_dm rho ((cs:num->num) l)` ASSUME_TAC THENL
     [UNDISCH_TAC `(w0:real^3) IN cball(vec 0,rho(NUMFST((cs:num->num) l)) / &6)` THEN
      REWRITE_TAC[p2cg_dm; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas
                                          (h:num->A->real^3^3) yc rho
                                          (kp:num->real^3->real^3) cs ((sq:num->num) n) (SUC l)`;
                                     `(cs:num->num) l`; `c:num`; `w0:real^3`; `z0:real^3`])
                        P2CE_GOOD_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(kp:num->real^3->real^3) c z0 IN p2ce_om rho kp cs l` THENL
     [MATCH_MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `l:num`; `w0:real^3`])
                          P2CE_GOOD_BLEND) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(kp:num->real^3->real^3) c z0 IN p2ce_om rho kp cs l` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) c z0 IN
                  IMAGE (kp ((cs:num->num) l)) (ball(vec 0,rho(NUMFST(cs l)) / &7))`
    MP_TAC THENL
     [REMOVE_THEN "or" MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `l:num`; `w0:real^3`])
                          P2CE_GOOD_RESET) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `w0:real^3 = w1` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `z':real^3`))
                                                     (concl th))) THEN
      EXISTS_TAC `(cs:num->num) l` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(w1:real^3) IN ball(vec 0,rho(NUMFST((cs:num->num) l)) / &7)` THEN
        REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      UNDISCH_TAC `(w1:real^3) IN ball(vec 0,rho(NUMFST((cs:num->num) l)) / &7)` THEN
      REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `l:num`; `c:num`; `z0:real^3`])
                          P2CE_GOOD_FAR) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "or" MP_TAC THEN
  MATCH_MP_TAC(TAUT `~b ==> (a \/ b ==> a)`) THEN
  UNDISCH_TAC `~((kp:num->real^3->real^3) c z0 IN
                 IMAGE (kp ((cs:num->num) l)) (cball(vec 0,rho(NUMFST(cs l)) / &6)))` THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0; IN_CBALL_0; NOT_EXISTS_THM; CONTRAPOS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The chart list at level j + 2 and the covering of the closure of W j. *)

let p2ce_cs = new_definition
 `p2ce_cs (P:num->num) j i = NUMPAIR (j + 2) (P(j + 2) - 1 - i)`;;

let P2CE_COVER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp j SUBSET
         p2ce_om rho kp (p2ce_cs P j) (P(j + 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2CC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `j:num` o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  REWRITE_TAC[SUBSET; p2cc_W; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2ce_std P2CC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(p:real^3) IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3))` THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `a:num`; `z:real^3`]) P2CC_DELTA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `a:num`; `z:real^3`; `j + 2`])
                P2CC_DELTA_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2cc_delta rho D kp (p:real^3) < &(SUC j) + &1` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_ADD; ARITH_RULE `SUC j + 1 = j + 2`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2ce_om; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) (p2ce_cs P j (P(j + 2) - 1 - i)))
                    (ball(vec 0,rho(NUMFST(p2ce_cs P j (P(j + 2) - 1 - i))) / &7))` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `P(j + 2) - 1 - i` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2ce_cs P j (P(j + 2) - 1 - i) = NUMPAIR (j + 2) i` SUBST1_TAC THENL
   [REWRITE_TAC[p2ce_cs] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUMPAIR_DEST; IN_IMAGE; IN_BALL_0] THEN EXISTS_TAC `w:real^3` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The base point. *)

let P2CE_XL_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp J.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> kp (NUMPAIR J 0) (vec 0) = p2cc_xl kp`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`J:num`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`0`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2cg_dv D (NUMPAIR J 0) (vec 0) p2cc_a0 (vec 0) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                   `sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                   `NUMPAIR J 0`; `p2cc_a0`; `vec 0:real^3`; `vec 0:real^3`] P2CG_D_SEQ) THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL; NUMPAIR_DEST; P2CC_A0] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    MATCH_MP_TAC(MESON[REAL_LT_REFL; REAL_ARITH `~(x = &0) ==> &0 < abs x`]
                   `!x. (!e. &0 < e ==> abs x < e) ==> x = &0`) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    ABBREV_TAC `n = N1 + p2cg_nv N0 Nn (NUMPAIR J 0) + p2cg_nv N0 Nn p2cc_a0 +
                    Nn J + Nn 0` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = &0 ==> abs(y - x) < e ==> abs x < e`) THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn (NUMPAIR J 0) <= (sq:num->num) n /\
                  p2cg_nv N0 Nn p2cc_a0 <= sq n /\ Nn J <= sq n`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[p2cg_dk] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR J 0`; `(sq:num->num) n`]) P2CG_NCH_BASIC) THEN
    MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`; `(sq:num->num) n`]) P2CG_NCH_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq(n:num):num`]) P2CC_A0_CTR) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `p2cg_ctr (yc:num->num->num->A) (sq(n:num)) (NUMPAIR J 0) = x(sq n)`
    SUBST1_TAC THENL
     [REWRITE_TAC[p2cg_ctr; NUMPAIR_DEST] THEN
      UNDISCH_TAC `p2cg_levels top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
      REWRITE_TAC[p2cg_levels] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIST_REFL THEN
    UNDISCH_TAC `p2cu_seq top atlas (h:num->A->real^3^3) x` THEN
    REWRITE_TAC[p2cu_seq] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2cc_xl] THEN
  UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)
                         (kp:num->real^3->real^3)` THEN
  REWRITE_TAC[p2cl_glue] THEN
  DISCH_THEN(MP_TAC o SPECL [`NUMPAIR J 0`; `p2cc_a0`; `vec 0:real^3`; `vec 0:real^3`]) THEN
  REWRITE_TAC[p2cg_dm; CENTRE_IN_BALL; NUMPAIR_DEST; P2CC_A0] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[P2CG_IN_OM; CENTRE_IN_BALL; NUMPAIR_DEST; P2CC_A0] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `NUMPAIR J 0`; `p2cc_a0`; `vec 0:real^3`]) P2CG_TR_PROPS) THEN
  ASM_REWRITE_TAC[P2CG_IN_OM; CENTRE_IN_BALL; NUMPAIR_DEST; P2CC_A0] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC);;

let P2CE_BASE = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> 0 < P(j + 2) /\
         ?N. !n. N <= n
                 ==> p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                            (p2cc_xl kp) = x(sq n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`0`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < P(j + 2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `p2cc_a0`; `vec 0:real^3`; `j + 2`])
                  P2CC_DELTA_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[p2cg_dm; CENTRE_IN_BALL; P2CC_A0] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `p2cc_a0`; `vec 0:real^3`]) P2CG_DV_REFL0) THEN
      ASM_REWRITE_TAC[CENTRE_IN_CBALL; P2CC_A0; NORM_0] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `P(j + 2) = SUC(P(j + 2) - 1) /\
                p2ce_cs P j (P(j + 2) - 1) = NUMPAIR (j + 2) 0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2ce_cs] THEN CONJ_TAC THENL [ASM_ARITH_TAC; AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `p2cg_nv N0 Nn (NUMPAIR (j + 2) 0) + Nn(j + 2)` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2cg_nv N0 Nn (NUMPAIR (j + 2) 0) <= (sq:num->num) n /\ Nn(j + 2) <= sq n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `(P:num->num)(j + 2)`)) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j + 2`]) P2CE_XL_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(kp:num->real^3->real^3) (NUMPAIR (j + 2) 0) (vec 0) =
                kp (p2ce_cs P j (P(j + 2) - 1)) (vec 0)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs P j`; `(sq:num->num) n`; `P(j + 2) - 1`;
                             `vec 0:real^3`]) P2CE_F_SUC_CHART) THEN
  ASM_REWRITE_TAC[p2cg_dm; CENTRE_IN_BALL; NORM_0; NUMPAIR_DEST] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR (j + 2) 0`]) P2CE_MU_FACTS) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^3` o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[NORM_0] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR (j + 2) 0`; `(sq:num->num) n`]) P2CG_NCH_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[p2cg_ctr; NUMPAIR_DEST] THEN
  UNDISCH_TAC `p2cg_levels top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
  REWRITE_TAC[p2cg_levels] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The pulled-back metrics.  Pullbacks along compositions,                   *)
(* locality of rfs_pullback, transitions as diffeomorphisms, and the         *)
(* transfer lemma: at y = kp c z, the covariant C^m distance measured in the *)
(* chart chosen by chart_at equals the one in the chart c, where the map is  *)
(* nch c o R near z.  P2CE_MPULLBACK_CHAIN is the chain rule for mpullback   *)
(* (the same statement as APX_MPULLBACK_CHAIN of pc_apx_chain, whose load    *)
(* closure is not needed here).                                              *)
(* ------------------------------------------------------------------------- *)

let P2CE_MPULLBACK_CHAIN = prove
 (`!(h:real^N->real^N) (k:real^N->real^N) G z.
     h differentiable at z /\ k differentiable at (h z)
     ==> mpullback h (mpullback k G) z = mpullback (k o h) G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN
   `frechet_derivative ((k:real^N->real^N) o (h:real^N->real^N)) (at z) =
    frechet_derivative k (at (h z)) o frechet_derivative h (at z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:real^N` THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `z:real^N`; `u:real^N`]
                  LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at z)) /\
                linear(frechet_derivative (k:real^N->real^N) (at (h z)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let P2CE_RFS_LOCAL = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) e' g s w.
     open s /\ w IN s /\ (!v. v IN s ==> e v = e' v)
     ==> rfs_pullback atlas e g w = rfs_pullback atlas e' g w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback] THEN
  SUBGOAL_THEN `(e:real^N->A) w = e' w` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[o_THM]);;

let P2CE_RFS_CHAIN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) (R:real^N->real^N) g w.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
     R differentiable at w /\ R w IN s
     ==> rfs_pullback atlas (e o R) g w = mpullback R (rfs_pullback atlas e g) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->A) (R(w:real^N)) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> can (find_term ((=) `IMAGE (e:real^N->A) s`)) (concl th) &&
                       can (find_term ((=) `open_in:(A topology)->(A->bool)->bool`)) (concl th))) THEN
    MATCH_MP_TAC(SET_RULE `(x:A) IN s ==> s SUBSET t ==> x IN t`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A)(R(w:real^N))`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mpullback (R:real^N->real^N) (rfs_pullback atlas (e:real^N->A) (g:A->real^N^N)) w =
    mpullback R (mpullback (SND(chart_at atlas (e(R w))) o e)
                           (metric_local atlas (chart_at atlas (e(R w))) g)) w`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN REWRITE_TAC[rfs_pullback]; ALL_TAC] THEN
  SUBGOAL_THEN `(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A)(R w))) o e)
                differentiable at ((R:real^N->real^N) w)` ASSUME_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC P2CG_PARAM_CHART_DIFF THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2CE_MPULLBACK_CHAIN] THEN REWRITE_TAC[rfs_pullback; o_ASSOC; o_THM]);;

let P2CE_TR_DIFFEO = prove
 (`!(Dm:num->real^N->bool) Om Tr a b U.
     p2cl_system Dm Om Tr /\ open U /\ U SUBSET Om a b
     ==> open (IMAGE (Tr a b) U) /\ IMAGE (Tr a b) U SUBSET Om b a /\
         diffeomorphism_on (IMAGE (Tr a b) U) U (Tr b a) (Tr a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cl_system] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u:real^N. u IN U ==> (Tr:num->num->real^N->real^N) a b u IN Om b a /\
                                       Tr b a (Tr a b u) = u`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN Om b a ==> (Tr:num->num->real^N->real^N) b a v IN Om a b /\
                                            Tr a b (Tr b a v) = v`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE ((Tr:num->num->real^N->real^N) a b) U)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE ((Tr:num->num->real^N->real^N) a b) U =
                  {v | v IN Om b a /\ Tr b a v IN U}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((Tr:num->num->real^N->real^N) a b) U SUBSET Om b a` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(Om:num->num->real^N->bool) b a` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(Om:num->num->real^N->bool) a b` THEN
    ASM_REWRITE_TAC[]]);;

let P2CE_G_FIELD = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> metric_field (ball(vec 0,rho(NUMFST a))) (p2cg_G top atlas h yc k a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2CE_SEQ_MFD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `NUMFST a` o CONJUNCT1 o REWRITE_RULE[p2cg_levels]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) yc k a`; `(rho:num->real)(NUMFST a)`;
                 `(K:num->real)(NUMFST a)`] P2CU_EXPMETRIC_FACTS) THEN
  ASM_REWRITE_TAC[p2cg_G] THEN SIMP_TAC[]);;

(* The transfer lemma. *)

let P2CE_LCK_TRANSFER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    k (Fm:real^3->A) (R:real^3->real^3) R' c z s m.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     p2cg_nv N0 Nn c <= k /\ &0 < s /\ ball(z,s) SUBSET p2cg_dm rho c /\
     diffeomorphism_on (ball(z,s)) (IMAGE R (ball(z,s))) R R' /\
     IMAGE R (ball(z,s)) SUBSET ball(vec 0,rho(NUMFST c)) /\
     (!w. w IN ball(z,s) ==> Fm(kp c w) = p2cg_nch top atlas h yc k c (R w))
     ==> lck_dist2 m
           (metric_local (p2cl_atlas (p2cg_dm rho) kp)
              (chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z))
              (p2cl_metric (p2cg_dm rho) kp Gl))
           (\w. rfs_pullback (atlas k)
                  (Fm o chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z)))
                  (h k) w)
           (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z)) (kp c z)) =
         lck_dist2 m (Gl c) (mpullback R (p2cg_G top atlas h yc k c)) z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  SUBGOAL_THEN `(z:real^3) IN p2cg_dm rho c` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z:real^3,s) SUBSET p2cg_dm rho c` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `kp:num->real^3->real^3`;
                 `c:num`; `z:real^3`] P2CL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open(p2cg_om rho D c i) /\
                p2cg_om rho D i c SUBSET p2cg_dm rho i /\
                (!v. v IN p2cg_om rho D i c
                     ==> p2cg_tr rho D i c v IN p2cg_om rho D c i) /\
                smooth_map_on (p2cg_om rho D i c) (p2cg_tr rho D i c) /\
                p2cg_tr rho D i c (p2cg_tr rho D c i z) = z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
    REWRITE_TAC[p2cl_system] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U = ball(z:real^3,s) INTER p2cg_om rho D c i` THEN
  SUBGOAL_THEN `open (U:real^3->bool) /\ (z:real^3) IN U /\ U SUBSET p2cg_om rho D c i /\
                U SUBSET ball(z,s)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET; IN_INTER;
                                     CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `c:num`; `i:num`;
                 `U:real^3->bool`] P2CE_TR_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (p2cg_tr rho D i c) (IMAGE (p2cg_tr rho D c i) U) = U /\
                smooth_map_on (ball(z:real^3,s)) (R:real^3->real^3) /\
                open (IMAGE (R:real^3->real^3) (ball(z,s)))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (IMAGE (p2cg_tr rho D c i) U) U (p2cg_tr rho D i c)
                                   (p2cg_tr rho D c i)` THEN
    UNDISCH_TAC `diffeomorphism_on (ball(z:real^3,s)) (IMAGE (R:real^3->real^3) (ball(z,s))) R (R':real^3->real^3)` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U ((Gl:num->real^3->real^3^3) c) /\
                metric_field U (mpullback (R:real^3->real^3)
                                 (p2cg_G top atlas (h:num->A->real^3^3) yc k c))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8)` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:real^3,s)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `p2cg_dm rho c` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[p2cg_dm] THEN MATCH_MP_TAC SUBSET_BALL THEN
      MP_TAC(ISPECL (p2cg_std @ [`NUMFST(c:num)`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(z:real^3,s)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (R:real^3->real^3) (ball(z,s))`; `R':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST(c:num)))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2CE_G_FIELD THEN EXISTS_TAC `x:num->A` THEN
      MAP_EVERY EXISTS_TAC [`K:num->real`; `N0:num->num`; `B:num->num->real`;
                            `NB:num->num->num`; `P:num->num`; `Nn:num->num`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (mpullback (p2cg_tr rho D i c) ((Gl:num->real^3->real^3^3) c))
                (mpullback (p2cg_tr rho D i c)
                   (mpullback (R:real^3->real^3)
                      (p2cg_G top atlas (h:num->A->real^3^3) yc k c)))
                (p2cg_tr rho D c i z)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`m:num`; `U:real^3->bool`; `IMAGE (p2cg_tr rho D c i) U`;
                   `p2cg_tr rho D i c`; `p2cg_tr rho D c i`; `(Gl:num->real^3->real^3^3) c`;
                   `mpullback (R:real^3->real^3) (p2cg_G top atlas (h:num->A->real^3^3) yc k c)`;
                   `p2cg_tr rho D c i z`] LCK_DIST2_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]] THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `IMAGE (p2cg_tr rho D c i) U` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^3) IN p2cg_om rho D i c /\ v IN p2cg_dm rho i /\
                p2cg_tr rho D i c v IN U` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      UNDISCH_TAC `(v:real^3) IN IMAGE (p2cg_tr rho D c i) U` THEN
      UNDISCH_TAC `IMAGE (p2cg_tr rho D i c) (IMAGE (p2cg_tr rho D c i) U) = U` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `kp:num->real^3->real^3`;
                   `Gl:num->real^3->real^3^3`; `i:num`; `v:real^3`] P2CL_METRIC_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `c:num`; `v:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `Gl:num->real^3->real^3^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the pulled-back metric through the chart i *)
  ABBREV_TAC `Tq = p2cg_tr rho D i c` THEN
  SUBGOAL_THEN `(Tq:real^3->real^3) differentiable at v /\
                (R:real^3->real^3) differentiable at (Tq v) /\
                (R o Tq) v IN ball(vec 0:real^3,rho(NUMFST(c:num)))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `p2cg_om rho D i c` THEN
      EXPAND_TAC "Tq" THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
      REWRITE_TAC[p2cl_system] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(z:real^3,s)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
      REWRITE_TAC[o_THM] THEN
      UNDISCH_TAC `IMAGE (R:real^3->real^3) (ball(z,s)) SUBSET ball(vec 0,rho(NUMFST(c:num)))` THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> IMAGE (f:real^3->real^3) s SUBSET t ==> f x IN t`) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`atlas (k:num):((A->bool)#(A->real^3))->bool`;
                 `(Fm:real^3->A) o chart_inv (p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) i)`;
                 `p2cg_nch top atlas (h:num->A->real^3^3) yc k c o ((R:real^3->real^3) o (Tq:real^3->real^3))`;
                 `(h:num->A->real^3^3) k`; `IMAGE (p2cg_tr rho D c i) U`; `v:real^3`]
                P2CE_RFS_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v':real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v':real^3) IN p2cg_om rho D i c /\ v' IN p2cg_dm rho i /\
                  (Tq:real^3->real^3) v' IN U` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM SET_TAC[]; ASM SET_TAC[];
        UNDISCH_TAC `(v':real^3) IN IMAGE (p2cg_tr rho D c i) U` THEN
        UNDISCH_TAC `IMAGE (Tq:real^3->real^3) (IMAGE (p2cg_tr rho D c i) U) = U` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `kp:num->real^3->real^3`;
                   `i:num`; `v':real^3`] P2CL_CHART_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) i v' = kp c (Tq v')` SUBST1_TAC THENL
     [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)
                             (kp:num->real^3->real^3)` THEN
      REWRITE_TAC[p2cl_glue] THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `c:num`; `v':real^3`; `(Tq:real^3->real^3) v'`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "Tq" THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `ball(vec 0:real^3,rho(NUMFST(c:num)))`;
                 `p2cg_nch top atlas (h:num->A->real^3^3) yc k c`; `(R:real^3->real^3) o (Tq:real^3->real^3)`;
                 `(h:num->A->real^3^3) k`; `v:real^3`] P2CE_RFS_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2CE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(ISPECL (p2cg_std @ [`c:num`; `k:num`]) P2CE_NCH_PARAM) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback ((R:real^3->real^3) o (Tq:real^3->real^3)) (p2cg_G top atlas (h:num->A->real^3^3) yc k c) v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ISPECL (p2cg_std @ [`c:num`; `k:num`;
                                     `((R:real^3->real^3) o (Tq:real^3->real^3)) v`])
                        P2CE_G_RFS) THEN
    ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CE_MPULLBACK_CHAIN THEN ASM_REWRITE_TAC[]]);;

(* The local estimate near a point where the maps are good. *)

let P2CE_MPULLBACK_ID = prove
 (`!(G:real^N->real^N^N). mpullback (\z. z) G = G`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; mpullback] THEN X_GEN_TAC `y:real^N` THEN
  MP_TAC(ISPEC `at (y:real^N)` HAS_DERIVATIVE_ID) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P2CE_GLIMIT_NEAR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp c z0.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ z0 IN p2cg_dm rho c
     ==> p2ci_near z0
           (\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                p2cg_G top atlas h yc (sq n) c)
           (vectorize o Gl c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `p2cg_G:(num->A topology)->(num->((A->bool)#(A->real^3))->bool)->(num->A->real^3^3)->(num->num->num->A)->num->num->real^3->real^3^3`)) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pc"))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(c:num)`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ball(z0:real^3,rho(NUMFST(c:num)) / &8) SUBSET
                ball(vec 0,&3 * rho(NUMFST c) / &8) /\
                ball(z0:real^3,rho(NUMFST(c:num)) / &8) SUBSET ball(vec 0,rho(NUMFST c))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN
    REWRITE_TAC[p2cg_dm; SUBSET; IN_BALL_0; IN_BALL] THEN DISCH_TAC THEN
    CONJ_TAC THEN X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`z0:real^3`; `w:real^3`] DIST_TRIANGLE_LE) THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `z0:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
    REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `rho(NUMFST(c:num)) / &8` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `p2cg_nv N0 Nn c` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST(c:num)))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`c:num`; `(sq:num->num) n`]) P2CE_G_FIELD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[metric_field]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `metric_field (ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8))
                              ((Gl:num->real^3->real^3^3) c)` THEN
    SIMP_TAC[metric_field];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pc" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                   C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:3)) l`) o SPEC `l:num list`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kn:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let P2CE_LOCAL_LCK = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fs:num->real^3->A) c z0 m eta.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z0 IN p2cg_dm rho c /\ p2ce_good top atlas h yc rho kp sq Fs c z0 /\ &0 < eta
     ==> ?r N. &0 < r /\
               !n z. N <= n /\ z IN ball(z0,r)
                     ==> lck_dist2 m
                           (metric_local (p2cl_atlas (p2cg_dm rho) kp)
                              (chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z))
                              (p2cl_metric (p2cg_dm rho) kp Gl))
                           (\w. rfs_pullback (atlas (sq n))
                                  (Fs n o chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp)
                                                              (kp c z)))
                                  (h (sq n)) w)
                           (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z)) (kp c z)) <
                         eta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(c:num)`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `rg:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `Ng:num` (LABEL_TAC "lg")) (LABEL_TAC "ng"))))) THEN
  USE_THEN "ng" (MP_TAC o MATCH_MP P2CE_NEAR_ID_DIFFEO) THEN
  DISCH_THEN(X_CHOOSE_THEN `rd:real` (X_CHOOSE_THEN `Nd:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd")))) THEN
  USE_THEN "ng" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `rho(NUMFST(c:num)) / &8`)))))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nu:num` (LABEL_TAC "nu")) THEN
  (* the lck estimate in the chart c *)
  MP_TAC(ISPECL [`ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8)`;
                 `(Gl:num->real^3->real^3^3) c`;
                 `\n:num. mpullback (\z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3)
                                           yc rho (sq n) c ((Fs:num->real^3->A) n
                                           ((kp:num->real^3->real^3) c z)))
                                    (p2cg_G top atlas h yc (sq n) c)`;
                 `z0:real^3`; `m:num`] P2CI_LCK_NEAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`z0:real^3`;
                     `\n z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) c
                              ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) c z))`;
                     `\z:real^3. z`;
                     `\n:num. p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) yc (sq n) c`;
                     `(Gl:num->real^3->real^3^3) c`] P2CI_NEAR_MPULLBACK) THEN
      REWRITE_TAC[P2CE_MPULLBACK_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL (p2ce_std @ [`c:num`; `z0:real^3`]) P2CE_GLIMIT_NEAR) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(X_CHOOSE_THEN `rl:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `eta:real`)))))) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nl:num` (LABEL_TAC "nl")) THEN
  EXISTS_TAC `min rg (min rd (min ru rl)) / &2` THEN
  EXISTS_TAC `Ng + Nd + Nu + Nl + p2cg_nv N0 Nn c` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `r = min rg (min rd (min ru rl)) / &2` THEN
  SUBGOAL_THEN `ball(z:real^3,r) SUBSET ball(z0,rg) /\ ball(z:real^3,r) SUBSET ball(z0,rd) /\
                ball(z:real^3,r) SUBSET ball(z0,ru) /\ (z:real^3) IN ball(z0,rl) /\ &0 < r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(z0,r)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `w:real^3` THEN DISCH_TAC) THEN
    TRY(MP_TAC(ISPECL [`z0:real^3`; `z:real^3`; `w:real^3`] DIST_TRIANGLE)) THEN
    EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cg_nv N0 Nn c <= (sq:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "dd" (MP_TAC o SPECL [`n:num`; `ball(z:real^3,r)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Ri:real^3->real^3`) THEN
  MP_TAC(ISPECL (p2ce_std @ [`(sq:num->num) n`; `(Fs:num->real^3->A) n`;
                             `\w. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                    (sq n) c ((Fs:num->real^3->A) n
                                    ((kp:num->real^3->real^3) c w))`;
                             `Ri:real^3->real^3`; `c:num`; `z:real^3`; `r:real`; `m:num`])
                P2CE_LCK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^3,rg)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^3` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^3) IN ball(z0,ru) /\ w IN p2cg_dm rho c` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "nu" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3) IN p2cg_dm rho c` THEN REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN
      MP_TAC(ISPECL [`p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                        ((sq:num->num) n) c ((Fs:num->real^3->A) n
                        ((kp:num->real^3->real^3) c w))`; `w:real^3`] NORM_TRIANGLE_SUB) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL (p2cg_std @ [`c:num`; `(sq:num->num) n`]) P2CE_L_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `(Fs:num->real^3->A) n ((kp:num->real^3->real^3) c w)` o
                 CONJUNCT2) THEN
      ANTS_TAC THENL
       [USE_THEN "lg" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
        SIMP_TAC[]]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
  USE_THEN "nl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Uniformity on the compact closure of W j. *)

let P2CE_COMPACT_EVENTUALLY = prove
 (`!top (K:B->bool) (Q:num->B->bool).
     compact_in top K /\
     (!y. y IN K ==> ?U N. open_in top U /\ y IN U /\ !n z. N <= n /\ z IN U ==> Q n z)
     ==> ?N. !n z. N <= n /\ z IN K ==> Q n z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->B->bool` (X_CHOOSE_THEN `NN:B->num` (LABEL_TAC "u"))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (U:B->B->bool) K`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    USE_THEN "u" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:B->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `IMAGE (NN:B->num) C` num_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y:B. y IN C /\ (z:B) IN (U:B->B->bool) y` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:B->bool) SUBSET UNIONS (IMAGE (U:B->B->bool) C)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:B`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN K` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN C` THEN UNDISCH_TAC `(C:B->bool) SUBSET K` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "u" (MP_TAC o C MP (ASSUME `(y:B) IN K`) o SPEC `y:B`) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[]);;

let P2CE_LCK_UNIFORM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j m eta.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ &0 < eta
     ==> ?N. !n y. N <= n /\
                   y IN p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp j
                   ==> lck_dist2 m
                         (metric_local (p2cl_atlas (p2cg_dm rho) kp)
                            (chart_at (p2cl_atlas (p2cg_dm rho) kp) y)
                            (p2cl_metric (p2cg_dm rho) kp Gl))
                         (\w. rfs_pullback (atlas (sq n))
                                (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)) o
                                 chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp) y))
                                (h (sq n)) w)
                         (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) y) y) < eta`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2CC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2ce_std P2CC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CE_COMPACT_EVENTUALLY THEN
  EXISTS_TAC `p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3))`
  MP_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp j` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^3) IN s ==> x IN t`) THEN
    REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3)
                                     yc rho (kp:num->real^3->real^3) (p2ce_cs P j)
                                     ((sq:num->num) n) (P(j + 2))`;
                             `c:num`; `z0:real^3`; `m:num`; `eta:real`]) P2CE_LOCAL_LCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs P j`]) P2CE_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_COVER) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y0:real^3) IN p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp j` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) c) (ball(z0,min r (rho(NUMFST c) / &4 - norm(z0:real^3))))` THEN
  EXISTS_TAC `N:num` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN
    REWRITE_TAC[p2cg_dm; SUBSET; IN_BALL; IN_BALL_0] THEN DISCH_TAC THEN
    X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `z0:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
    REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
    UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN ball(z0,min r (rho(NUMFST(c:num)) / &4 - norm(z0:real^3)))` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity.  Goodness at every point of a compact set S in               *)
(* a chart gives uniform data on balls of a fixed radius around S (landing,  *)
(* smoothness, |w - w'| <= 2 |R w - R w'|, invertible derivative, uniform    *)
(* closeness to the identity).  At level J the final maps are then           *)
(* eventually injective on the union of the chart images of                  *)
(* cball(0,2 rho_J / 15): if two points have the same image, their D-        *)
(* distance is small, so they lie in one ball of the same chart, where the   *)
(* map is injective.                                                         *)
(* ------------------------------------------------------------------------- *)

let P2CE_FINITE_MIN = prove
 (`!(f:A->real) s.
     FINITE s /\ (!x. x IN s ==> &0 < f x) ==> ?d. &0 < d /\ !x. x IN s ==> d <= f x`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o C MP (ASSUME `!x:A. x IN t ==> &0 < f x`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d ((f:A->real) a)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL]);;

let P2CE_GOOD_UNIFORM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fs:num->real^3->A) c S.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     compact S /\ (!z. z IN S ==> p2ce_good top atlas h yc rho kp sq Fs c z)
     ==> ?lam N.
           &0 < lam /\
           (!n z. N <= n /\ z IN S
                  ==> ball(z,lam) SUBSET p2cg_dm rho c /\
                      (!w. w IN ball(z,lam)
                           ==> Fs n (kp c w) IN IMAGE (p2cg_nch top atlas h yc (sq n) c)
                                                      (ball(vec 0,rho(NUMFST c)))) /\
                      smooth_map_on (ball(z,lam))
                        (\w. p2ce_L top atlas h yc rho (sq n) c (Fs n (kp c w))) /\
                      (!w w'. w IN ball(z,lam) /\ w' IN ball(z,lam)
                              ==> norm(w - w') <=
                                  &2 * norm(p2ce_L top atlas h yc rho (sq n) c (Fs n (kp c w)) -
                                            p2ce_L top atlas h yc rho (sq n) c
                                              (Fs n (kp c w')))) /\
                      (!w. w IN ball(z,lam)
                           ==> ~(det(matrix(frechet_derivative
                                    (\w. p2ce_L top atlas h yc rho (sq n) c (Fs n (kp c w)))
                                    (at w))) = &0))) /\
           (!e. &0 < e
                ==> ?Ne. !n z w. Ne <= n /\ z IN S /\ w IN ball(z,lam)
                                 ==> norm(p2ce_L top atlas h yc rho (sq n) c
                                            (Fs n (kp c w)) - w) < e)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gd"))) THEN
  (* local data at each point *)
  SUBGOAL_THEN
   `!z0. z0 IN S
         ==> ?r M. &0 < r /\
                   (!n. M <= n
                        ==> ball(z0,r) SUBSET p2cg_dm rho c /\
                            (!w. w IN ball(z0,r)
                                 ==> (Fs:num->real^3->A) n (kp c w) IN
                                     IMAGE (p2cg_nch (top:num->A topology) atlas
                                              (h:num->A->real^3^3) yc (sq n) c)
                                           (ball(vec 0,rho(NUMFST c)))) /\
                            smooth_map_on (ball(z0,r))
                              (\w. p2ce_L top atlas h yc rho (sq n) c
                                     (Fs n ((kp:num->real^3->real^3) c w))) /\
                            (!w w'. w IN ball(z0,r) /\ w' IN ball(z0,r)
                                    ==> norm(w - w') <=
                                        &2 * norm(p2ce_L top atlas h yc rho (sq n) c
                                                    (Fs n (kp c w)) -
                                                  p2ce_L top atlas h yc rho (sq n) c
                                                    (Fs n (kp c w')))) /\
                            (!w. w IN ball(z0,r)
                                 ==> ~(det(matrix(frechet_derivative
                                          (\w. p2ce_L top atlas h yc rho (sq n) c
                                                 (Fs n (kp c w))) (at w))) = &0))) /\
                   (!e. &0 < e
                        ==> ?Ne. !n w. Ne <= n /\ w IN ball(z0,r)
                                       ==> norm(p2ce_L top atlas h yc rho (sq n) c
                                                  (Fs n (kp c w)) - w) < e)`
  MP_TAC THENL
   [X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
    USE_THEN "gd" (MP_TAC o C MP (ASSUME `(z0:real^3) IN S`) o SPEC `z0:real^3`) THEN
    REWRITE_TAC[p2ce_good] THEN
    DISCH_THEN(X_CHOOSE_THEN `rg:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `Ng:num` (LABEL_TAC "lg")) (LABEL_TAC "ng"))))) THEN
    USE_THEN "ng" (MP_TAC o MATCH_MP P2CE_NEAR_ID_INJ) THEN
    DISCH_THEN(X_CHOOSE_THEN `ri:real` (X_CHOOSE_THEN `Ni:num`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))) THEN
    USE_THEN "ng" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cl")))))) THEN
    EXISTS_TAC `min rg (min ri ru)` THEN EXISTS_TAC `Ng + Ni:num` THEN
    SUBGOAL_THEN `ball(z0:real^3,min rg (min ri ru)) SUBSET ball(z0,rg) /\
                  ball(z0:real^3,min rg (min ri ru)) SUBSET ball(z0,ri) /\
                  ball(z0:real^3,min rg (min ri ru)) SUBSET ball(z0,ru)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "inj" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^3,rg)` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN USE_THEN "lg" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^3,ri)` THEN
        ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `&2`)) (concl th))) THEN ASM SET_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
          can (find_term ((=) `det:real^3^3->real`)) (concl th) && is_forall(concl th))) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]]];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "cl" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Ne:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real` (X_CHOOSE_THEN `M:real^3->num` (LABEL_TAC "loc"))) THEN
  (* a finite subcover *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\z0:real^3. ball(z0,r z0 / &2)) S`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y:real^3) IN S`) o SPEC `y:real^3`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[EXISTS_FINITE_SUBSET_IMAGE] o
             ONCE_REWRITE_RULE[TAUT `a /\ b /\ c <=> b /\ a /\ c`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\z0:real^3. r z0 / &2`; `T0:real^3->bool`] P2CE_FINITE_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `IMAGE (M:real^3->num) T0` num_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `NM:num`) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN S ==> ?z0. z0 IN T0 /\ ball(z,lam) SUBSET ball(z0,r z0) /\ z0 IN S`
  (LABEL_TAC "cov") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(S:real^3->bool) SUBSET UNIONS (IMAGE (\z0:real^3. ball(z0,r z0 / &2)) T0)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z0:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(z:real^3) IN ball(z0,r z0 / &2)` THEN REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `lam <= (r:real^3->real) z0 / &2` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `lam:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`z0:real^3`; `z:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `NM:num`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "cov" (MP_TAC o C MP (ASSUME `(z:real^3) IN S`) o SPEC `z:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(z0:real^3) IN S`) o SPEC `z0:real^3`) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `NM:num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^3,r z0)` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `&2`)) (concl th))) THEN ASM SET_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `det:real^3^3->real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]]];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!z0:real^3. z0 IN T0
                  ==> ?Ne. !n w. Ne <= n /\ w IN ball(z0,r z0)
                                 ==> norm(p2ce_L (top:num->A topology) atlas
                                            (h:num->A->real^3^3) yc rho (sq n) c
                                            ((Fs:num->real^3->A) n
                                             ((kp:num->real^3->real^3) c w)) - w) < e`
    MP_TAC THENL
     [X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o SPEC `z0:real^3`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `Nee:real->num` MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
      DISCH_TAC THEN EXISTS_TAC `(Nee:real->num) e` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `Nf:real^3->num` (LABEL_TAC "nf")) THEN
    MP_TAC(ISPEC `IMAGE (Nf:real^3->num) T0` num_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `Ne:num`) THEN EXISTS_TAC `Ne:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    USE_THEN "cov" (MP_TAC o C MP (ASSUME `(z:real^3) IN S`) o SPEC `z:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "nf" (MP_TAC o C MP (ASSUME `(z0:real^3) IN T0`) o SPEC `z0:real^3`) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Ne:num` THEN ASM_SIMP_TAC[]; ASM SET_TAC[]]]);;

(* Small D-distance from a point of a chart gives a nearby point of the same chart. *)

let P2CE_DV_SMALL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp a z b w e.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     norm z < rho(NUMFST a) / &7 /\ w IN p2cg_dm rho b /\
     p2cg_dv D a z b w < e /\ e <= rho(NUMFST a) / &20
     ==> w IN p2cg_om rho D b a /\ p2cg_tr rho D b a w IN p2cg_dm rho a /\
         kp b w = kp a (p2cg_tr rho D b a w) /\
         norm(p2cg_tr rho D b a w - z) < sqrt(&2) * e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(a:num)`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(b:num)`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN cball(vec 0,rho(NUMFST(a:num)) / &2) /\
                (w:real^3) IN cball(vec 0,rho(NUMFST(b:num)) / &2) /\
                (vec 0:real^3) IN cball(vec 0,rho(NUMFST(a:num)) / &2) /\
                norm(w:real^3) < rho(NUMFST b) / &4`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN p2cg_dm rho b` THEN
    REWRITE_TAC[p2cg_dm; IN_BALL_0; IN_CBALL_0; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN p2cg_om rho D b a` ASSUME_TAC THENL
   [REWRITE_TAC[P2CG_IN_OM; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `b:num`; `w:real^3`; `a:num`; `z:real^3`; `a:num`; `vec 0:real^3`])
                  P2CG_DV_TRI) THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_SYM) THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`]) P2CG_DV_REFL0) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `a:num`; `w:real^3`]) P2CG_TR_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ABBREV_TAC `z' = p2cg_tr rho D b a w` THEN
  SUBGOAL_THEN `(z':real^3) IN p2cg_dm rho a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2cg_dm]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)
                           (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[p2cl_glue] THEN
    DISCH_THEN(MP_TAC o SPECL [`b:num`; `a:num`; `w:real^3`; `z':real^3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^3) IN cball(vec 0,rho(NUMFST(a:num)) / &2) /\
                norm(z':real^3) < rho(NUMFST a) / &4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z':real^3) IN ball(vec 0,rho(NUMFST(a:num)) / &4)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST(a:num)) / &4` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `z:real^3`; `z':real^3`]) P2CG_DV_LOWER) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `z:real^3`; `b:num`; `w:real^3`; `a:num`; `z':real^3`])
                P2CG_DV_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`z:real^3`; `z':real^3`] NORM_SUB) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sqrt(&2) * p2cg_dv D a z a (z':real^3)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The pointwise injectivity argument for one pair of charts. *)

let P2CE_INJ_POINT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fm:real^3->A) k a b z w lam eps.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     p2cg_nv N0 Nn a <= k /\ p2cg_nv N0 Nn b <= k /\
     &0 < lam /\ &0 < eps /\ eps <= lam / &2 /\ eps <= rho(NUMFST a) / &20 /\
     norm z < rho(NUMFST a) / &7 /\ w IN p2cg_dm rho b /\
     (!v. v IN ball(z,lam)
          ==> Fm (kp a v) IN IMAGE (p2cg_nch top atlas h yc k a) (ball(vec 0,rho(NUMFST a)))) /\
     (!v v'. v IN ball(z,lam) /\ v' IN ball(z,lam)
             ==> norm(v - v') <=
                 &2 * norm(p2ce_L top atlas h yc rho k a (Fm (kp a v)) -
                           p2ce_L top atlas h yc rho k a (Fm (kp a v')))) /\
     norm(p2ce_L top atlas h yc rho k a (Fm (kp a z)) - z) < eps / &8 /\
     Fm (kp b w) IN IMAGE (p2cg_nch top atlas h yc k b) (ball(vec 0,rho(NUMFST b))) /\
     norm(p2ce_L top atlas h yc rho k b (Fm (kp b w)) - w) < eps / &8 /\
     abs(p2cg_dk top atlas h yc k a z b w - p2cg_dv D a z b w) < eps / &4 /\
     Fm (kp a z) = Fm (kp b w)
     ==> kp a z = kp b w`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "land") (CONJUNCTS_THEN2 (LABEL_TAC "lip") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(a:num)`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(b:num)`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2CE_L_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "la1") (LABEL_TAC "la2")) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2CE_L_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lb1") (LABEL_TAC "lb2")) THEN
  SUBGOAL_THEN `(z:real^3) IN ball(z,lam)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ce_L top atlas (h:num->A->real^3^3) yc rho k a ((Fm:real^3->A) ((kp:num->real^3->real^3) a z))
      IN ball(vec 0,rho(NUMFST(a:num))) /\
    p2cg_nch top atlas h yc k a (p2ce_L top atlas h yc rho k a (Fm (kp a z))) = Fm (kp a z)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "la2" MATCH_MP_TAC THEN USE_THEN "land" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ce_L top atlas (h:num->A->real^3^3) yc rho k b ((Fm:real^3->A) ((kp:num->real^3->real^3) b w))
      IN ball(vec 0,rho(NUMFST(b:num))) /\
    p2cg_nch top atlas h yc k b (p2ce_L top atlas h yc rho k b (Fm (kp b w))) = Fm (kp b w)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "lb2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u = p2ce_L top atlas (h:num->A->real^3^3) yc rho k a
                    ((Fm:real^3->A) ((kp:num->real^3->real^3) a z))` THEN
  ABBREV_TAC `u' = p2ce_L top atlas (h:num->A->real^3^3) yc rho k b
                     ((Fm:real^3->A) ((kp:num->real^3->real^3) b w))` THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST(a:num)) /\ norm(u:real^3) < rho(NUMFST a) /\
                norm(w:real^3) < rho(NUMFST(b:num)) /\ norm(u':real^3) < rho(NUMFST b)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN p2cg_dm rho b` THEN
    UNDISCH_TAC `(u:real^3) IN ball(vec 0,rho(NUMFST(a:num)))` THEN
    UNDISCH_TAC `(u':real^3) IN ball(vec 0,rho(NUMFST(b:num)))` THEN
    REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the images coincide, so the chart distance of u and u' is 0 *)
  SUBGOAL_THEN `p2cg_dk top atlas (h:num->A->real^3^3) yc k a u b u' = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_dk] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2CE_SEQ_MFD) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2CE_NCH_PARAM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` (MP_TAC o MATCH_MP OPEN_IN_SUBSET o
                                                 CONJUNCT1 o CONJUNCT2)) THEN
    UNDISCH_TAC `(Fm:real^3->A) ((kp:num->real^3->real^3) b w) IN
                 IMAGE (p2cg_nch top atlas (h:num->A->real^3^3) yc k b)
                       (ball(vec 0,rho(NUMFST(b:num))))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* hence dk at (z,w) is small, and so is dv *)
  SUBGOAL_THEN `p2cg_dv D a z b w < eps` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`k:num`; `a:num`; `z:real^3`; `a:num`; `u:real^3`;
                               `b:num`; `w:real^3`]) P2CG_DK_TRI) THEN
    MP_TAC(ISPECL (p2cg_std @ [`k:num`; `a:num`; `u:real^3`; `b:num`; `u':real^3`;
                               `b:num`; `w:real^3`]) P2CG_DK_TRI) THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `z:real^3`; `u:real^3`]) P2CG_NCH_LIP) THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`; `u':real^3`; `w:real^3`]) P2CG_NCH_LIP) THEN
    ASM_REWRITE_TAC[GSYM p2cg_dk] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `sqrt(&2) * norm(z - u:real^3) <= &3 / &2 * norm(z - u) /\
                  sqrt(&2) * norm(u' - w:real^3) <= &3 / &2 * norm(u' - w)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC P2CG_SQRT2_LT THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`z:real^3`; `u:real^3`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2ce_std @ [`a:num`; `z:real^3`; `b:num`; `w:real^3`; `eps:real`])
                P2CE_DV_SMALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z' = p2cg_tr rho D b a w` THEN
  SUBGOAL_THEN `(z':real^3) IN ball(z,lam)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    SUBGOAL_THEN `sqrt(&2) * eps <= &3 / &2 * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN MP_TAC P2CG_SQRT2_LT THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^3) = z'` (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `p2ce_L top atlas (h:num->A->real^3^3) yc rho k a ((Fm:real^3->A) ((kp:num->real^3->real^3) a z')) = u`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(Fm:real^3->A) ((kp:num->real^3->real^3) a z') =
                  p2cg_nch top atlas (h:num->A->real^3^3) yc k a u` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(kp:num->real^3->real^3) b w = kp a z'` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      USE_THEN "la1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "lip" (MP_TAC o SPECL [`z:real^3`; `z':real^3`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_MUL_RZERO; NORM_LE_0; VECTOR_SUB_EQ]);;

let P2CE_NUM_BOUND = prove
 (`!(f:num->num) m. ?N. !i. i < m ==> f i <= N`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `IMAGE (f:num->num) {i | i < m}` num_FINITE) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM]);;

let P2CE_IN_OM_LEVEL = prove
 (`!rho (kp:num->real^3->real^3) P j i z.
     i < P(j + 2) /\ norm z < rho(j + 2) / &7
     ==> kp (NUMPAIR (j + 2) i) z IN p2ce_om rho kp (p2ce_cs P j) (P(j + 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ce_om; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                    (ball(vec 0,rho(j + 2) / &7))` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `P(j + 2) - 1 - i` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p2ce_cs P j (P(j + 2) - 1 - i) = NUMPAIR (j + 2) i` SUBST1_TAC THENL
     [REWRITE_TAC[p2ce_cs] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[NUMPAIR_DEST]];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0]]);;

let P2CE_LEVEL_CHART_DATA = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ i < P(j + 2)
     ==> ?lam M Ne.
           &0 < lam /\
           (!n:num z.
              M <= n /\ z IN cball(vec 0,&2 * rho(j + 2) / &15)
              ==> (!w. w IN ball(z,lam)
                       ==> p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                             (kp (NUMPAIR (j + 2) i) w) IN
                           IMAGE (p2cg_nch top atlas h yc (sq n) (NUMPAIR (j + 2) i))
                                 (ball(vec 0,rho(j + 2)))) /\
                  (!w w'. w IN ball(z,lam) /\ w' IN ball(z,lam)
                          ==> norm(w - w') <=
                              &2 * norm(p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                          (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                             (P(j + 2)) (kp (NUMPAIR (j + 2) i) w)) -
                                        p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                          (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                             (P(j + 2)) (kp (NUMPAIR (j + 2) i) w')))) /\
                  smooth_map_on (ball(z,lam))
                    (\w. p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                           (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                              (kp (NUMPAIR (j + 2) i) w))) /\
                  (!w. w IN ball(z,lam)
                       ==> ~(det(matrix(frechet_derivative
                                (\w. p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                       (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                          (P(j + 2)) (kp (NUMPAIR (j + 2) i) w)))
                                (at w))) = &0))) /\
           (!e n:num z w.
                       &0 < e /\ Ne e <= n /\ z IN cball(vec 0,&2 * rho(j + 2) / &15) /\
                       w IN ball(z,lam)
                       ==> norm(p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                  (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                                     (kp (NUMPAIR (j + 2) i) w)) - w) < e)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                                     (P(j + 2))`;
                             `NUMPAIR (j + 2) i`;
                             `cball(vec 0:real^3,&2 * rho(j + 2) / &15)`]) P2CE_GOOD_UNIFORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs P j`]) P2CE_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[p2cg_dm; IN_BALL_0; IN_CBALL_0; NUMPAIR_DEST] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CE_IN_OM_LEVEL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `M:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "st")
      (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ne:real->num` (LABEL_TAC "cl")) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `M:num`; `Ne:real->num`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "st" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "cl" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]);;

let P2CE_INJ_LEVEL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> ?N. !n i i' z w.
               N <= n /\ i < P(j + 2) /\ i' < P(j + 2) /\
               z IN cball(vec 0,&2 * rho(j + 2) / &15) /\
               w IN cball(vec 0,&2 * rho(j + 2) / &15) /\
               p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                      (kp (NUMPAIR (j + 2) i) z) =
               p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                      (kp (NUMPAIR (j + 2) i') w)
               ==> kp (NUMPAIR (j + 2) i) z = kp (NUMPAIR (j + 2) i') w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_LEVEL_CHART_DATA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `lamf:num->real` (X_CHOOSE_THEN `Mf:num->num`
    (X_CHOOSE_THEN `Nef:num->real->num` (LABEL_TAC "un")))) THEN
  MP_TAC(ISPECL [`lamf:num->real`; `{i:num | i < P(j + 2)}`] P2CE_FINITE_MIN) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ANTS_TAC THENL [USE_THEN "un" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `eps = min (d / &2) (rho(j + 2) / &20)` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= d / &2 /\ eps <= rho(j + 2) / &20` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* uniform convergence of the chart distances, for each pair of charts *)
  SUBGOAL_THEN
   `!i i'. ?Nd. !n:num z w.
              Nd <= n /\ z IN cball(vec 0,rho(NUMFST(NUMPAIR (j + 2) i)) / &2) /\
              w IN cball(vec 0,rho(NUMFST(NUMPAIR (j + 2) i')) / &2)
              ==> abs(p2cg_dk top atlas (h:num->A->real^3^3) yc (sq n)
                        (NUMPAIR (j + 2) i) z (NUMPAIR (j + 2) i') w -
                      p2cg_dv D (NUMPAIR (j + 2) i) z (NUMPAIR (j + 2) i') w) < eps / &4`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2CG_D_UNIF THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nd:num->num->num` (LABEL_TAC "du")) THEN
  MP_TAC(ISPECL [`Mf:num->num`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:num`) THEN
  MP_TAC(ISPECL [`\i. (Nef:num->real->num) i (eps / &8)`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B2:num`) THEN
  SUBGOAL_THEN `?B3. !i i'. i < P(j + 2) /\ i' < P(j + 2) ==> (Nd:num->num->num) i i' <= B3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!i. ?Bi. !i'. i' < P(j + 2) ==> (Nd:num->num->num) i i' <= Bi` MP_TAC THENL
     [GEN_TAC THEN MATCH_ACCEPT_TAC(ISPECL [`(Nd:num->num->num) i`; `P(j + 2):num`]
                                          P2CE_NUM_BOUND);
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Bf:num->num`) THEN
    MP_TAC(ISPECL [`Bf:num->num`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
    DISCH_THEN(X_CHOOSE_TAC `B3:num`) THEN EXISTS_TAC `B3:num` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(Bf:num->num) i` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `B1 + B2 + B3 + p2cg_nv N0 Nn (NUMPAIR (j + 2) 0)` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `i:num`; `i':num`; `z:real^3`; `w:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!l. p2cg_nv N0 Nn (NUMPAIR (j + 2) l) <= (sq:num->num) n` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `B1 + B2 + B3 + p2cg_nv N0 Nn (NUMPAIR (j + 2) 0) <= n` THEN
    REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Mf:num->num) i <= n /\ Mf i' <= n /\
                (Nef:num->real->num) i (eps / &8) <= n /\ Nef i' (eps / &8) <= n /\
                (Nd:num->num->num) i i' <= n` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THENL
     [EXISTS_TAC `B1:num`; EXISTS_TAC `B1:num`; EXISTS_TAC `B2:num`; EXISTS_TAC `B2:num`;
      EXISTS_TAC `B3:num`] THEN
    ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "un" (MP_TAC o C MP (ASSUME `(i:num) < P(j + 2)`) o SPEC `i:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o SPECL [`n:num`; `z:real^3`]) (LABEL_TAC "ci"))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lz") (CONJUNCTS_THEN2 (LABEL_TAC "lip") (K ALL_TAC))) THEN
  USE_THEN "un" (MP_TAC o C MP (ASSUME `(i':num) < P(j + 2)`) o SPEC `i':num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o SPECL [`n:num`; `w:real^3`]) (LABEL_TAC "ci'"))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lw") (K ALL_TAC)) THEN
  MATCH_MP_TAC(ISPECL (p2ce_std @ [`p2ce_F top atlas (h:num->A->real^3^3) yc rho
                                      (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                                      (P(j + 2))`;
                                   `(sq:num->num) n`;
                                   `NUMPAIR (j + 2) i`; `NUMPAIR (j + 2) i'`; `z:real^3`;
                                   `w:real^3`; `d:real`; `eps:real`]) P2CE_INJ_POINT) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
  SUBGOAL_THEN `(d:real) <= lamf (i:num) /\ d <= lamf (i':num) /\
                &0 < lamf i /\ &0 < lamf i'` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(z:real^3,d) SUBSET ball(z,lamf (i:num)) /\
                (z:real^3) IN ball(z,lamf i) /\ (w:real^3) IN ball(w,lamf (i':num))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[p2cg_dm; IN_CBALL_0; IN_BALL_0; NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN USE_THEN "lz" MATCH_MP_TAC THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`v:real^3`; `v':real^3`] THEN STRIP_TAC THEN
    USE_THEN "lip" MATCH_MP_TAC THEN ASM SET_TAC[];
    USE_THEN "ci" (MP_TAC o SPECL [`eps / &8`; `n:num`; `z:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    USE_THEN "lw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "ci'" (MP_TAC o SPECL [`eps / &8`; `n:num`; `w:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    USE_THEN "du" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
    UNDISCH_TAC `(z:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The final maps are diffeomorphisms.  On each piece                       *)
(* kp (j + 2,i) (ball(0,2 rho/15)) the final map is nch o R o (kp)^-1 with R *)
(* a diffeomorphism (injective, smooth, invertible derivative), hence a      *)
(* manifold diffeomorphism onto its image; the pieces cover the closure of   *)
(* W j and the map is injective on their union, so the pieces glue          *)
(* (MFD_DIFFEO_GLUE_OPEN) and restrict to W j.                               *)
(* ------------------------------------------------------------------------- *)

let P2CE_KP_PARAM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp c s.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     open s /\ s SUBSET p2cg_dm rho c
     ==> mfd_param (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp) s (kp c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2CC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `p2cg_dm rho c` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `chart_inv (p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `p2cg_dm rho c =
                  IMAGE (SND(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c))
                        (FST(p2cl_chart (p2cg_dm rho) kp c))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> f x = x) ==> s = IMAGE f s`) THEN
      ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `FST(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c)`;
                   `SND(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c)`]
                  MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2CL_CHART_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[]]);;

(* One piece: the final map composed with the chart is a parametrization. *)

let P2CE_PIECE_PARAM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ i < P(j + 2)
     ==> ?N. !n. N <= n
                 ==> mfd_param (top(sq n)) (atlas(sq n)) (ball(vec 0,&2 * rho(j + 2) / &15))
                       (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)) o
                        kp (NUMPAIR (j + 2) i))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_KP_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`; `i:num`]) P2CE_LEVEL_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `Ne:real->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "st") (K ALL_TAC)))))) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_INJ_LEVEL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `NI:num` (LABEL_TAC "inj")) THEN
  EXISTS_TAC `M + NI + p2cg_nv N0 Nn (NUMPAIR (j + 2) i)` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w w'. w IN ball(vec 0:real^3,&2 * rho(j + 2) / &15) /\
           w' IN ball(vec 0:real^3,&2 * rho(j + 2) / &15) /\
           p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                  (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))
                  (kp (NUMPAIR (j + 2) i) w) =
           p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                  (kp (NUMPAIR (j + 2) i) w')
           ==> w = w'`
  (LABEL_TAC "inj1") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `z':real^3`)) (concl th))) THEN
    EXISTS_TAC `NUMPAIR (j + 2) i` THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN ball(vec 0,&2 * rho(j + 2) / &15)` THEN
      REWRITE_TAC[p2cg_dm; IN_BALL_0; NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(w':real^3) IN ball(vec 0,&2 * rho(j + 2) / &15)` THEN
      REWRITE_TAC[p2cg_dm; IN_BALL_0; NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "inj" MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  ABBREV_TAC `s = ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
  ABBREV_TAC `a = NUMPAIR (j + 2) i` THEN
  ABBREV_TAC `Fm = p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))` THEN
  SUBGOAL_THEN `p2cg_nv N0 Nn a <= (sq:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `NUMFST(a:num) = j + 2 /\ s SUBSET p2cg_dm rho a /\
                (!w:real^3. w IN s ==> w IN cball(vec 0,&2 * rho(j + 2) / &15)) /\
                open (s:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "s"] THEN
    REWRITE_TAC[NUMPAIR_DEST; p2cg_dm; SUBSET; IN_BALL_0; IN_CBALL_0; OPEN_BALL] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the pointwise data on s *)
  SUBGOAL_THEN
   `!w:real^3. w IN s
               ==> Fm (kp a w) IN IMAGE (p2cg_nch top atlas (h:num->A->real^3^3) yc ((sq:num->num) n) a)
                                        (ball(vec 0,rho(j + 2))) /\
                   (?t. open t /\ w IN t /\
                        smooth_map_on t (\w. p2ce_L top atlas h yc rho ((sq:num->num) n) a
                                               ((Fm:real^3->A) ((kp:num->real^3->real^3) a w)))) /\
                   ~(det(matrix(frechet_derivative
                          (\w. p2ce_L top atlas h yc rho ((sq:num->num) n) a (Fm (kp a w))) (at w))) = &0)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "st" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN ball(w,lam)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `IMAGE:(real^3->A)->(real^3->bool)->A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `ball(w:real^3,lam)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `det:real^3^3->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `R = \w. p2ce_L top atlas (h:num->A->real^3^3) yc rho ((sq:num->num) n) a
                        ((Fm:real^3->A) ((kp:num->real^3->real^3) a w))` THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `(sq:num->num) n`]) P2CE_L_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1") (LABEL_TAC "l2")) THEN
  SUBGOAL_THEN
   `!w:real^3. w IN s
               ==> (R:real^3->real^3) w IN ball(vec 0,rho(j + 2)) /\
                   p2cg_nch top atlas (h:num->A->real^3^3) yc ((sq:num->num) n) a (R w) =
                   (Fm:real^3->A) ((kp:num->real^3->real^3) a w)`
  (LABEL_TAC "rw") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN EXPAND_TAC "R" THEN REWRITE_TAC[] THEN
    USE_THEN "l2" MATCH_MP_TAC THEN
    USE_THEN "pt" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?R'. diffeomorphism_on s (IMAGE (R:real^3->real^3) s) R R'` MP_TAC THENL
   [MATCH_MP_TAC P2CE_INJ_DIFFEO THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
      SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
      USE_THEN "inj1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rw" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
      USE_THEN "rw" (MP_TAC o C MP (ASSUME `(w':real^3) IN s`) o SPEC `w':real^3`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `R':real^3->real^3`) THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `p2cg_nch top atlas (h:num->A->real^3^3) yc ((sq:num->num) n) a o (R:real^3->real^3)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2CE_SEQ_MFD) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,rho(j + 2))`; `IMAGE (R:real^3->real^3) s`;
                          `R':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2CE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL (p2cg_std @ [`a:num`; `(sq:num->num) n`]) P2CE_NCH_PARAM) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]]);;

let P2CE_PIECE_DIFFEO = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ i < P(j + 2)
     ==> ?N. !n. N <= n
                 ==> ?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                           (IMAGE (kp (NUMPAIR (j + 2) i)) (ball(vec 0,&2 * rho(j + 2) / &15)))
                           (top(sq n)) (atlas(sq n))
                           (IMAGE (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))
                              (IMAGE (kp (NUMPAIR (j + 2) i))
                                     (ball(vec 0,&2 * rho(j + 2) / &15))))
                           (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    MP_TAC(MATCH_MP P2CE_PIECE_PARAM th)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2CC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
  ABBREV_TAC `Fm = p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  MP_TAC(ISPECL (p2ce_std @ [`NUMPAIR (j + 2) i`; `s:real^3->bool`]) P2CE_KP_PARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[OPEN_BALL; p2cg_dm; SUBSET; IN_BALL_0; NUMPAIR_DEST] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `k':real^3->real^3`) THEN
  SUBGOAL_THEN `smooth_manifold_atlas ((top:num->A topology) ((sq:num->num) n))
                  ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2CE_SEQ_MFD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i)) s`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `s:real^3->bool`;
                 `(top:num->A topology) ((sq:num->num) n)`; `(atlas:num->((A->bool)#(A->real^3))->bool) ((sq:num->num) n)`;
                 `IMAGE ((Fm:real^3->A) o (kp:num->real^3->real^3) (NUMPAIR (j + 2) i)) s`;
                 `k':real^3->real^3`; `(kp:num->real^3->real^3) (NUMPAIR (j + 2) i)`;
                 `(Fm:real^3->A) o (kp:num->real^3->real^3) (NUMPAIR (j + 2) i)`;
                 `e':A->real^3`] MFD_DIFFEO_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(kp:num->real^3->real^3) (NUMPAIR (j + 2) i) o (e':A->real^3)` THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC MFD_DIFFEO_EQ THEN
  MAP_EVERY EXISTS_TAC [`((Fm:real^3->A) o (kp:num->real^3->real^3) (NUMPAIR (j + 2) i)) o
                         (k':real^3->real^3)`;
                        `(kp:num->real^3->real^3) (NUMPAIR (j + 2) i) o (e':A->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    can (find_term ((=) `k':real^3->real^3`)) (concl th) &&
    can (find_term ((=) `euclidean:(real^3)topology`)) (concl th) &&
    not (can (find_term ((=) `e':A->real^3`)) (concl th)))) THEN
  ASM_SIMP_TAC[]);;

(* The pieces cover the closure of W j. *)

let P2CE_COVER_PIECES = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp j SUBSET
         UNIONS {IMAGE (kp (NUMPAIR (j + 2) i)) (ball(vec 0,&2 * rho(j + 2) / &15)) |
                 i | i < P(j + 2)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2CC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `j:num` o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  REWRITE_TAC[SUBSET; p2cc_W; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2ce_std P2CC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(p:real^3) IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3))` THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `a:num`; `z:real^3`]) P2CC_DELTA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `a:num`; `z:real^3`; `j + 2`])
                P2CC_DELTA_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2cc_delta rho D kp (p:real^3) < &(SUC j) + &1` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_ADD; ARITH_RULE `SUC j + 1 = j + 2`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN EXISTS_TAC `w:real^3` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Gluing the pieces. *)

let P2CE_UNIONS_LT_SUC = prove
 (`!(f:num->real^3->bool) m.
     UNIONS {f i | i | i < SUC m} = UNIONS {f i | i | i < m} UNION f m /\
     UNIONS {f i | i | i < 0} = {}`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNION; IN_ELIM_THM; LT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let P2CE_DIFFEO_UNION = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> ?N. !n. N <= n
                 ==> ?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                           (UNIONS {IMAGE (kp (NUMPAIR (j + 2) i))
                                          (ball(vec 0,&2 * rho(j + 2) / &15)) |
                                    i | i < P(j + 2)})
                           (top(sq n)) (atlas(sq n))
                           (IMAGE (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))
                              (UNIONS {IMAGE (kp (NUMPAIR (j + 2) i))
                                             (ball(vec 0,&2 * rho(j + 2) / &15)) |
                                       i | i < P(j + 2)}))
                           (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2CC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_BASE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!i. ?Np. i < P(j + 2)
             ==> !n. Np <= n
                     ==> ?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                               (IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                                      (ball(vec 0,&2 * rho(j + 2) / &15)))
                               ((top:num->A topology) ((sq:num->num) n))
                               ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
                               (IMAGE (p2ce_F top atlas (h:num->A->real^3^3) yc rho kp
                                         (p2ce_cs P j) (sq n) (P(j + 2)))
                                  (IMAGE (kp (NUMPAIR (j + 2) i))
                                         (ball(vec 0,&2 * rho(j + 2) / &15))))
                               (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < P(j + 2)` THENL
     [MP_TAC(ISPECL (p2ce_std @ [`j:num`; `i:num`]) P2CE_PIECE_DIFFEO) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Np:num->num` (LABEL_TAC "pc")) THEN
  MP_TAC(ISPECL [`Np:num->num`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `BP:num`) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_INJ_LEVEL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `NI:num` (LABEL_TAC "inj")) THEN
  EXISTS_TAC `BP + NI:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ABBREV_TAC `pc = \i. IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                             (ball(vec 0,&2 * rho(j + 2) / &15))` THEN
  ABBREV_TAC `U = UNIONS {(pc:num->real^3->bool) i | i | i < P(j + 2)}` THEN
  ABBREV_TAC `Fm = p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))` THEN
  SUBGOAL_THEN `!i. IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                          (ball(vec 0,&2 * rho(j + 2) / &15)) = pc i`
  (LABEL_TAC "pcd") THENL
   [EXPAND_TAC "pc" THEN REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "pcd" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  (* injectivity on U *)
  SUBGOAL_THEN `!p q. p IN U /\ q IN U /\ (Fm:real^3->A) p = Fm q ==> p = q`
  (LABEL_TAC "uinj") THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i':num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(p:real^3) IN pc (i:num)` THEN UNDISCH_TAC `(q:real^3) IN pc (i':num)` THEN
    USE_THEN "pcd" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "inj" MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      UNDISCH_TAC `(Fm:real^3->A) p = Fm q` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fm" THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\q:A. @p:real^3. p IN U /\ (Fm:real^3->A) p = q` THEN
  (* each piece with the global inverse *)
  SUBGOAL_THEN
   `!i:num. i < P(j + 2)
        ==> mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
              ((pc:num->real^3->bool) i)
              ((top:num->A topology) ((sq:num->num) n))
              ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
              (IMAGE (Fm:real^3->A) (pc i)) Fm (\q:A. @p:real^3. p IN U /\ Fm p = q)`
  (LABEL_TAC "pg") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "pc" (MP_TAC o C MP (ASSUME `(i:num) < P(j + 2)`) o SPEC `i:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `BP:num` THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `G0:A->real^3`) THEN
    MATCH_MP_TAC MFD_DIFFEO_EQ THEN MAP_EVERY EXISTS_TAC [`Fm:real^3->A`; `G0:A->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2CE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(p:real^3) IN U` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN X_GEN_TAC `p':real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN USE_THEN "uinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* induction over the number of pieces *)
  SUBGOAL_THEN
   `!m. 1 <= m /\ m <= P(j + 2)
        ==> mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
              (UNIONS {(pc:num->real^3->bool) i | i | i < m})
              ((top:num->A topology) ((sq:num->num) n))
              ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
              (IMAGE (Fm:real^3->A) (UNIONS {pc i | i | i < m})) Fm
              (\q:A. @p:real^3. p IN U /\ Fm p = q)`
  MP_TAC THENL
   [INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[P2CE_UNIONS_LT_SUC; UNION_EMPTY] THEN
      USE_THEN "pg" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[P2CE_UNIONS_LT_SUC; IMAGE_UNION] THEN
    MATCH_MP_TAC MFD_DIFFEO_GLUE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`Fm:real^3->A`; `\q:A. @p:real^3. p IN U /\ (Fm:real^3->A) p = q`;
                          `Fm:real^3->A`; `\q:A. @p:real^3. p IN U /\ (Fm:real^3->A) p = q`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2CE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "pg" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `P(j + 2):num`) THEN ASM_REWRITE_TAC[LE_REFL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "U" THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The headline.  For every level j there is one sequence of                *)
(* maps Fm n (the final patched maps of level j) such that for all large n   *)
(* Fm n is a diffeomorphism of W j onto an open subset of the manifold sq n  *)
(* sending xl to x (sq n), and for every m and eta > 0, for all large n its  *)
(* pulled-back metric is eta-close in lck_dist2 m to the limit metric on the *)
(* closure of W j (P2CE_EMBED).                                              *)
(* ------------------------------------------------------------------------- *)

let P2CE_EMBED_LEVEL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j m eta.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ &0 < eta
     ==> ?N. !n. N <= n
                 ==> (?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                            (p2cc_W rho D kp j) (top(sq n)) (atlas(sq n))
                            (IMAGE (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))
                                   (p2cc_W rho D kp j))
                            (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G) /\
                     p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)) (p2cc_xl kp) =
                     x(sq n) /\
                     (!y. y IN p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp j
                          ==> lck_dist2 m
                                (metric_local (p2cl_atlas (p2cg_dm rho) kp)
                                   (chart_at (p2cl_atlas (p2cg_dm rho) kp) y)
                                   (p2cl_metric (p2cg_dm rho) kp Gl))
                                (\w. rfs_pullback (atlas (sq n))
                                       (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                               (P(j + 2)) o
                                        chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp) y))
                                       (h (sq n)) w)
                                (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) y) y) < eta)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2CC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2ce_std P2CC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_DIFFEO_UNION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "du")) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_BASE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "bs") o CONJUNCT2) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`; `m:num`; `eta:real`]) P2CE_LCK_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "lk")) THEN
  EXISTS_TAC `N1 + N2 + N3:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "du" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `G:A->real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    EXISTS_TAC `UNIONS {IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                              (ball(vec 0,&2 * rho(j + 2) / &15)) | i | i < P(j + 2)}` THEN
    EXISTS_TAC `IMAGE (p2ce_F (top:num->A topology) atlas h yc rho (kp:num->real^3->real^3)
                         (p2ce_cs P j) ((sq:num->num) n) (P(j + 2)))
                      (UNIONS {IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                                     (ball(vec 0,&2 * rho(j + 2) / &15)) | i | i < P(j + 2)})` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3) closure_of p2cc_W rho D kp j` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2CE_COVER_PIECES) THEN ASM_REWRITE_TAC[]];
    USE_THEN "bs" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "lk" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let P2CE_EMBED = prove
 (`!top atlas (h:num->A->real^3^3) x.
     P2C_REQ_CGT_STATEMENT (:A) /\ p2cu_seq top atlas h x
     ==> ?(M:(real^3)topology) atlasM g xl (W:num->real^3->bool) (sq:num->num).
           hausdorff_space M /\ smooth_manifold_atlas M atlasM /\
           riemannian_metric atlasM g /\ mfd_complete (M,atlasM) g /\ xl IN topspace M /\
           (!k. open_in M (W k) /\ xl IN W k /\ compact_in M (M closure_of W k) /\
                M closure_of W k SUBSET W (SUC k)) /\
           UNIONS {W k | k IN (:num)} = topspace M /\
           (!m n. m < n ==> sq m < sq n) /\
           (!j. ?Fm:num->real^3->A.
                  (?N. !n. N <= n
                           ==> (?G. mfd_diffeo M atlasM (W j) (top(sq n)) (atlas(sq n))
                                      (IMAGE (Fm n) (W j)) (Fm n) G) /\
                               Fm n xl = x(sq n)) /\
                  (!m eta.
                     &0 < eta
                     ==> ?N. !n y. N <= n /\ y IN M closure_of W j
                                   ==> lck_dist2 m
                                         (metric_local atlasM (chart_at atlasM y) g)
                                         (\z. rfs_pullback (atlas(sq n))
                                                (Fm n o chart_inv (chart_at atlasM y))
                                                (h(sq n)) z)
                                         (SND(chart_at atlasM y) y) < eta))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2CC_COMPLETE_LIMIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->real` (X_CHOOSE_THEN `K:num->real`
    (X_CHOOSE_THEN `N0:num->num` (X_CHOOSE_THEN `B:num->num->real`
    (X_CHOOSE_THEN `NB:num->num->num` (X_CHOOSE_THEN `P:num->num`
    (X_CHOOSE_THEN `Nn:num->num` (X_CHOOSE_THEN `yc:num->num->num->A`
    (X_CHOOSE_THEN `sq:num->num` (X_CHOOSE_THEN `D:num#num->real^(3,3)finite_sum->real^1`
    (X_CHOOSE_THEN `Gl:num->real^3->real^3^3` (X_CHOOSE_THEN `kp:num->real^3->real^3`
      STRIP_ASSUME_TAC)))))))))))) THEN
  SUBGOAL_THEN `p2ce_ctx top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[p2ce_ctx]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CE_CTX_FACTS) THEN
  MAP_EVERY EXISTS_TAC
   [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
    `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
    `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`; `p2cc_xl kp`;
    `p2cc_W rho D kp`; `sq:num->num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2cg_dsys top atlas (h:num->A->real^3^3) yc rho sq D` THEN
    SIMP_TAC[p2cg_dsys];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN
  EXISTS_TAC `\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                         (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                         (P(j + 2))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL (p2ce_std @ [`j:num`; `0`; `&1`]) P2CE_EMBED_LEVEL) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
    SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`m:num`; `eta:real`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2ce_std @ [`j:num`; `m:num`; `eta:real`]) P2CE_EMBED_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]]);;

