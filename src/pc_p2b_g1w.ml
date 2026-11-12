(* ========================================================================= *)
(* Unit pc_p2b_g1w (Part 2B): invariance of the weak forms                   *)
(* p2bw_t1, p2bw_t2, p2bw_tid of the W3 vocabulary under the space-time     *)
(* maps Phi(x,t) = (H x, lam t) (H a diffeomorphism of open sets, lam > 0), *)
(* with the transformed coefficients G = (1/lam) DH' (G0 o Phi) DH,          *)
(* R = lam (R0 o Phi), l = l0 o Phi.  Used by G1 of MT Prop 9.20 to move    *)
(* W3 from charts of the kappa-solution to charts of the limit along the    *)
(* embeddings phi k and the parabolic rescaling by tau k.                   *)
(*                                                                           *)
(* First the block determinant and the maps Phi.                             *)
(* ========================================================================= *)

needs "src/pc_p2b_w920.ml";;
needs "src/pc_p2a_wkdec.ml";;

prioritize_real();;
type_invention_error := true;;

(* abs det of a block-diagonal linear map of real^(N,1), by measures. *)

let P2BX_DET_BLOCK = prove
 (`!(A:real^N^N) c.
     abs(det(matrix(\v:real^(N,1)finite_sum. pastecart (A ** fstcart v) (c % sndcart v)))) =
     abs(det A) * abs c`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `L = \v:real^(N,1)finite_sum. pastecart ((A:real^N^N) ** fstcart v) (c % sndcart v)` THEN
  SUBGOAL_THEN `linear (L:real^(N,1)finite_sum->real^(N,1)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_PASTECART THEN CONJ_TAC THEN
    REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD; SNDCART_CMUL;
                MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s1 = interval[vec 0:real^N,vec 1]` THEN
  ABBREV_TAC `t1 = interval[vec 0:real^1,vec 1]` THEN
  SUBGOAL_THEN `measurable(s1:real^N->bool) /\ measure s1 = &1 /\
                measurable(t1:real^1->bool) /\ measure t1 = &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s1"; "t1"] THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; MEASURE_INTERVAL; CONTENT_UNIT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (L:real^(N,1)finite_sum->real^(N,1)finite_sum) (s1 PCROSS t1) =
    (IMAGE (\x. (A:real^N^N) ** x) s1) PCROSS (IMAGE (\y:real^1. c % y) t1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; FORALL_PASTECART;
                PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(\x. (A:real^N^N) ** x) /\ linear(\y:real^1. c % y)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix(\y:real^1. c % y) = c %% mat 1` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV) [GSYM MATRIX_OF_MATRIX_VECTOR_MUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^(N,1)finite_sum->real^(N,1)finite_sum`;
                 `(s1:real^N->bool) PCROSS (t1:real^1->bool)`] MEASURE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[MEASURABLE_PCROSS] THEN
  ASM_SIMP_TAC[MEASURE_PCROSS] THEN
  ASM_SIMP_TAC[MEASURE_PCROSS; MEASURABLE_LINEAR_IMAGE; MEASURE_LINEAR_IMAGE] THEN
  ASM_REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; DET_CMUL; DET_I; DIMINDEX_1] THEN
  REAL_ARITH_TAC);;

(* The space-time maps Phi(x,t) = (H x, lam t): diffeomorphisms of the     *)
(* cylinders over U and V, with the block derivative.                         *)

let P2BX_PHI_DIFFEO = prove
 (`!(U:real^N->bool) V H H' lam.
     diffeomorphism_on U V H H' /\ &0 < lam
     ==> diffeomorphism_on {z:real^(N,1)finite_sum | fstcart z IN U}
                           {w:real^(N,1)finite_sum | fstcart w IN V}
           (\z. pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))
           (\w. pastecart (H'(fstcart w)) (lift(drop(sndcart w) / lam))) /\
         !z. fstcart z IN U
             ==> ((\z. pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) has_derivative
                  (\v. pastecart (frechet_derivative H (at (fstcart z)) (fstcart v))
                                 (lam % sndcart v))) (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. open s ==> open {z:real^(N,1)finite_sum | fstcart z IN s}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{z:real^(N,1)finite_sum | fstcart z IN s} = s PCROSS (:real^1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                  FSTCART_PASTECART; IN_UNIV];
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. lift(lam * drop x) = lam % x` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. lift(drop x / lam) = inv lam % x` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. fstcart z IN U
        ==> ((\z:real^(N,1)finite_sum. pastecart ((H:real^N->real^N)(fstcart z)) (lam % sndcart z))
             has_derivative
             (\v. pastecart (frechet_derivative H (at (fstcart z)) (fstcart v))
                            (lam % sndcart v))) (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^(N,1)finite_sum. (H:real^N->real^N)(fstcart z)) = H o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      SUBGOAL_THEN `(\v:real^(N,1)finite_sum. frechet_derivative (H:real^N->real^N)
                       (at (fstcart(z:real^(N,1)finite_sum))) (fstcart v)) =
                    frechet_derivative H (at (fstcart z)) o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_FSTCART];
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL] THEN
      REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART; FORALL_PASTECART;
                FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `s:real^1`] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (H:real^N->real^N) U = V`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`(H':real^N->real^N) y`; `inv lam % (s:real^1)`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (H':real^N->real^N) V = U`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART; FORALL_PASTECART;
                FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real^1`] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (H':real^N->real^N) V = U`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`(H:real^N->real^N) x`; `lam % (s:real^1)`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (H:real^N->real^N) U = V`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_PASTECART; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                PASTECART_INJ] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    REWRITE_TAC[FORALL_PASTECART; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                PASTECART_INJ] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^(N,1)finite_sum. (H:real^N->real^N)(fstcart z)) =
                    H o fstcart o (\z. z)` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN; SMOOTH_MAP_ON_ID] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM];
      SUBGOAL_THEN `(\z:real^(N,1)finite_sum. lam % sndcart z) =
                    (\v:real^(N,1)finite_sum. lam % sndcart v) o (\z. z)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_ID] THEN
      REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL] THEN REPEAT STRIP_TAC THEN
      VECTOR_ARITH_TAC];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\w:real^(N,1)finite_sum. (H':real^N->real^N)(fstcart w)) =
                    H' o fstcart o (\z. z)` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN; SMOOTH_MAP_ON_ID] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM];
      SUBGOAL_THEN `(\w:real^(N,1)finite_sum. inv lam % sndcart w) =
                    (\v:real^(N,1)finite_sum. inv lam % sndcart v) o (\z. z)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_ID] THEN
      REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL] THEN REPEAT STRIP_TAC THEN
      VECTOR_ARITH_TAC]]);;

(* ========================================================================= *)
(* Test functions move along diffeomorphisms; the chain rule for wan_tder,   *)
(* wan_xder through Phi; the bilinear form as a dot product; the matrix      *)
(* algebra of the transformed coefficients.                                  *)
(* ========================================================================= *)

(* Images of open sets under diffeomorphisms of open sets are open. *)

let P2BX_DIFFEO_IMAGE_OPEN = prove
 (`!(S:real^M->bool) S' (P:real^M->real^M) P' N0.
     diffeomorphism_on S S' P P' /\ open N0 /\ N0 SUBSET S
     ==> open(IMAGE P N0) /\ IMAGE P N0 = {w | w IN S' /\ P' w IN N0}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^M` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^M) IN S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (P:real^M->real^M) S = S'`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(P':real^M->real^M) w` THEN ASM_SIMP_TAC[]];
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]]);;

(* A test function on N0 moved by the diffeomorphism P. *)

let P2BX_TEST_TRANSPORT = prove
 (`!(S:real^M->bool) S' (P:real^M->real^M) P' N0 phi.
     diffeomorphism_on S S' P P' /\ open N0 /\ N0 SUBSET S /\ wan_test N0 phi
     ==> wan_test (IMAGE P N0) (\w. if w IN IMAGE P N0 then phi(P' w) else &0) /\
         (!z. z IN N0 ==> (\w. if w IN IMAGE P N0 then phi(P' w) else &0) (P z) = phi z) /\
         ((!z. &0 <= phi z) ==> !w. &0 <= (\w. if w IN IMAGE P N0 then phi(P' w) else &0) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^M->bool`; `S':real^M->bool`; `P:real^M->real^M`; `P':real^M->real^M`;
                 `N0:real^M->bool`] P2BX_DIFFEO_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `diffeomorphism_on (S:real^M->bool) (S':real^M->bool) (P:real^M->real^M)
                                 (P':real^M->real^M)` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  UNDISCH_TAC `wan_test (N0:real^M->bool) (phi:real^M->real)` THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!z:real^M. z IN N0 ==> (P':real^M->real^M) ((P:real^M->real^M) z) = z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (P:real^M->real^M) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(w IN IMAGE (P:real^M->real^M) k)
        ==> (\w. if w IN IMAGE P N0 then (phi:real^M->real) (P' w) else &0) w = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `~(w IN IMAGE (P:real^M->real^M) k)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `w:real^M` THEN
    ASM_CASES_TAC `(w:real^M) IN IMAGE (P:real^M->real^M) N0` THENL
     [EXISTS_TAC `IMAGE (P:real^M->real^M) N0` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `(\x. lift((phi:real^M->real) x)) o (P':real^M->real^M)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^M)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `S':real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^M) DIFF IMAGE (P:real^M->real^M) k` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\x:real^M. lift(&0)` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      X_GEN_TAC `v:real^M` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^M` o check (fun th ->
        can (find_term ((=) `k:real^M->bool`)) (concl th) && is_forall (concl th) &&
        can (find_term ((=) `N0:real^M->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    EXISTS_TAC `IMAGE (P:real^M->real^M) k` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^M` o check (fun th ->
      can (find_term ((=) `k:real^M->bool`)) (concl th) && is_forall (concl th) &&
      can (find_term ((=) `N0:real^M->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(P:real^M->real^M) z IN IMAGE P N0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    DISCH_TAC THEN X_GEN_TAC `w:real^M` THEN BETA_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* ========================================================================= *)
(* The chain rule through Phi for wan_tder and the spatial gradient, the     *)
(* bilinear form as a dot product, and the algebra of the transformed metric *)
(* (inverse and square root of det).                                         *)
(* ========================================================================= *)

let P2BX_PHI_CHAIN = prove
 (`!(U:real^N->bool) V H H' lam (f0:real^(N,1)finite_sum->real) f O z.
     diffeomorphism_on U V H H' /\ &0 < lam /\ open O /\ z IN O /\
     (!w. w IN O
          ==> fstcart w IN U /\
              f w = f0 (pastecart (H(fstcart w)) (lift(lam * drop(sndcart w))))) /\
     (\w. lift(f0 w)) differentiable at (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))
     ==> (\w. lift(f w)) differentiable at z /\
         wan_tder f z =
         lam * wan_tder f0 (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
         ((lambda i. wan_xder i f z):real^N) =
         transp(matrix(frechet_derivative H (at (fstcart z)))) **
         (lambda j. wan_xder j f0 (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `zz = pastecart ((H:real^N->real^N)(fstcart (z:real^(N,1)finite_sum)))
                             (lift(lam * drop(sndcart z)))` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`] P2BX_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^(N,1)finite_sum` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  ABBREV_TAC `D0 = frechet_derivative (\w. lift((f0:real^(N,1)finite_sum->real) w)) (at zz)` THEN
  ABBREV_TAC `DH = frechet_derivative (H:real^N->real^N) (at (fstcart(z:real^(N,1)finite_sum)))` THEN
  SUBGOAL_THEN `linear(D0:real^(N,1)finite_sum->real^1) /\ linear(DH:real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "D0" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "DH" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      UNDISCH_TAC `diffeomorphism_on (U:real^N->bool) (V:real^N->bool) (H:real^N->real^N)
                                     (H':real^N->real^N)` THEN
      REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift((f:real^(N,1)finite_sum->real) w)) has_derivative
     (D0 o (\v. pastecart ((DH:real^N->real^N) (fstcart v)) (lam % sndcart v)))) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(\w. lift((f0:real^(N,1)finite_sum->real) w)) o
                (\w. pastecart ((H:real^N->real^N)(fstcart w)) (lift(lam * drop(sndcart w))))` THEN
    UNDISCH_TAC `open(O:real^(N,1)finite_sum->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^(N,1)finite_sum`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(w:real^(N,1)finite_sum) IN O` (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN EXPAND_TAC "DH" THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "D0" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\w. lift((f:real^(N,1)finite_sum->real) w)) (at z) =
    D0 o (\v. pastecart ((DH:real^N->real^N) (fstcart v)) (lam % sndcart v))`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `(D0:real^(N,1)finite_sum->real^1) o
                (\v. pastecart ((DH:real^N->real^N) (fstcart v)) (lam % sndcart v))` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[wan_tder] THEN ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN `(DH:real^N->real^N)(vec 0) = vec 0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC(ISPEC `DH:real^N->real^N` LINEAR_0) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `pastecart (vec 0:real^N) (lam % lift(&1)) = lam % pastecart (vec 0) (lift(&1))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear(D0:real^(N,1)finite_sum->real^1)`)] THEN
    REWRITE_TAC[DROP_CMUL];
    ALL_TAC] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix_vector_mul; TRANSP_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[wan_xder] THEN ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPEC `\y:real^N. (D0:real^(N,1)finite_sum->real^1) (pastecart y (vec 0))`
               LINEAR_COMPONENTWISE_EXPANSION) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `(\y:real^N. (D0:real^(N,1)finite_sum->real^1) (pastecart y (vec 0))) =
                  D0 o (\y. pastecart y (vec 0))` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_RID;
                VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(DH:real^N->real^N) (basis i)`; `1`]) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; wan_xder] THEN BETA_TAC THEN
  SUBGOAL_THEN `(DH:real^N->real^N)(basis i)$j = matrix DH$j$i` SUBST1_TAC THENL
   [ASM_SIMP_TAC[matrix; LAMBDA_BETA]; ALL_TAC] THEN
  REFL_TAC);;

(* The bilinear form of W3 as a dot product of the spatial gradients. *)

let P2BX_BIL_DOT = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u v z.
     p2bw_bil A u v z =
     ((lambda i. wan_xder i u z):real^N) dot (A z ** (lambda j. wan_xder j v z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bw_bil; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; matrix_vector_mul; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

(* The transformed metric: inverse and the square root of the determinant. *)

let P2BX_METRIC_ALG = prove
 (`!(M:real^N^N) (G0:real^N^N) lam.
     invertible M /\ invertible G0 /\ &0 < lam
     ==> M ** matrix_inv(inv lam %% (transp M ** G0 ** M)) ** transp M =
         lam %% matrix_inv G0 /\
         sqrt(det(inv lam %% (transp M ** G0 ** M))) =
         sqrt(inv lam pow dimindex(:N)) * abs(det M) * sqrt(det G0)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[MATRIX_INV_CMUL; REAL_INV_INV] THEN
    SUBGOAL_THEN `invertible(transp(M:real^N^N)) /\ invertible((G0:real^N^N) ** M)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[INVERTIBLE_TRANSP; INVERTIBLE_MATRIX_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_INV_MUL; MATRIX_INV_TRANSP] THEN
    REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
    ASM_SIMP_TAC[MATRIX_INV; TRANSP_MAT; MATRIX_MUL_RID];
    REWRITE_TAC[DET_CMUL; DET_MUL; DET_TRANSP] THEN
    REWRITE_TAC[REAL_ARITH `m * g * m = m pow 2 * g`] THEN
    REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS]]);;

(* ========================================================================= *)
(* The bilinear forms of the transformed coefficients; absolute              *)
(* integrability of tests times L^infty_loc functions; the change of         *)
(* variables for the weak forms along Phi.                                   *)
(* ========================================================================= *)

let P2BX_BIL_TRANSFER = prove
 (`!(M:real^N^N) (G0:real^N^N) lam a b.
     invertible M /\ invertible G0 /\ &0 < lam
     ==> (transp M ** a) dot
         ((sqrt(det(inv lam %% (transp M ** G0 ** M))) %%
           matrix_inv(inv lam %% (transp M ** G0 ** M))) ** (transp M ** b)) =
         lam * (sqrt(inv lam pow dimindex(:N)) * abs(det M)) *
         (a dot ((sqrt(det G0) %% matrix_inv G0) ** b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`M:real^N^N`; `G0:real^N^N`; `lam:real`] P2BX_METRIC_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

(* Tests times L^infty_loc functions, and derivatives of tests times them, *)
(* are absolutely integrable.                                                *)

let P2BX_TEST_LEBM_ABSINT = prove
 (`!(om:real^M->bool) phi h.
     open om /\ wan_test om phi /\ p2bw_lebm om h
     ==> (\z. lift(phi z * h z)) absolutely_integrable_on om /\
         !v. (\z. lift(drop(frechet_derivative (\y. lift(phi y)) (at z) v) * h z))
             absolutely_integrable_on om`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`] WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  SUBGOAL_THEN `!x y. abs((phi:real^M->real) x - phi y) <= abs B * norm(x - y)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B * norm(x - y:real^M)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `h:real^M->real`; `k:real^M->bool`] P2BW_LEBM_L1BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (MP_TAC o CONJUNCT2)) THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^M->real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LIP_SUPPORT_ABSINT THEN
      MAP_EVERY EXISTS_TAC [`abs B`; `k:real^M->bool`] THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    X_GEN_TAC `v:real^M` THEN
    MP_TAC(ISPECL [`phi:real^M->real`; `abs B`; `k:real^M->bool`; `v:real^M`]
                  P2BW_LIP_DER_ABSINT) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `\x. drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) v)`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* The change of variables along Phi for a function vanishing outside the  *)
(* image of N0, against its pullback weighted by the Jacobian.              *)

let P2BX_COV_TRANSFER = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) N0 F0 Ft Z.
     diffeomorphism_on U V H H' /\ &0 < lam /\ open om0 /\ open N0 /\
     (!z. z IN N0
          ==> fstcart z IN U /\
              pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))) IN om0) /\
     (\w. lift(F0 w)) absolutely_integrable_on om0 /\
     (!w. ~(w IN IMAGE (\z. pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) N0)
          ==> F0 w = &0) /\
     negligible Z /\
     (!z. z IN N0 /\ ~(z IN Z)
          ==> Ft z = sqrt(inv lam pow dimindex(:N)) *
                     (abs(det(matrix(frechet_derivative H (at (fstcart z))))) * lam) *
                     F0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))))
     ==> (\z. lift(Ft z)) integrable_on N0 /\
         integral N0 (\z. lift(Ft z)) =
         sqrt(inv lam pow dimindex(:N)) % integral om0 (\w. lift(F0 w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`] P2BX_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = \z:real^(N,1)finite_sum. pastecart ((H:real^N->real^N)(fstcart z))
                                                     (lift(lam * drop(sndcart z)))` THEN
  ABBREV_TAC `P' = \w:real^(N,1)finite_sum. pastecart ((H':real^N->real^N)(fstcart w))
                                                      (lift(drop(sndcart w) / lam))` THEN
  SUBGOAL_THEN `(N0:real^(N,1)finite_sum->bool) SUBSET {z | fstcart z IN U}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^(N,1)finite_sum | fstcart z IN U}`;
                 `{w:real^(N,1)finite_sum | fstcart w IN V}`;
                 `P:real^(N,1)finite_sum->real^(N,1)finite_sum`;
                 `P':real^(N,1)finite_sum->real^(N,1)finite_sum`; `N0:real^(N,1)finite_sum->bool`]
                P2BX_DIFFEO_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET om0` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(N,1)finite_sum. z IN N0
        ==> ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) has_derivative
             (\v:real^(N,1)finite_sum. pastecart (frechet_derivative (H:real^N->real^N) (at (fstcart z)) (fstcart v))
                            (lam % sndcart v))) (at z within N0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN N0 /\ y IN N0 /\ (P:real^(N,1)finite_sum->real^(N,1)finite_sum) x = P y
          ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
        can (find_term ((=) `P':real^(N,1)finite_sum->real^(N,1)finite_sum`)) (concl th) &&
        is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "diffeomorphism_on")) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^(N,1)finite_sum` th) THEN
                         MP_TAC(SPEC `y:real^(N,1)finite_sum` th)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the change of variables *)
  SUBGOAL_THEN `(\w. lift((F0:real^(N,1)finite_sum->real) w)) absolutely_integrable_on
                IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `om0:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:real^(N,1)finite_sum. lift((F0:real^(N,1)finite_sum->real) w)`;
                 `P:real^(N,1)finite_sum->real^(N,1)finite_sum`;
                 `\(z:real^(N,1)finite_sum) (v:real^(N,1)finite_sum). pastecart
                      (frechet_derivative (H:real^N->real^N) (at (fstcart z)) (fstcart v))
                      (lam % sndcart v)`;
                 `N0:real^(N,1)finite_sum->bool`;
                 `integral (IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0)
                    (\w. lift((F0:real^(N,1)finite_sum->real) w))`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integral (IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0)
       (\w. lift((F0:real^(N,1)finite_sum->real) w)) =
    integral om0 (\w. lift(F0 w))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^(N,1)finite_sum. lift((F0:real^(N,1)finite_sum->real) w)`;
                   `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0`;
                   `om0:real^(N,1)finite_sum->bool`] P2AW_INTEGRAL_SUPERSET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(N,1)finite_sum. z IN N0
        ==> abs(det(matrix(\v:real^(N,1)finite_sum. pastecart
                   (frechet_derivative (H:real^N->real^N) (at (fstcart z)) (fstcart v))
                   (lam % sndcart v)))) =
            abs(det(matrix(frechet_derivative H (at (fstcart z))))) * lam`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `linear(frechet_derivative (H:real^N->real^N) (at (fstcart(z:real^(N,1)finite_sum))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      UNDISCH_TAC `diffeomorphism_on (U:real^N->bool) (V:real^N->bool) (H:real^N->real^N)
                                     (H':real^N->real^N)` THEN
      REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    REWRITE_TAC[P2BX_DET_BLOCK] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(N,1)finite_sum. z IN N0 DIFF Z
        ==> lift((Ft:real^(N,1)finite_sum->real) z) =
            sqrt(inv lam pow dimindex(:N)) %
            (abs(det(matrix(\v:real^(N,1)finite_sum. pastecart
                   (frechet_derivative (H:real^N->real^N) (at (fstcart z)) (fstcart v))
                   (lam % sndcart v)))) %
             lift((F0:real^(N,1)finite_sum->real) ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[LIFT_CMUL; VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\z:real^(N,1)finite_sum. sqrt(inv lam pow dimindex(:N)) %
                 (abs(det(matrix(\v:real^(N,1)finite_sum. pastecart
                   (frechet_derivative (H:real^N->real^N) (at (fstcart z)) (fstcart v))
                   (lam % sndcart v)))) %
                  lift((F0:real^(N,1)finite_sum->real) ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z)))`;
      `\z:real^(N,1)finite_sum. lift((Ft:real^(N,1)finite_sum->real) z)`;
      `Z:real^(N,1)finite_sum->bool`; `N0:real^(N,1)finite_sum->bool`] INTEGRABLE_SPIKE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `integral N0 (\z:real^(N,1)finite_sum. sqrt(inv lam pow dimindex(:N)) %
                 (abs(det(matrix(\v:real^(N,1)finite_sum. pastecart
                   (frechet_derivative (H:real^N->real^N) (at (fstcart z)) (fstcart v))
                   (lam % sndcart v)))) %
                  lift((F0:real^(N,1)finite_sum->real) ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z))))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `Z:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_CMUL o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Absolute integrability of the weak integrands; the pointwise              *)
(* transformation laws at differentiability points; the generic transfer of  *)
(* integrals psi Q + c bil(l,psi).                                           *)
(* ========================================================================= *)

(* The integrand psi Q + c bil(A,l,psi) is absolutely integrable. *)

let P2BX_WEAK_ABSINT = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) l psi Q c.
     open om /\ wan_test om psi /\ p2bw_lebm om Q /\ wan_loclip om l /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om)
     ==> (\z. lift(psi z * Q z + c * p2bw_bil A l psi z)) absolutely_integrable_on om`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real`;
                   `Q:real^(N,1)finite_sum->real`] P2BX_TEST_LEBM_ABSINT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN
  SUBGOAL_THEN
   `!z. p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l psi z =
        sum(1..dimindex(:N))
          (\j. drop(frechet_derivative (\y. lift((psi:real^(N,1)finite_sum->real) y)) (at z)
                     (pastecart (basis j) (vec 0))) *
               sum(1..dimindex(:N)) (\i. A z$i$j * wan_xder i l z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[p2bw_bil; GSYM wan_xder] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real`;
                 `\z. sum(1..dimindex(:N))
                        (\i. (A:real^(N,1)finite_sum->real^N^N) z$i$j * wan_xder i l z)`]
                P2BX_TEST_LEBM_ABSINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LEBM_SUM THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_SIMP_TAC[];
      REWRITE_TAC[wan_xder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `pastecart (basis j:real^N) (vec 0:real^1)` o CONJUNCT2) THEN
    REWRITE_TAC[]]);;

(* A function vanishing on an open neighbourhood has zero derivatives. *)

let P2BX_DERIV_ZERO_OPEN = prove
 (`!(f:real^M->real) O w.
     open O /\ w IN O /\ (!x. x IN O ==> f x = &0)
     ==> frechet_derivative (\y. lift(f y)) (at w) = (\v. vec 0)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN EXISTS_TAC `\y:real^M. lift(&0)` THEN
  UNDISCH_TAC `open(O:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN REPEAT STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[DIST_SYM]);;

(* The transformation laws at a point where l0 is differentiable. *)

let P2BX_TRANSFER_POINT = prove
 (`!(U:real^N->bool) V H H' lam (G0:real^(N,1)finite_sum->real^N^N) l0 psi N0 G l phi z.
     diffeomorphism_on U V H H' /\ &0 < lam /\ open N0 /\ z IN N0 /\
     transp(G0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))) =
     G0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
     (!v. ~(v = vec 0)
          ==> &0 < v dot (G0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) ** v)) /\
     (!w. w IN N0
          ==> fstcart w IN U /\
              G w = inv lam %% (transp(matrix(frechet_derivative H (at (fstcart w)))) **
                               G0(pastecart (H(fstcart w)) (lift(lam * drop(sndcart w)))) **
                               matrix(frechet_derivative H (at (fstcart w)))) /\
              l w = l0(pastecart (H(fstcart w)) (lift(lam * drop(sndcart w)))) /\
              phi w = psi(pastecart (H(fstcart w)) (lift(lam * drop(sndcart w))))) /\
     (\w. lift(l0 w)) differentiable at (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
     (\w. lift(psi w)) differentiable at (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))
     ==> wan_tder l z =
         lam * wan_tder l0 (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
         sqrt(det(G z)) =
         (sqrt(inv lam pow dimindex(:N)) * abs(det(matrix(frechet_derivative H (at (fstcart z)))))) *
         sqrt(det(G0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))))) /\
         p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l l z =
         lam * (sqrt(inv lam pow dimindex(:N)) *
                abs(det(matrix(frechet_derivative H (at (fstcart z)))))) *
         p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0
                  (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
         p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l phi z =
         lam * (sqrt(inv lam pow dimindex(:N)) *
                abs(det(matrix(frechet_derivative H (at (fstcart z)))))) *
         p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 psi
                  (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `zz = pastecart ((H:real^N->real^N)(fstcart (z:real^(N,1)finite_sum)))
                             (lift(lam * drop(sndcart z)))` THEN
  ABBREV_TAC `M = matrix(frechet_derivative (H:real^N->real^N) (at (fstcart (z:real^(N,1)finite_sum))))` THEN
  SUBGOAL_THEN `fstcart(z:real^(N,1)finite_sum) IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(M:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `U:real^N->bool`; `H':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G0:real^(N,1)finite_sum->real^N^N) zz)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_DET_NZ] THEN
    MP_TAC(ISPEC `(G0:real^(N,1)finite_sum->real^N^N) zz` P2BW_COEFF_POINT) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^(N,1)finite_sum->real^N^N) z =
                inv lam %% (transp(M:real^N^N) ** (G0:real^(N,1)finite_sum->real^N^N) zz ** M)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`; `l0:real^(N,1)finite_sum->real`; `l:real^(N,1)finite_sum->real`;
                 `N0:real^(N,1)finite_sum->bool`; `z:real^(N,1)finite_sum`] P2BX_PHI_CHAIN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`; `psi:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`;
                 `N0:real^(N,1)finite_sum->bool`; `z:real^(N,1)finite_sum`] P2BX_PHI_CHAIN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!(u:real^(N,1)finite_sum->real) u0.
      ((lambda i. wan_xder i u z):real^N) = transp(M:real^N^N) ** (lambda j. wan_xder j u0 zz)
      ==> p2bw_bil (\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) %% matrix_inv(G z)) l u z =
          lam * (sqrt(inv lam pow dimindex(:N)) * abs(det M)) *
          p2bw_bil (\w. sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) %% matrix_inv(G0 w)) l0 u0 zz`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[P2BX_BIL_DOT] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[P2BX_BIL_TRANSFER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(det(inv lam %% (transp(M:real^N^N) ** (G0:real^(N,1)finite_sum->real^N^N) zz ** M))) =
    (sqrt(inv lam pow dimindex(:N)) * abs(det(M:real^N^N))) *
    sqrt(det((G0:real^(N,1)finite_sum->real^N^N) zz))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`M:real^N^N`; `(G0:real^(N,1)finite_sum->real^N^N) zz`; `lam:real`]
                  P2BX_METRIC_ALG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The generic transfer of the integrals psi Q0 + c bil0(l0,psi) along Phi,  *)
(* with the moved test psi.                                                  *)
(* ========================================================================= *)

let P2BX_BIL_ZERO_RIGHT = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u v z.
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_xder j v z = &0)
     ==> p2bw_bil A u v z = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_bil] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_RZERO]);;

(* wan_xder vanishes where the function vanishes on an open neighbourhood. *)

let P2BX_XDER_ZERO_OPEN = prove
 (`!(f:real^(N,1)finite_sum->real) O w.
     open O /\ w IN O /\ (!x. x IN O ==> f x = &0)
     ==> (!j. wan_xder j f w = &0) /\ wan_tder f w = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX_DERIV_ZERO_OPEN) THEN
  ASM_REWRITE_TAC[wan_xder; wan_tder; DROP_VEC]);;

(* The non-differentiability set of a locally Lipschitz function on an open *)
(* set is negligible.                                                         *)

let P2BX_LOCLIP_AE_OPEN = prove
 (`!(om:real^M->bool) u.
     open om /\ wan_loclip om u
     ==> negligible {z | z IN om /\ ~((\y. lift(u y)) differentiable at z)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `f:num->real^M->bool` STRIP_ASSUME_TAC o
    MATCH_MP OPEN_UNION_COMPACT_SUBSETS) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `UNIONS {{z | z IN (f:num->real^M->bool) n /\
                           ~((\y. lift((u:real^M->real) y)) differentiable at z)} | n IN (:num)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC P2BW_LOCLIP_AE_ON THEN EXISTS_TAC `om:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^M) IN UNIONS {f n | n IN (:num)}` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((\y. lift((u:real^M->real) y)) differentiable at z)` THEN SET_TAC[]);;

(* The generic transfer. *)

let P2BX_WEAK_TRANSFER_GEN = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 l0 Q0 c N0 G l Qt phi.
     diffeomorphism_on U V H H' /\ &0 < lam /\ open om0 /\
     (\w. (vectorize:real^N^N->real^(N,N)finite_prod) (G0 w)) continuous_on om0 /\
     (!w. w IN om0 ==> transp(G0 w) = G0 w /\ !v. ~(v = vec 0) ==> &0 < v dot (G0 w ** v)) /\
     wan_loclip om0 l0 /\ p2bw_lebm om0 Q0 /\ open N0 /\
     (!z. z IN N0
          ==> fstcart z IN U /\
              pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))) IN om0 /\
              G z = inv lam %% (transp(matrix(frechet_derivative H (at (fstcart z)))) **
                               G0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) **
                               matrix(frechet_derivative H (at (fstcart z)))) /\
              l z = l0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))) /\
     (!z. z IN N0 /\
          (\w. lift(l0 w)) differentiable at (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))
          ==> Qt z = lam * (sqrt(inv lam pow dimindex(:N)) *
                            abs(det(matrix(frechet_derivative H (at (fstcart z)))))) *
                     Q0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))) /\
     wan_test N0 phi
     ==> ?psi. wan_test om0 psi /\ ((!z. &0 <= phi z) ==> !w. &0 <= psi w) /\
               (\z. lift(phi z * Qt z +
                         c * p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l phi z))
               integrable_on N0 /\
               integral N0 (\z. lift(phi z * Qt z +
                                    c * p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l phi z)) =
               sqrt(inv lam pow dimindex(:N)) %
               integral om0 (\w. lift(psi w * Q0 w +
                                     c * p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 psi w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`] P2BX_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = \z:real^(N,1)finite_sum. pastecart ((H:real^N->real^N)(fstcart z))
                                                     (lift(lam * drop(sndcart z)))` THEN
  ABBREV_TAC `P' = \w:real^(N,1)finite_sum. pastecart ((H':real^N->real^N)(fstcart w))
                                                      (lift(drop(sndcart w) / lam))` THEN
  SUBGOAL_THEN `(N0:real^(N,1)finite_sum->bool) SUBSET {z | fstcart z IN U}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term ((=) `P':real^(N,1)finite_sum->real^(N,1)finite_sum`)) (concl th) &&
    is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "diffeomorphism_on")) THEN
  MP_TAC(ISPECL [`{z:real^(N,1)finite_sum | fstcart z IN U}`;
                 `{w:real^(N,1)finite_sum | fstcart w IN V}`;
                 `P:real^(N,1)finite_sum->real^(N,1)finite_sum`;
                 `P':real^(N,1)finite_sum->real^(N,1)finite_sum`;
                 `N0:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`]
                P2BX_TEST_TRANSPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `psi = \w. if w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0
                        then (phi:real^(N,1)finite_sum->real) (P' w) else &0` THEN
  STRIP_TAC THEN EXISTS_TAC `psi:real^(N,1)finite_sum->real` THEN
  SUBGOAL_THEN `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET om0` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_test om0 (psi:real^(N,1)finite_sum->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_SUBSET THEN
    EXISTS_TAC `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the support of phi and its image *)
  UNDISCH_TAC `wan_test (N0:real^(N,1)finite_sum->bool) phi` THEN
  REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `K:real^(N,1)finite_sum->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum. z IN N0 ==> P'((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z) = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `P':real^(N,1)finite_sum->real^(N,1)finite_sum`)) (concl th) &&
      is_forall(concl th) && can (find_term ((=) `U:real^N->bool`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^(N,1)finite_sum | fstcart z IN U}` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) K)
        ==> (psi:real^(N,1)finite_sum->real) w = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "psi" THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^(N,1)finite_sum` STRIP_ASSUME_TAC o
      REWRITE_RULE[IN_IMAGE]) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `~(w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) K)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) K)
        ==> (!j. wan_xder j (psi:real^(N,1)finite_sum->real) w = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`psi:real^(N,1)finite_sum->real`;
                   `(:real^(N,1)finite_sum) DIFF IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) K`;
                   `w:real^(N,1)finite_sum`] P2BX_XDER_ZERO_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; GSYM closed] THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum.
                 pastecart ((H:real^N->real^N)(fstcart z)) (lift(lam * drop(sndcart z))) =
                 (P:real^(N,1)finite_sum->real^(N,1)finite_sum) z`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  (* the bad set *)
  ABBREV_TAC `Z = {z:real^(N,1)finite_sum | z IN K /\
                   ~((\w. lift((l0:real^(N,1)finite_sum->real) w)) differentiable at
                     ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z))}` THEN
  SUBGOAL_THEN `negligible(Z:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `IMAGE (P':real^(N,1)finite_sum->real^(N,1)finite_sum)
                  {w | w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 /\
                       ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at w)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
      REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `{w | w IN om0 /\
                         ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at w)}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC P2BX_LOCLIP_AE_OPEN THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET om0` THEN
          SET_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
      X_GEN_TAC `w:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{w:real^(N,1)finite_sum | fstcart w IN V}` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && aconv (rhs(concl th)) `{w:real^(N,1)finite_sum | fstcart w IN V}`)) THEN
      UNDISCH_TAC `(w:real^(N,1)finite_sum) IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0` THEN
      UNDISCH_TAC `(N0:real^(N,1)finite_sum->bool) SUBSET {z | fstcart z IN U}` THEN SET_TAC[];
      EXPAND_TAC "Z" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
      EXISTS_TAC `(P:real^(N,1)finite_sum->real^(N,1)finite_sum) z` THEN
      SUBGOAL_THEN `(z:real^(N,1)finite_sum) IN N0` ASSUME_TAC THENL
       [UNDISCH_TAC `(K:real^(N,1)finite_sum->bool) SUBSET N0` THEN
        UNDISCH_TAC `(z:real^(N,1)finite_sum) IN K` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `z:real^(N,1)finite_sum` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* coefficient continuity of the source *)
  MP_TAC(ISPECL [`om0:real^(N,1)finite_sum->bool`; `G0:real^(N,1)finite_sum->real^N^N`]
                P2BW_COEFF_CONT) THEN
  ASM_REWRITE_TAC[p2bw_coeff; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`; `om0:real^(N,1)finite_sum->bool`; `N0:real^(N,1)finite_sum->bool`;
                 `\w. (psi:real^(N,1)finite_sum->real) w * Q0 w +
                      c * p2bw_bil (\w. sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) %%
                                        matrix_inv(G0 w)) l0 psi w`;
                 `\z. (phi:real^(N,1)finite_sum->real) z * Qt z +
                      c * p2bw_bil (\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) %%
                                        matrix_inv(G z)) l phi z`;
                 `Z:real^(N,1)finite_sum->bool`] P2BX_COV_TRANSFER) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `w:real^(N,1)finite_sum` THEN EXPAND_TAC "psi" THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BX_WEAK_ABSINT THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) K)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0)` THEN
      UNDISCH_TAC `(K:real^(N,1)finite_sum->bool) SUBSET N0` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN
     `p2bw_bil (\w. sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) %% matrix_inv(G0 w)) l0
               (psi:real^(N,1)finite_sum->real) w = &0`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
    MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN K` THENL
   [SUBGOAL_THEN `(\w. lift((l0:real^(N,1)finite_sum->real) w)) differentiable at
                  ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z)` ASSUME_TAC THENL
     [UNDISCH_TAC `~((z:real^(N,1)finite_sum) IN Z)` THEN EXPAND_TAC "Z" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                   `lam:real`; `G0:real^(N,1)finite_sum->real^N^N`;
                   `l0:real^(N,1)finite_sum->real`; `psi:real^(N,1)finite_sum->real`;
                   `N0:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                   `l:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`;
                   `z:real^(N,1)finite_sum`] P2BX_TRANSFER_POINT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(ASM_SIMP_TAC[] THEN NO_TAC) THEN
      TRY(X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [wan_test] o
        check (fun th -> concl th = `wan_test (om0:real^(N,1)finite_sum->bool) psi`));
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* outside the support *)
  SUBGOAL_THEN `open((N0:real^(N,1)finite_sum->bool) DIFF K)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^(N,1)finite_sum->real`; `(N0:real^(N,1)finite_sum->bool) DIFF K`;
                 `z:real^(N,1)finite_sum`] P2BX_XDER_ZERO_OPEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_DIFF]; STRIP_TAC] THEN
  SUBGOAL_THEN `~((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z IN IMAGE P K)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((z:real^(N,1)finite_sum) IN K)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^(N,1)finite_sum) = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(y:real^(N,1)finite_sum) IN N0` ASSUME_TAC THENL
     [UNDISCH_TAC `(K:real^(N,1)finite_sum->bool) SUBSET N0` THEN
      UNDISCH_TAC `(y:real^(N,1)finite_sum) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN
   `p2bw_bil (\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) %% matrix_inv(G z)) l
             (phi:real^(N,1)finite_sum->real) z = &0 /\
    p2bw_bil (\w. sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) %% matrix_inv(G0 w)) l0
             (psi:real^(N,1)finite_sum->real) (P z) = &0`
  (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  CONJ_TAC THEN MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* p2bw_t1, p2bw_t2 and p2bw_tid move along                                  *)
(* Phi(x,t) = (H x, lam t) with G = (1/lam) DH' (G0 o Phi) DH,                *)
(* R = lam (R0 o Phi), l = l0 o Phi.                                          *)
(* ========================================================================= *)

(* The common hypotheses, as a predicate on the data. *)

let p2bx_wtr = new_definition
 `p2bx_wtr (U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 R0 l0 N0 G R l <=>
    diffeomorphism_on U V H H' /\ &0 < lam /\
    open om0 /\ (!w. w IN om0 ==> &0 < drop(sndcart w)) /\
    (\w. (vectorize:real^N^N->real^(N,N)finite_prod) (G0 w)) continuous_on om0 /\
    (!w. w IN om0 ==> transp(G0 w) = G0 w /\ !v. ~(v = vec 0) ==> &0 < v dot (G0 w ** v)) /\
    (\w. lift(R0 w)) continuous_on om0 /\ wan_loclip om0 l0 /\
    open N0 /\
    (!z. z IN N0
         ==> fstcart z IN U /\ &0 < drop(sndcart z) /\
             pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))) IN om0 /\
             G z = inv lam %% (transp(matrix(frechet_derivative H (at (fstcart z)))) **
                              G0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) **
                              matrix(frechet_derivative H (at (fstcart z)))) /\
             R z = lam * R0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
             l z = l0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))))`;;

(* The laws of the pointwise quantities at differentiability points. *)

let P2BX_WTR_POINT = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 R0 l0 N0 G R l z.
     p2bx_wtr U V H H' lam om0 G0 R0 l0 N0 G R l /\ z IN N0 /\
     (\w. lift(l0 w)) differentiable at (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))
     ==> wan_tder l z =
         lam * wan_tder l0 (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
         sqrt(det(G z)) =
         (sqrt(inv lam pow dimindex(:N)) * abs(det(matrix(frechet_derivative H (at (fstcart z)))))) *
         sqrt(det(G0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))))) /\
         p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l l z =
         lam * (sqrt(inv lam pow dimindex(:N)) *
                abs(det(matrix(frechet_derivative H (at (fstcart z)))))) *
         p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0
                  (pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
         R z = lam * R0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
         l z = l0(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z)))) /\
         drop(sndcart(pastecart (H(fstcart z)) (lift(lam * drop(sndcart z))))) =
         lam * drop(sndcart z) /\
         &0 < drop(sndcart z) /\
         &0 < sqrt(inv lam pow dimindex(:N)) * abs(det(matrix(frechet_derivative H (at (fstcart z)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx_wtr] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`; `G0:real^(N,1)finite_sum->real^N^N`;
                 `l0:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                 `N0:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `l:real^(N,1)finite_sum->real`; `l:real^(N,1)finite_sum->real`;
                 `z:real^(N,1)finite_sum`] P2BX_TRANSFER_POINT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[SNDCART_PASTECART; LIFT_DROP] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ];
    REWRITE_TAC[GSYM REAL_ABS_NZ; GSYM INVERTIBLE_DET_NZ] THEN
    MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `U:real^N->bool`; `H':real^N->real^N`] THEN
    ASM_SIMP_TAC[]]);;

(* The source pieces are L^infty_loc on om0. *)

let P2BX_WTR_LEBM = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 R0 l0 N0 G R l.
     p2bx_wtr U V H H' lam om0 G0 R0 l0 N0 G R l
     ==> p2bw_lebm om0 (wan_tder l0) /\
         p2bw_lebm om0 (\w. sqrt(det(G0 w))) /\
         p2bw_lebm om0 (p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0) /\
         p2bw_lebm om0 R0 /\ p2bw_lebm om0 l0 /\
         p2bw_lebm om0 (\w. inv(drop(sndcart w))) /\
         !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> (\w. lift((sqrt(det(G0 w)) %% matrix_inv(G0 w))$i$j)) continuous_on om0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx_wtr] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om0:real^(N,1)finite_sum->bool`; `G0:real^(N,1)finite_sum->real^N^N`]
                P2BW_COEFF_CONT) THEN
  ASM_REWRITE_TAC[p2bw_coeff; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `wan_tder (l0:real^(N,1)finite_sum->real) =
                  (\x. drop(frechet_derivative (\y. lift(l0 y)) (at x)
                             (pastecart (vec 0) (lift(&1)))))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; wan_tder]; ALL_TAC] THEN
    MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC P2BW_LEBM_CONT THEN MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN MATCH_MP_TAC P2BW_CONT_TAU_INV THEN
    ASM_SIMP_TAC[]]);;

let P2BX_T1_TRANSFER = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 R0 l0 N0 G R l.
     p2bx_wtr U V H H' lam om0 G0 R0 l0 N0 G R l /\
     p2bw_t1 om0 (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) (\w. sqrt(det(G0 w))) R0 l0
     ==> p2bw_t1 N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP P2BX_WTR_LEBM th) THEN
               STRIP_ASSUME_TAC(REWRITE_RULE[p2bx_wtr] th)) (LABEL_TAC "T1")) THEN
  REWRITE_TAC[p2bw_t1] THEN X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`; `om0:real^(N,1)finite_sum->bool`; `G0:real^(N,1)finite_sum->real^N^N`;
                 `l0:real^(N,1)finite_sum->real`;
                 `\w. wan_tder l0 w * sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) +
                      p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0 w +
                      (&(dimindex(:N)) / (&2 * drop(sndcart w)) - R0 w) * sqrt(det(G0 w))`;
                 `&1`; `N0:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `l:real^(N,1)finite_sum->real`;
                 `\z. wan_tder l z * sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) +
                      p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l l z +
                      (&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * sqrt(det(G z))`;
                 `phi:real^(N,1)finite_sum->real`] P2BX_WEAK_TRANSFER_GEN) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC P2BW_LEBM_ADD THEN ASM_SIMP_TAC[P2BW_LEBM_MUL; ETA_AX] THEN
      MATCH_MP_TAC P2BW_LEBM_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2BW_LEBM_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC P2BW_LEBM_CMUL THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[];
      X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                     `lam:real`; `om0:real^(N,1)finite_sum->bool`; `G0:real^(N,1)finite_sum->real^N^N`;
                     `R0:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                     `N0:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                     `R:real^(N,1)finite_sum->real`; `l:real^(N,1)finite_sum->real`;
                     `z:real^(N,1)finite_sum`] P2BX_WTR_POINT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < lam`; `&0 < drop(sndcart(z:real^(N,1)finite_sum))`] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^(N,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LID]) THEN
  REMOVE_THEN "T1" (MP_TAC o SPEC `psi:real^(N,1)finite_sum->real` o REWRITE_RULE[p2bw_t1]) THEN
  ASM_SIMP_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[DROP_CMUL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_POW_LE THEN
  MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P2BX_T2_TRANSFER = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 R0 l0 N0 G R l.
     p2bx_wtr U V H H' lam om0 G0 R0 l0 N0 G R l /\
     p2bw_t2 om0 (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) (\w. sqrt(det(G0 w))) R0 l0
     ==> p2bw_t2 N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP P2BX_WTR_LEBM th) THEN
               STRIP_ASSUME_TAC(REWRITE_RULE[p2bx_wtr] th)) (LABEL_TAC "T2")) THEN
  REWRITE_TAC[p2bw_t2] THEN X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ARITH `x - &2 * y = x + --(&2) * y`] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`; `om0:real^(N,1)finite_sum->bool`; `G0:real^(N,1)finite_sum->real^N^N`;
                 `l0:real^(N,1)finite_sum->real`;
                 `\w. --(p2bw_bil (\w. sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) %%
                                       matrix_inv(G0 w)) l0 l0 w) +
                      (R0 w + (l0 w - &(dimindex(:N))) / drop(sndcart w)) * sqrt(det(G0 w))`;
                 `--(&2)`; `N0:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `l:real^(N,1)finite_sum->real`;
                 `\z. --(p2bw_bil (\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) %%
                                       matrix_inv(G z)) l l z) +
                      (R z + (l z - &(dimindex(:N))) / drop(sndcart z)) * sqrt(det(G z))`;
                 `phi:real^(N,1)finite_sum->real`] P2BX_WEAK_TRANSFER_GEN) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LEBM_NEG THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
      MATCH_MP_TAC P2BW_LEBM_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC P2BW_LEBM_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2BW_LEBM_CONT THEN REWRITE_TAC[CONTINUOUS_ON_CONST];
      ASM_SIMP_TAC[];
      X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                     `lam:real`; `om0:real^(N,1)finite_sum->bool`; `G0:real^(N,1)finite_sum->real^N^N`;
                     `R0:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                     `N0:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                     `R:real^(N,1)finite_sum->real`; `l:real^(N,1)finite_sum->real`;
                     `z:real^(N,1)finite_sum`] P2BX_WTR_POINT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < lam`; `&0 < drop(sndcart(z:real^(N,1)finite_sum))`] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^(N,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "T2" (MP_TAC o SPEC `psi:real^(N,1)finite_sum->real` o REWRITE_RULE[p2bw_t2]) THEN
  ASM_SIMP_TAC[] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ARITH `x - &2 * y = x + --(&2) * y`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[DROP_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= s * --x ==> s * x <= &0`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_NEG_GE0] THEN FIRST_ASSUM ACCEPT_TAC]);;

let P2BX_TID_TRANSFER = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 R0 l0 N0 G R l.
     p2bx_wtr U V H H' lam om0 G0 R0 l0 N0 G R l /\
     p2bw_tid om0 (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) (\w. sqrt(det(G0 w))) R0 l0
     ==> p2bw_tid N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[p2bx_wtr] th)) MP_TAC) THEN
  REWRITE_TAC[p2bw_tid] THEN BETA_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`] P2BX_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `P = \z:real^(N,1)finite_sum. pastecart ((H:real^N->real^N)(fstcart z))
                                                     (lift(lam * drop(sndcart z)))` THEN
  ABBREV_TAC `P' = \w:real^(N,1)finite_sum. pastecart ((H':real^N->real^N)(fstcart w))
                                                      (lift(drop(sndcart w) / lam))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term ((=) `P':real^(N,1)finite_sum->real^(N,1)finite_sum`)) (concl th) &&
    is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "diffeomorphism_on")) THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum.
                 pastecart ((H:real^N->real^N)(fstcart z)) (lift(lam * drop(sndcart z))) =
                 (P:real^(N,1)finite_sum->real^(N,1)finite_sum) z`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET
                {w:real^(N,1)finite_sum | fstcart w IN V}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && aconv (rhs(concl th)) `{w:real^(N,1)finite_sum | fstcart w IN V}`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `IMAGE (P':real^(N,1)finite_sum->real^(N,1)finite_sum)
     ({w | w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 /\
           ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at w)} UNION
      ({w | w IN om0 /\
            ~(wan_tder l0 w * sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) =
              (R0 w * sqrt(det(G0 w)) -
               p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0 w) / &2 -
              l0 w / (&2 * drop(sndcart w)) * sqrt(det(G0 w)))} INTER IMAGE P N0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN REWRITE_TAC[LE_REFL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `{w | w IN om0 /\
                         ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at w)}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC P2BX_LOCLIP_AE_OPEN THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET om0`
          MP_TAC THENL
           [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; SET_TAC[]]];
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `{w | w IN om0 /\
            ~(wan_tder l0 w * sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) =
              (R0 w * sqrt(det(G0 w)) -
               p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0 w) / &2 -
              l0 w / (&2 * drop(sndcart w)) * sqrt(det(G0 w)))}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
      X_GEN_TAC `w:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_UNION; IN_INTER; IN_ELIM_THM] THEN
      DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{w:real^(N,1)finite_sum | fstcart w IN V}` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET
                   {w:real^(N,1)finite_sum | fstcart w IN V}` THEN
      UNDISCH_TAC `(w IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 /\
                    ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at w)) \/
                   (w IN om0 /\
                    ~(wan_tder l0 w * sqrt(det((G0:real^(N,1)finite_sum->real^N^N) w)) =
                      (R0 w * sqrt(det(G0 w)) -
                       p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0 w) / &2 -
                      l0 w / (&2 * drop(sndcart w)) * sqrt(det(G0 w)))) /\
                   w IN IMAGE P N0` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_UNION; IN_INTER] THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
  EXISTS_TAC `(P:real^(N,1)finite_sum->real^(N,1)finite_sum) z` THEN
  SUBGOAL_THEN `(P':real^(N,1)finite_sum->real^(N,1)finite_sum) (P z) = z` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `P':real^(N,1)finite_sum->real^(N,1)finite_sum`)) (concl th) &&
      is_forall(concl th) && can (find_term ((=) `U:real^N->bool`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x. (P:real^(N,1)finite_sum->real^(N,1)finite_sum) z = P x /\ x IN N0`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXISTS_TAC `z:real^(N,1)finite_sum` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at
                 ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(P:real^(N,1)finite_sum->real^(N,1)finite_sum) z IN om0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC
   `~(wan_tder (l:real^(N,1)finite_sum->real) z * sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) =
      (R z * sqrt(det(G z)) - p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l l z) / &2 -
      l z / (&2 * drop(sndcart z)) * sqrt(det(G z)))` THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`; `om0:real^(N,1)finite_sum->bool`; `G0:real^(N,1)finite_sum->real^N^N`;
                 `R0:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                 `N0:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `R:real^(N,1)finite_sum->real`; `l:real^(N,1)finite_sum->real`;
                 `z:real^(N,1)finite_sum`] P2BX_WTR_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `wan_tder (l0:real^(N,1)finite_sum->real)
      ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) (z:real^(N,1)finite_sum)) *
    sqrt(det((G0:real^(N,1)finite_sum->real^N^N) (P z))) =
    (R0 (P z) * sqrt(det(G0 (P z))) -
     p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 l0 (P z)) / &2 -
    l0 (P z) / (&2 * drop(sndcart(P z))) * sqrt(det(G0 (P z)))` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < lam`; `&0 < drop(sndcart(z:real^(N,1)finite_sum))`] THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The weak forms are local: p2bw_t1, p2bw_t2 (smooth partitions of unity,   *)
(* P2AW_SMOOTH_PARTITION) and p2bw_tid (Lindelof) hold on an open set when   *)
(* they hold near every point.                                               *)
(* ========================================================================= *)

(* Finite covers of compact sets by half balls with a property of the       *)
(* full balls.                                                               *)

let P2BX_FINITE_BALL_COVER = prove
 (`!(k:real^M->bool) (Q:real^M->real->bool).
     compact k /\ (!z. z IN k ==> ?r. &0 < r /\ Q z r)
     ==> ?J (cs:num->real^M) rs.
           (!j. 1 <= j /\ j <= J ==> &0 < rs j /\ Q (cs j) (rs j)) /\
           k SUBSET UNIONS (IMAGE (\j. ball(cs j, rs j / &2)) (1..J))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `r:real^M->real`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `IMAGE (\z:real^M. ball(z, r z / &2)) k` o
    GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL] o check (fun th ->
      is_comb(concl th) && fst(dest_const(rator(concl th))) = "compact")) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN EXISTS_TAC `z:real^M` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\z:real^M. ball(z, r z / &2)`; `k:real^M->bool`;
                 `f':(real^M->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> ((p <=> q) ==> r)`) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^M->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG] o check (fun th ->
    concl th = `FINITE(D:real^M->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real^M` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`CARD(D:real^M->bool)`; `g:num->real^M`;
                        `(r:real^M->real) o (g:num->real^M)`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g:num->real^M) j IN k` (fun th -> ASM_SIMP_TAC[th]) THEN
    SUBGOAL_THEN `(g:num->real^M) j IN D` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `D = IMAGE (g:num->real^M) (1..CARD(D:real^M->bool))`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_NUMSEG];
      UNDISCH_TAC `(D:real^M->bool) SUBSET k` THEN SET_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS(f':(real^M->bool)->bool)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `f' = IMAGE (\z:real^M. ball(z, r z / &2)) D`)) THEN
    SUBGOAL_THEN
     `IMAGE (\z:real^M. ball(z, r z / &2)) D =
      IMAGE (\j. ball((g:num->real^M) j, ((r:real^M->real) o g) j / &2)) (1..CARD(D:real^M->bool))`
    (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o check (fun th ->
        concl th = `D = IMAGE (g:num->real^M) (1..CARD(D:real^M->bool))`)) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

(* Derivatives of finite sums. *)

let P2BX_XDER_SUM = prove
 (`!(f:num->real^(N,1)finite_sum->real) J z.
     (!j. 1 <= j /\ j <= J ==> (\w. lift(f j w)) differentiable at z)
     ==> !i. wan_xder i (\w. sum(1..J) (\j. f j w)) z = sum(1..J) (\j. wan_xder i (f j) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_xder] THEN
  SUBGOAL_THEN
   `frechet_derivative (\w. lift(sum(1..J) (\j. (f:num->real^(N,1)finite_sum->real) j w))) (at z) =
    (\h. vsum(1..J) (\j. frechet_derivative (\w. lift(f j w)) (at z) h))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[LIFT_SUM; o_DEF] THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF] THEN SIMP_TAC[]);;

(* Restrictions of L^infty_loc and locally Lipschitz functions. *)

let P2BX_LEBM_SUBSET = prove
 (`!(s:real^M->bool) t h. p2bw_lebm s h /\ t SUBSET s ==> p2bw_lebm t h`,
  REWRITE_TAC[p2bw_lebm] THEN MESON_TAC[SUBSET_TRANS]);;

let P2BX_LOCLIP_SUBSET = prove
 (`!(s:real^M->bool) t u. wan_loclip s u /\ t SUBSET s ==> wan_loclip t u`,
  REWRITE_TAC[wan_loclip] THEN MESON_TAC[SUBSET_TRANS]);;

(* The bilinear form is linear in the test. *)

let P2BX_BIL_SUM = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u (f:num->real^(N,1)finite_sum->real) J z.
     (!j. 1 <= j /\ j <= J ==> (\w. lift(f j w)) differentiable at z)
     ==> p2bw_bil A u (\w. sum(1..J) (\j. f j w)) z = sum(1..J) (\j. p2bw_bil A u (f j) z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX_XDER_SUM) THEN
  ASM_REWRITE_TAC[p2bw_bil] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

(* The gluing of the weak inequalities. *)

let P2BX_WEAK_GLUE = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) l X c.
     open om /\ p2bw_lebm om X /\ wan_loclip om l /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (!z. z IN om
          ==> ?N. open N /\ z IN N /\ N SUBSET om /\
                  !psi. wan_test N psi /\ (!x. &0 <= psi x)
                        ==> &0 <= drop(integral N
                                    (\x. lift(psi x * X x + c * p2bw_bil A l psi x))))
     ==> !phi. wan_test om phi /\ (!x. &0 <= phi x)
               ==> &0 <= drop(integral om (\x. lift(phi x * X x + c * p2bw_bil A l phi x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test] o check (fun th ->
    concl th = `wan_test (om:real^(N,1)finite_sum->bool) phi`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:real^(N,1)finite_sum->bool`;
                 `\z r. ?N. open N /\ N SUBSET om /\ ball(z:real^(N,1)finite_sum,r) SUBSET N /\
                            !psi. wan_test N psi /\ (!x. &0 <= psi x)
                                  ==> &0 <= drop(integral N
                                    (\x. lift(psi x * X x +
                                              c * p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l psi x)))`]
                P2BX_FINITE_BALL_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum` o check (fun th ->
      can (find_term ((=) `c:real`)) (concl th) && is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open(N:real^(N,1)finite_sum->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `N:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num` (X_CHOOSE_THEN `cs:num->real^(N,1)finite_sum`
    (X_CHOOSE_THEN `rs:num->real` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_AND_EXISTS_THM; RIGHT_IMP_EXISTS_THM] o check (fun th ->
    can (find_term ((=) `rs:num->real`)) (concl th) && is_forall (concl th))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:num->real^(N,1)finite_sum->bool` (LABEL_TAC "NN")) THEN
  MP_TAC(ISPECL [`k:real^(N,1)finite_sum->bool`; `cs:num->real^(N,1)finite_sum`;
                 `rs:num->real`; `J:num`] P2AW_SMOOTH_PARTITION) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:num->real^(N,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
  (* the pieces *)
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= J
        ==> wan_test ((NN:num->real^(N,1)finite_sum->bool) j)
                     (\x. (phi:real^(N,1)finite_sum->real) x * (theta:num->real^(N,1)finite_sum->real) (j:num) x) /\
            open (NN j) /\ NN j SUBSET om /\
            (!x. &0 <= phi x * (theta:num->real^(N,1)finite_sum->real) (j:num) x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "NN" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC WAN_TEST_SUBSET THEN
    EXISTS_TAC `ball((cs:num->real^(N,1)finite_sum) j, rs j)` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(ISPECL [`ball((cs:num->real^(N,1)finite_sum) j, rs j)`;
                   `(theta:num->real^(N,1)finite_sum->real) j`;
                   `phi:real^(N,1)finite_sum->real`] WAN_TEST_SMUL) THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `wfun = \(psi:real^(N,1)finite_sum->real) x.
                    psi x * (X:real^(N,1)finite_sum->real) x +
                    c * p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l psi x` THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= J
        ==> (\x. lift((wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real)
                       (\x. (phi:real^(N,1)finite_sum->real) x * (theta:num->real^(N,1)finite_sum->real) (j:num) x) x))
            integrable_on om /\
            &0 <= drop(integral om (\x. lift(wfun (\x. phi x * (theta:num->real^(N,1)finite_sum->real) (j:num) x) x)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `NN:num->real^(N,1)finite_sum->bool`)) (concl th) &&
      is_forall (concl th) && not (can (find_term ((=) `rs:num->real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "NN" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\x. (phi:real^(N,1)finite_sum->real) x *
                                  (theta:num->real^(N,1)finite_sum->real) (j:num) x` o
      check (fun th -> can (find_term ((=) `c:real`)) (concl th) && is_forall (concl th) &&
                       not (can (find_term ((=) `rs:num->real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x. lift((wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real)
                               (\x. (phi:real^(N,1)finite_sum->real) x *
                                     (theta:num->real^(N,1)finite_sum->real) (j:num) x) x)`;
                   `(NN:num->real^(N,1)finite_sum->bool) j`; `om:real^(N,1)finite_sum->bool`]
                  P2AW_INTEGRAL_SUPERSET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT o check (fun th ->
          can (find_term ((=) `theta:num->real^(N,1)finite_sum->real`)) (concl th) &&
          fst(dest_const(fst(strip_comb(concl th)))) = "wan_test")) THEN
        DISCH_THEN(X_CHOOSE_THEN `kj:real^(N,1)finite_sum->bool` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
        X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~((x:real^(N,1)finite_sum) IN kj)` ASSUME_TAC THENL
         [UNDISCH_TAC `~((x:real^(N,1)finite_sum) IN NN(j:num))` THEN
          UNDISCH_TAC `(kj:real^(N,1)finite_sum->bool) SUBSET NN(j:num)` THEN SET_TAC[];
          ALL_TAC] THEN
        EXPAND_TAC "wfun" THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN ASM_SIMP_TAC[] THEN
        REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
        SUBGOAL_THEN `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l
                        (\x. (phi:real^(N,1)finite_sum->real) x * (theta:num->real^(N,1)finite_sum->real) (j:num) x) x = &0`
        (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
        MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[WAN_XDER_DPART];
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN EXPAND_TAC "wfun" THEN
        MATCH_MP_TAC P2BX_WEAK_ABSINT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC P2BX_LEBM_SUBSET THEN EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
          ASM_REWRITE_TAC[];
          REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[]]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "wfun" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the integrand of phi is the sum *)
  SUBGOAL_THEN
   `!x. (wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real) phi x =
        sum(1..J) (\j. wfun (\x. phi x * (theta:num->real^(N,1)finite_sum->real) j x) x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    SUBGOAL_THEN `(phi:real^(N,1)finite_sum->real) =
                  (\x. sum(1..J) (\j. phi x * (theta:num->real^(N,1)finite_sum->real) j x))`
    (fun th -> EXPAND_TAC "wfun" THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; SUM_LMUL] THEN X_GEN_TAC `y:real^(N,1)finite_sum` THEN
      ASM_CASES_TAC `(y:real^(N,1)finite_sum) IN k` THEN
      ASM_SIMP_TAC[REAL_MUL_RID; REAL_MUL_LZERO];
      ALL_TAC] THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`A:real^(N,1)finite_sum->real^N^N`; `l:real^(N,1)finite_sum->real`;
                   `\j x. (phi:real^(N,1)finite_sum->real) x *
                          (theta:num->real^(N,1)finite_sum->real) j x`;
                   `J:num`; `x:real^(N,1)finite_sum`] P2BX_BIL_SUM) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        can (find_term ((=) `NN:num->real^(N,1)finite_sum->bool`)) (concl th) &&
        is_forall (concl th) && not (can (find_term ((=) `rs:num->real`)) (concl th)) &&
        not (can (find_term ((=) `wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real`))
                 (concl th)))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[wan_test] THEN STRIP_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om (\x. lift((phi:real^(N,1)finite_sum->real) x * X x +
                          c * p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l phi x)) =
    vsum(1..J) (\j. integral om
      (\x. lift((wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real)
                 (\x. phi x * (theta:num->real^(N,1)finite_sum->real) j x) x)))`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `integral om (\x. vsum(1..J) (\j.
         lift((wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real)
              (\x. (phi:real^(N,1)finite_sum->real) x *
                   (theta:num->real^(N,1)finite_sum->real) j x) x)))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(N,1)finite_sum` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real`))
            (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "sum")) (concl th))) THEN
      EXPAND_TAC "wfun" THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF];
      MP_TAC(ISPECL [`\(j:num) (x:real^(N,1)finite_sum).
                        lift((wfun:(real^(N,1)finite_sum->real)->real^(N,1)finite_sum->real)
                             (\x. (phi:real^(N,1)finite_sum->real) x *
                                  (theta:num->real^(N,1)finite_sum->real) j x) x)`;
                     `om:real^(N,1)finite_sum->bool`; `1..J`] INTEGRAL_VSUM) THEN
      BETA_TAC THEN ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ASM_SIMP_TAC[];
        DISCH_THEN(fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  ASM_SIMP_TAC[]);;

(* The integrands of p2bw_t1 and p2bw_t2 are L^infty_loc. *)

let P2BX_T12_LEBM = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l
     ==> p2bw_lebm om (\z. wan_tder l z * rho z + p2bw_bil A l l z +
                           (&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * rho z) /\
         p2bw_lebm om (\z. --(p2bw_bil A l l z) +
                           (R z + (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z) /\
         p2bw_lebm om (\z. p2bw_bil A l l z -
                           (R z + (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bw_lebm om (p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bw_lebm om (\z. ((R:real^(N,1)finite_sum->real) z +
                       ((l:real^(N,1)finite_sum->real) z - &(dimindex(:N))) / drop(sndcart z)) *
                      (rho:real^(N,1)finite_sum->real) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN
    MATCH_MP_TAC P2BW_CONT_T2COEFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[wan_tder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_REWRITE_TAC[ETA_AX]];
      MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[ETA_AX];
        MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN
        MATCH_MP_TAC P2BW_CONT_T1COEFF THEN ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC P2BW_LEBM_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BW_LEBM_NEG THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC P2BW_LEBM_SUB THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* p2bw_t1 is local. *)

let P2BX_T1_GLUE = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\
     (!z. z IN om ==> ?N. open N /\ z IN N /\ N SUBSET om /\ p2bw_t1 N A rho R l)
     ==> p2bw_t1 om A rho R l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P2BX_T12_LEBM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
     `l:real^(N,1)finite_sum->real`;
     `\z. wan_tder (l:real^(N,1)finite_sum->real) z * (rho:real^(N,1)finite_sum->real) z +
          p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z +
          (&(dimindex(:N)) / (&2 * drop(sndcart z)) - (R:real^(N,1)finite_sum->real) z) * rho z`;
     `&1`] P2BX_WEAK_GLUE)) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_t1")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:real^(N,1)finite_sum->bool`
      (STRIP_ASSUME_TAC o REWRITE_RULE[p2bw_t1])) THEN
    EXISTS_TAC `N:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[p2bw_t1] THEN ASM_REWRITE_TAC[]]);;

(* p2bw_t2 as a nonnegativity statement. *)

let P2BX_T2_EQUIV = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l
     ==> (p2bw_t2 om A rho R l <=>
          !phi. wan_test om phi /\ (!x. &0 <= phi x)
                ==> &0 <= drop(integral om
                       (\x. lift(phi x * (p2bw_bil A l l x -
                                          (R x + (l x - &(dimindex(:N))) / drop(sndcart x)) *
                                          rho x) +
                                 &2 * p2bw_bil A l phi x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P2BX_T12_LEBM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bw_t2] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN
  ASM_CASES_TAC `wan_test (om:real^(N,1)finite_sum->bool) phi` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift((phi:real^(N,1)finite_sum->real) x *
              (p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l x -
               ((R:real^(N,1)finite_sum->real) x + (l x - &(dimindex(:N))) / drop(sndcart x)) *
               (rho:real^(N,1)finite_sum->real) x) +
              &2 * p2bw_bil A l phi x)) =
    (\x. --(lift(phi x * (--(p2bw_bil A l l x) +
                          (R x + (l x - &(dimindex(:N))) / drop(sndcart x)) * rho x) -
                 &2 * p2bw_bil A l phi x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_NEG; LIFT_EQ] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om (\x. --(lift((phi:real^(N,1)finite_sum->real) x *
                  (--(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l x) +
                   ((R:real^(N,1)finite_sum->real) x + (l x - &(dimindex(:N))) / drop(sndcart x)) *
                   (rho:real^(N,1)finite_sum->real) x) -
                  &2 * p2bw_bil A l phi x))) =
    --integral om (\x. lift(phi x * (--(p2bw_bil A l l x) +
                          (R x + (l x - &(dimindex(:N))) / drop(sndcart x)) * rho x) -
                 &2 * p2bw_bil A l phi x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NEG THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(BETA_RULE(ISPECL
      [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
       `l:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`;
       `\x. --(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l x) +
            ((R:real^(N,1)finite_sum->real) x + (l x - &(dimindex(:N))) / drop(sndcart x)) *
            (rho:real^(N,1)finite_sum->real) x`;
       `--(&2)`] P2BX_WEAK_ABSINT)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DROP_NEG; REAL_NEG_GE0]);;

(* p2bw_t2 is local. *)

let P2BX_T2_GLUE = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\
     (!z. z IN om ==> ?N. open N /\ z IN N /\ N SUBSET om /\ p2bw_t2 N A rho R l)
     ==> p2bw_t2 om A rho R l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P2BX_T12_LEBM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P2BX_T2_EQUIV) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
     `l:real^(N,1)finite_sum->real`;
     `\x. p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l x -
          ((R:real^(N,1)finite_sum->real) x + (l x - &(dimindex(:N))) / drop(sndcart x)) *
          (rho:real^(N,1)finite_sum->real) x`;
     `&2`] P2BX_WEAK_GLUE)) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_t2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`N:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                 `rho:real^(N,1)finite_sum->real`; `R:real^(N,1)finite_sum->real`;
                 `l:real^(N,1)finite_sum->real`] P2BX_T2_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(fun th -> UNDISCH_TAC `p2bw_t2 (N:real^(N,1)finite_sum->bool)
                                        (A:real^(N,1)finite_sum->real^N^N) rho R l` THEN
                         REWRITE_TAC[th])]);;

(* p2bw_tid is local (Lindelof). *)

let P2BX_TID_GLUE = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l.
     (!z. z IN om ==> ?N. open N /\ z IN N /\ N SUBSET om /\ p2bw_tid N A rho R l)
     ==> p2bw_tid om A rho R l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2bw_tid] THEN
  MP_TAC(ISPEC `{N:real^(N,1)finite_sum->bool |
                   open N /\ N SUBSET om /\
                   p2bw_tid N (A:real^(N,1)finite_sum->real^N^N) rho R l}` LINDELOF) THEN
  ANTS_TAC THENL [SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^(N,1)finite_sum->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\N. {z | z IN N /\
                    ~(wan_tder (l:real^(N,1)finite_sum->real) z * (rho:real^(N,1)finite_sum->real) z =
                      ((R:real^(N,1)finite_sum->real) z * rho z -
                       p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) / &2 -
                      l z / (&2 * drop(sndcart z)) * rho z)})
                  (f':(real^(N,1)finite_sum->bool)->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `N:real^(N,1)finite_sum->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2bw_tid (N:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l`
    MP_TAC THENL
     [UNDISCH_TAC `(N:real^(N,1)finite_sum->bool) IN f'` THEN
      UNDISCH_TAC `(f':(real^(N,1)finite_sum->bool)->bool) SUBSET
                   {N | open N /\ N SUBSET om /\
                        p2bw_tid N (A:real^(N,1)finite_sum->real^N^N) rho R l}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[p2bw_tid]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^(N,1)finite_sum) IN UNIONS f'` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_tid")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:real^(N,1)finite_sum->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]);;

