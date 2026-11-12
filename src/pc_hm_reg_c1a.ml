(* ========================================================================= *)
(* Unit pc_hm_reg_c1a (a unit of the harmonic map regularity chain of        *)
(* pc_hm_regularity): continuous weakly harmonic maps are C^(1,al).  The     *)
(* weak Euler-Lagrange equation (HMRM_WHARMONIC_EL) is extended to bounded   *)
(* W_0^(1,2) tests; comparison with the harmonic replacement on small discs  *)
(* gives Morrey decay of the energy, Hoelder continuity, and Campanato decay *)
(* of the weak gradient.                                                     *)
(* ========================================================================= *)

needs "src/pc_hm_rmin_fv.ml";;
needs "src/pc_hm_reg_boot.ml";;
needs "src/pc_wan_lap2d.ml";;
needs "src/pc_wan_sob2pb.ml";;
needs "src/pc_wan_sob2r.ml";;
needs "src/pc_hm_dirichlet.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Euler-Lagrange density hmrm_eld is linear in the test arguments and   *)
(* bounded by C(|h| |q|^2 + |q| |k|); a smooth bounded truncation of the     *)
(* identity.                                                                 *)
(* ========================================================================= *)

let HMRC_ELD_SUB = prove
 (`!S (G:real^K->real^K^K) d p q h1 h2 k1 k2.
     cm_target S G d /\ p IN S
     ==> hmrm_eld S G p q h1 k1 - hmrm_eld S G p q h2 k2 =
         hmrm_eld S G p q (h1 - h2) (k1 - k2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point (S:real^K->bool)) (at y))) differentiable (at (p:real^K)) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) differentiable (at p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[hmrm_eld] THEN ASM_SIMP_TAC[HMC_MDERIV_SUB; MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
              DOT_LSUB; DOT_RSUB; DOT_LADD; DOT_RADD] THEN
  REAL_ARITH_TAC);;

let HMRC_ELD_BOUND = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?Ca Cb. &0 <= Ca /\ &0 <= Cb /\
                 !p q h k. p IN S
                           ==> abs(hmrm_eld S G p q h k)
                               <= Ca * norm h * norm q pow 2 + Cb * norm q * norm k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam1:real` (X_CHOOSE_THEN `CJ:real`
    (X_CHOOSE_THEN `CG:real` (X_CHOOSE_THEN `C2:real` (X_CHOOSE_THEN `C3:real`
    (X_CHOOSE_THEN `C4:real` STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  MAP_EVERY EXISTS_TAC [`&2 * CJ * Lam1 + CG`; `&2 * Lam1`] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^K`; `q:real^K`; `h:real^K`; `k:real^K`] THEN DISCH_TAC THEN
  ABBREV_TAC `Jp = jacobian (closest_point (S:real^K->bool)) (at p)` THEN
  SUBGOAL_THEN `norm((Jp:real^K^K) ** (k:real^K)) <= norm k /\ norm(Jp ** (h:real^K)) <= norm h`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMC_PROJ_NORM THEN EXPAND_TAC "Jp" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(mderiv (\y. jacobian (closest_point (S:real^K->bool)) (at y)) p h ** (q:real^K))
    <= CJ * norm(h:real^K) * norm q /\
    norm((G:real^K->real^K^K) p ** q) <= Lam1 * norm q /\
    norm(mderiv G p ((Jp:real^K^K) ** h) ** q) <= CG * norm h * norm q`
  MP_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CG * norm((Jp:real^K^K) ** (h:real^K)) * norm(q:real^K)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `A1 = mderiv (\y. jacobian (closest_point (S:real^K->bool)) (at y)) p h ** (q:real^K)` THEN
  ABBREV_TAC `A2 = (Jp:real^K^K) ** (k:real^K)` THEN
  ABBREV_TAC `C1 = (G:real^K->real^K^K) p ** (q:real^K)` THEN
  ABBREV_TAC `D1 = mderiv (G:real^K->real^K^K) p ((Jp:real^K^K) ** h) ** (q:real^K)` THEN
  STRIP_TAC THEN
  REWRITE_TAC[hmrm_eld] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A1 + A2:real^K`; `C1:real^K`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  MP_TAC(ISPECL [`q:real^K`; `D1:real^K`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  MP_TAC(ISPECL [`A1:real^K`; `A2:real^K`] NORM_TRIANGLE) THEN
  SUBGOAL_THEN
   `(norm(A1:real^K) + norm(A2:real^K)) * norm(C1:real^K) <=
    (CJ * norm(h:real^K) * norm(q:real^K) + norm(k:real^K)) * (Lam1 * norm q) /\
    norm(q:real^K) * norm(D1:real^K) <= norm q * (CG * norm(h:real^K) * norm q)`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_ADD; NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= norm(C1:real^K)` MP_TAC THENL [REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(A1 + A2:real^K) * norm(C1:real^K) <= (norm A1 + norm A2) * norm C1`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; NORM_TRIANGLE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* A smooth bounded truncation of the identity map. *)

let HMRC_TRUNC = prove
 (`!R. &0 < R
       ==> ?Tr:real^K->real^K.
             smooth_map_on (:real^K) Tr /\ Tr(vec 0) = vec 0 /\
             (!y. norm(Tr y) <= &2 * R) /\
             (!y. norm y < R ==> Tr y = y) /\
             (!y. norm y < R ==> frechet_derivative Tr (at y) = (\v. v)) /\
             (?L. &0 <= L /\ !y v. norm(frechet_derivative Tr (at y) v) <= L * norm v)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\y:real^K. smooth_bump R (&2 * R) y % y` THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) (\y:real^K. smooth_bump R (&2 * R) y % y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^K)`; `\y:real^K. lift(smooth_bump R (&2 * R) y)`; `\y:real^K. y`]
      SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^K. norm y < R ==> smooth_bump R (&2 * R) y % y = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`R:real`; `&2 * R`; `y:real^K`] SMOOTH_BUMP_1) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^K` THEN ASM_CASES_TAC `&2 * R <= norm(y:real^K)` THENL
     [MP_TAC(ISPECL [`R:real`; `&2 * R`; `y:real^K`] SMOOTH_BUMP_0) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[VECTOR_MUL_LZERO; NORM_0] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[NORM_MUL] THEN
      MP_TAC(ISPECL [`R:real`; `&2 * R`; `y:real^K`] SMOOTH_BUMP_BOUNDS) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[real_abs] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm(y:real^K)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
        ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\y:real^K. y`; `R - norm(y:real^K)`] THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^K` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(NORM_ARITH `norm(z:real^K) <= norm(y:real^K) + norm(z - y)`) THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\y:real^K. smooth_bump R (&2 * R) y % y`; `cball(vec 0:real^K,&2 * R)`]
      HMR_CSUPP_DERIV_BOUND) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`R:real`; `&2 * R`; `y:real^K`] SMOOTH_BUMP_0) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[VECTOR_MUL_LZERO]];
      MESON_TAC[]]]);;

(* ========================================================================= *)
(* Measurability and integrability of the Euler-Lagrange density along a     *)
(* continuous map with continuous bounded test values and L^2 test           *)
(* derivatives.                                                              *)
(* ========================================================================= *)

let HMRC_MDERIV_CONT = prove
 (`!V s (M:real^N->real^N^N) (w:real^2->real^N) (A:real^2->real^N).
     open V /\ smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o M) /\
     w continuous_on s /\ (!z. z IN s ==> w z IN V) /\ A continuous_on s
     ==> ((vectorize:real^N^N->real^(N,N)finite_prod) o (\z. mderiv M (w z) (A z)))
         continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\z. vsum(1..dimindex(:N))
                    (\k. drop(lift((A:real^2->real^N) z$k)) %
                         partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                               (M:real^N->real^N^N)) ((w:real^2->real^N) z))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; mderiv; VECTORIZE_MATRIFY; LIFT_DROP; partial_derivative] THEN
    SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o M) differentiable
                  at ((w:real^2->real^N) z)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               (M:real^N->real^N^N)) ((w:real^2->real^N) z)) =
    partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o M) o w`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

(* Integrability of the density. *)

let HMRC_ELD_INTEGRABLE = prove
 (`!S (G:real^K->real^K^K) d (B:real^2->bool) (u:real^2->real^K) w q k M.
     cm_target S G d /\ open B /\ u continuous_on B /\ (!x. x IN B ==> u x IN S) /\
     w continuous_on B /\ (!x. x IN B ==> norm(w x) <= M) /\
     q IN lspace B (&2) /\ k IN lspace B (&2)
     ==> (\x. lift(hmrm_eld S G (u x) (q x) (w x) (k x))) integrable_on B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca:real` (X_CHOOSE_THEN `Cb:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRC_ELD_BOUND) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `!x. x IN B ==> (u:real^2->real^K) x IN cm_tube S d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\x. jacobian (closest_point (S:real^K->bool)) (at ((u:real^2->real^K) x))))
    continuous_on B /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (\x. (G:real^K->real^K^K)(u x)))
    continuous_on B`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `((vectorize:real^K^K->real^(K,K)finite_prod) o
         (\x. jacobian (closest_point (S:real^K->bool)) (at ((u:real^2->real^K) x)))) =
        ((vectorize:real^K^K->real^(K,K)finite_prod) o
         (\y. jacobian (closest_point S) (at y))) o u`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET; FORALL_IN_IMAGE];
      SUBGOAL_THEN
       `((vectorize:real^K^K->real^(K,K)finite_prod) o
         (\x. (G:real^K->real^K^K)((u:real^2->real^K) x))) =
        ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o u`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. jacobian (closest_point (S:real^K->bool)) (at ((u:real^2->real^K) x)) **
                     (w:real^2->real^K) x) continuous_on B`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^2->real^K) measurable_on B /\ (k:real^2->real^K) measurable_on B`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^2->real^K) IN lspace B (&2)` THEN
    UNDISCH_TAC `(k:real^2->real^K) IN lspace B (&2)` THEN
    REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(Ca * M * norm((q:real^2->real^K) x) pow 2 +
                       Cb * (norm(q x) * norm((k:real^2->real^K) x)))` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                         ((w:real^2->real^K) x) ((k:real^2->real^K) x))) =
      (\x. lift(&2 * (((matrify(((vectorize:real^K^K->real^(K,K)finite_prod) o
                         (\x. mderiv (\y. jacobian (closest_point S) (at y)) (u x) (w x))) x)
                        :real^K^K) ** q x +
                       (matrify(((vectorize:real^K^K->real^(K,K)finite_prod) o
                         (\x. jacobian (closest_point S) (at (u x)))) x):real^K^K) ** k x) dot
                      ((matrify(((vectorize:real^K^K->real^(K,K)finite_prod) o
                         (\x. G(u x))) x):real^K^K) ** q x)) +
                q x dot ((matrify(((vectorize:real^K^K->real^(K,K)finite_prod) o
                         (\x. mderiv G (u x) (jacobian (closest_point S) (at (u x)) ** w x))) x)
                        :real^K^K) ** q x)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; hmrm_eld; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC HMC_LD_FORM_MEAS THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN MATCH_MP_TAC HMRC_MDERIV_CONT THENL
     [EXISTS_TAC `cm_tube (S:real^K->bool) d`; EXISTS_TAC `(:real^K)`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE];
      ONCE_REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
      MAP_EVERY EXISTS_TAC [`&2`; `&2`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Ca * norm((w:real^2->real^K) x) * norm((q:real^2->real^K) x) pow 2 +
                Cb * norm(q x) * norm((k:real^2->real^K) x)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_POW_2]]);;

(* ========================================================================= *)
(* Tools for passing to the limit in the Euler-Lagrange identity along       *)
(* truncated test maps.                                                      *)
(* ========================================================================= *)

let HMRC_ELD_SPLIT = prove
 (`!S (G:real^K->real^K^K) d p q h k.
     cm_target S G d /\ p IN S
     ==> hmrm_eld S G p q h k = hmrm_eld S G p q h (vec 0) + hmrm_eld S G p q (vec 0) k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`;
                 `h:real^K`; `vec 0:real^K`; `k:real^K`; `k:real^K`] HMRC_ELD_SUB) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN REAL_ARITH_TAC);;

let HMRC_SQ_NULL = prove
 (`!a b. (!n:num. &0 <= a n) /\ (!n. a n pow 2 <= b n) /\ (b ---> &0) sequentially
         ==> (a ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n:num. sqrt(b n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[real_abs] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 = sqrt(&0)` SUBST1_TAC THENL [REWRITE_TAC[SQRT_0]; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT]]);;

let HMRC_FD_CONT = prove
 (`!(Tr:real^K->real^N) v.
     smooth_map_on (:real^K) Tr
     ==> (\y. frechet_derivative Tr (at y) v) continuous_on (:real^K)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\y. vsum(1..dimindex(:K))
                    (\k. drop(lift((v:real^K)$k)) % partial_derivative k (Tr:real^K->real^N) y)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP; partial_derivative] THEN
    SUBGOAL_THEN `(Tr:real^K->real^N) differentiable at y` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; ETA_AX]);;

(* L^2 convergence of the derivative of the truncation applied to a fixed   *)
(* L^2 field along an a.e. convergent sequence.                             *)

let HMRC_L2_DT_CONV = prove
 (`!(B:real^2->bool) (Tr:real^K->real^K) L R (f:num->real^2->real^K) (w:real^2->real^K)
    (g:real^2->real^K) Z.
     open B /\ smooth_map_on (:real^K) Tr /\ &0 <= L /\
     (!y v. norm(frechet_derivative Tr (at y) v) <= L * norm v) /\
     (!y. norm y < R ==> frechet_derivative Tr (at y) = (\v. v)) /\
     (!n. (f n) continuous_on B) /\ g IN lspace B (&2) /\ negligible Z /\
     (!x. x IN B DIFF Z ==> ((\n. f n x) --> w x) sequentially) /\
     (!x. x IN B ==> norm(w x) < R)
     ==> (!n. (\x. frechet_derivative Tr (at (f n x)) (g x)) IN lspace B (&2)) /\
         ((\n. lnorm B (&2) (\x. frechet_derivative Tr (at (f n x)) (g x) - g x)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. L % (g:real^2->real^K) x) IN lspace B (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LSPACE_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^K) measurable_on B` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^2->real^K) IN lspace B (&2)` THEN
    REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y v. norm(frechet_derivative (Tr:real^K->real^K) (at y) v) <= norm(L % v)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; real_abs]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
                                ((g:real^2->real^K) x)) IN lspace B (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`B:real^2->bool`; `&2`;
                   `\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
                                           ((g:real^2->real^K) x)`;
                   `\x. L % (g:real^2->real^K) x`] LSPACE_BOUNDED_MEASURABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(ISPECL [`B:real^2->bool`;
                   `\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))`;
                   `g:real^2->real^K`] HMC_MEAS_LINEAR_APPLY) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x)) (basis k)) =
        (\y. frechet_derivative Tr (at y) (basis k)) o f n`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      ASM_SIMP_TAC[HMRC_FD_CONT; SUBSET_UNIV]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\n x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
                              ((g:real^2->real^K) x)`;
    `g:real^2->real^K`; `\x. L % (g:real^2->real^K) x`; `B:real^2->bool`; `&2`;
    `Z:real^2->bool`] LSPACE_DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^K) x = frechet_derivative (Tr:real^K->real^K) (at (w x)) (g x)`
  (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
   [SUBGOAL_THEN `norm((w:real^2->real^K) x) < R` (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. frechet_derivative (Tr:real^K->real^K) (at y) ((g:real^2->real^K) x)`;
                 `sequentially`; `\n. (f:num->real^2->real^K) n x`; `(w:real^2->real^K) x`]
    LIM_CONTINUOUS_FUNCTION) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`Tr:real^K->real^K`; `(g:real^2->real^K) x`] HMRC_FD_CONT) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]);;

(* Passing to the limit in the density: bounded a.e. convergence of the     *)
(* test values and L^2 convergence of the test derivatives.                  *)

let HMRC_ELD_LIMIT = prove
 (`!S (G:real^K->real^K^K) d (B:real^2->bool) (u:real^2->real^K) (q:real^2->real^K)
    (h:num->real^2->real^K) (k:num->real^2->real^K) (w:real^2->real^K) (kw:real^2->real^K)
    C0 Z.
     cm_target S G d /\ open B /\ u continuous_on B /\ (!x. x IN B ==> u x IN S) /\
     q IN lspace B (&2) /\
     (!n. (h n) continuous_on B) /\ (!n x. x IN B ==> norm(h n x) <= C0) /\
     w continuous_on B /\ (!x. x IN B ==> norm(w x) <= C0) /\
     negligible Z /\ (!x. x IN B DIFF Z ==> ((\n. h n x) --> w x) sequentially) /\
     (!n. k n IN lspace B (&2)) /\ kw IN lspace B (&2) /\
     ((\n. lnorm B (&2) (\x. k n x - kw x)) ---> &0) sequentially
     ==> ((\n. drop(integral B (\x. lift(hmrm_eld S G (u x) (q x) (h n x) (k n x))))) --->
          drop(integral B (\x. lift(hmrm_eld S G (u x) (q x) (w x) (kw x))))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca:real` (X_CHOOSE_THEN `Cb:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRC_ELD_BOUND) THEN
  SUBGOAL_THEN `(\x:real^2. vec 0:real^K) IN lspace B (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_0 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (\x. (k:num->real^2->real^K) n x - (kw:real^2->real^K) x) IN lspace B (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                     ((h:num->real^2->real^K) n x) ((k:num->real^2->real^K) n x)))
        integrable_on B /\
        (\x. lift(hmrm_eld S G (u x) (q x) ((w:real^2->real^K) x) ((kw:real^2->real^K) x)))
        integrable_on B /\
        (\x. lift(hmrm_eld S G (u x) (q x) (h n x - w x) (vec 0))) integrable_on B /\
        (\x. lift(hmrm_eld S G (u x) (q x) (vec 0) (k n x - kw x))) integrable_on B`
  ASSUME_TAC THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC HMRC_ELD_INTEGRABLE THENL
     [MAP_EVERY EXISTS_TAC [`d:real`; `C0:real`];
      MAP_EVERY EXISTS_TAC [`d:real`; `C0:real`];
      MAP_EVERY EXISTS_TAC [`d:real`; `&2 * C0`];
      MAP_EVERY EXISTS_TAC [`d:real`; `&0`]] THEN
    ASM_SIMP_TAC[ETA_AX; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; NORM_0; REAL_LE_REFL] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm((h:num->real^2->real^K) n x) <= C0 /\ norm((w:real^2->real^K) x) <= C0`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(NORM_ARITH `!a b:real^K. norm(a - b) <= norm a + norm b`) THEN
    DISCH_THEN(MP_TAC o SPECL [`(h:num->real^2->real^K) n x`; `(w:real^2->real^K) x`]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the difference splits *)
  SUBGOAL_THEN
   `!n. drop(integral B (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                                 ((h:num->real^2->real^K) n x) ((k:num->real^2->real^K) n x)))) -
        drop(integral B (\x. lift(hmrm_eld S G (u x) (q x) ((w:real^2->real^K) x)
                                 ((kw:real^2->real^K) x)))) =
        drop(integral B (\x. lift(hmrm_eld S G (u x) (q x) (h n x - w x) (vec 0)))) +
        drop(integral B (\x. lift(hmrm_eld S G (u x) (q x) (vec 0) (k n x - kw x))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "integrable_on")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_SIMP_TAC[GSYM DROP_SUB; GSYM DROP_ADD; GSYM INTEGRAL_SUB; GSYM INTEGRAL_ADD] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(u:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `(u:real^2->real^K) x`;
                   `(q:real^2->real^K) x`; `(h:num->real^2->real^K) n x`; `(w:real^2->real^K) x`;
                   `(k:num->real^2->real^K) n x`; `(kw:real^2->real^K) x`] HMRC_ELD_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HMRC_ELD_SPLIT THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REALLIM_NULL] THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [(* dominated convergence for the value part *)
    MP_TAC(ISPECL
     [`\n x. lift(hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                    ((h:num->real^2->real^K) n x - (w:real^2->real^K) x) (vec 0))`;
      `\x:real^2. vec 0:real^1`;
      `\x. lift(Ca * (&2 * C0) * norm((q:real^2->real^K) x) pow 2)`;
      `B:real^2->bool`; `Z:real^2->bool`] DOMINATED_CONVERGENCE_AE) THEN
    REWRITE_TAC[INTEGRAL_0] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
        ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE];
        MAP_EVERY X_GEN_TAC [`n:num`; `x:real^2`] THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Ca * norm((h:num->real^2->real^K) n x - (w:real^2->real^K) x) *
                    norm((q:real^2->real^K) x) pow 2 + Cb * norm(q x) * norm(vec 0:real^K)` THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_ADD_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        SUBGOAL_THEN `norm((h:num->real^2->real^K) n x) <= C0 /\ norm((w:real^2->real^K) x) <= C0`
        MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MP_TAC(NORM_ARITH `!a b:real^K. norm(a - b) <= norm a + norm b`) THEN
        DISCH_THEN(MP_TAC o SPECL [`(h:num->real^2->real^K) n x`; `(w:real^2->real^K) x`]) THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        SUBGOAL_THEN `((\n. norm((h:num->real^2->real^K) n z - (w:real^2->real^K) z)) ---> &0)
                      sequentially` ASSUME_TAC THENL
         [REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NUM; GSYM LIM_NULL_NORM] THEN
          SUBGOAL_THEN `vec 0:real^K = (w:real^2->real^K) z - w z` SUBST1_TAC THENL
           [REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
          MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
          ALL_TAC] THEN
        MATCH_MP_TAC LIM_NULL_COMPARISON THEN
        EXISTS_TAC `\n. Ca * norm((h:num->real^2->real^K) n z - (w:real^2->real^K) z) *
                        norm((q:real^2->real^K) z) pow 2` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `Ca * norm((h:num->real^2->real^K) n z - (w:real^2->real^K) z) *
                      norm((q:real^2->real^K) z) pow 2 + Cb * norm(q z) * norm(vec 0:real^K)` THEN
          CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL];
          SUBGOAL_THEN
           `((\n. Ca * norm((h:num->real^2->real^K) n z - (w:real^2->real^K) z) *
                  norm((q:real^2->real^K) z) pow 2) ---> &0) sequentially`
          MP_TAC THENL
           [MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC REALLIM_NULL_RMUL THEN
            ASM_REWRITE_TAC[];
            REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NUM]]]];
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP] THEN
      REWRITE_TAC[LIFT_NUM]];
    (* Hoelder for the derivative part *)
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC `\n. Cb * (lnorm B (&2) (q:real^2->real^K) *
                          lnorm B (&2) (\x. (k:num->real^2->real^K) n x - (kw:real^2->real^K) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[ABS_DROP] THEN
      SUBGOAL_THEN
       `(\x. lift(norm((q:real^2->real^K) x) *
                  norm((k:num->real^2->real^K) n x - (kw:real^2->real^K) x))) integrable_on B`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN MAP_EVERY EXISTS_TAC [`&2`; `&2`] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(integral B (\x. Cb % lift(norm((q:real^2->real^K) x) *
                     norm((k:num->real^2->real^K) n x - (kw:real^2->real^K) x))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Ca * norm(vec 0:real^K) * norm((q:real^2->real^K) x) pow 2 +
                    Cb * norm(q x) * norm((k:num->real^2->real^K) n x - (kw:real^2->real^K) x)` THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_LE_REFL];
        ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOELDER_INEQUALITY THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV];
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The weak Euler-Lagrange equation of a continuous weakly harmonic map      *)
(* holds for bounded continuous W_0^(1,2) tests (truncated approximation by  *)
(* vector test maps, a.e. convergent subsequence, dominated convergence and  *)
(* Hoelder).                                                                 *)
(* ========================================================================= *)

let HMRC_REALLIM_SUBSEQ = prove
 (`!(s:num->real) r l.
     (!m n. m < n ==> r m < r n) /\ (s ---> l) sequentially
     ==> ((\n. s (r n)) ---> l) sequentially`,
  REWRITE_TAC[TENDSTO_REAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o (s:num->real)`; `r:num->num`; `lift l`] LIM_SUBSEQUENCE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let HMRC_VTEST_PD_LSPACE = prove
 (`!(B:real^2->bool) (phi:real^2->real^K) i.
     open B /\ bounded B /\ wan_vtest B phi
     ==> (\x. partial_derivative i phi x) IN lspace B (&2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kp:real^2->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `phi:real^2->real^K`; `kp:real^2->bool`; `i:num`]
    WAN_VTEST_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LSPACE_BOUNDED_MEASURABLE_SIMPLE THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ASM_SIMP_TAC[MEASURABLE_OPEN];
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `vec 0 INSERT IMAGE (\x. partial_derivative i (phi:real^2->real^K) x) kp` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BOUNDED_INSERT] THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INSERT; IN_IMAGE] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^2) IN kp` THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[]]]]);;

let HMRC_FD_APPLY_MEAS = prove
 (`!(B:real^2->bool) (Tr:real^K->real^K) (g:real^2->real^K) (v:real^2->real^K).
     open B /\ smooth_map_on (:real^K) Tr /\ g continuous_on B /\ v measurable_on B
     ==> (\x. frechet_derivative Tr (at (g x)) (v x)) measurable_on B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `\x. frechet_derivative (Tr:real^K->real^K) (at ((g:real^2->real^K) x))`;
                 `v:real^2->real^K`] HMC_MEAS_LINEAR_APPLY) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. frechet_derivative (Tr:real^K->real^K) (at ((g:real^2->real^K) x)) (basis k)) =
      (\y. frechet_derivative Tr (at y) (basis k)) o g`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[HMRC_FD_CONT; SUBSET_UNIV]]);;

(* L^2 convergence of the partials of the truncated tests. *)

let HMRC_PD_TRUNC_CONV = prove
 (`!(B:real^2->bool) (Tr:real^K->real^K) L R (f:num->real^2->real^K) (w:real^2->real^K) Z i.
     open B /\ bounded B /\ smooth_map_on (:real^K) Tr /\ &0 <= L /\
     (!y v. norm(frechet_derivative Tr (at y) v) <= L * norm v) /\
     (!y. norm y < R ==> frechet_derivative Tr (at y) = (\v. v)) /\
     (!n. wan_vtest B (f n)) /\ wan_w12 B w /\ 1 <= i /\ i <= 2 /\
     ((\n. wan_dir B (\x. f n x - w x)) ---> &0) sequentially /\
     negligible Z /\ (!x. x IN B DIFF Z ==> ((\n. f n x) --> w x) sequentially) /\
     (!x. x IN B ==> norm(w x) < R)
     ==> ((\n. lnorm B (&2) (\x. partial_derivative i (Tr o f n) x - wan_wd B i w x)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. smooth_map_on (:real^2) ((f:num->real^2->real^K) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_vtest]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ((f:num->real^2->real^K) n) continuous_on B` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_wd B i (w:real^2->real^K) IN lspace B (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (\x. partial_derivative i ((f:num->real^2->real^K) n) x) IN lspace B (&2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[HMRC_VTEST_PD_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. partial_derivative i ((f:num->real^2->real^K) n) x - wan_wd B i (w:real^2->real^K) x)
        IN lspace B (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the dominated part *)
  MP_TAC(ISPECL [`B:real^2->bool`; `Tr:real^K->real^K`; `L:real`; `R:real`;
                 `f:num->real^2->real^K`; `w:real^2->real^K`; `wan_wd B i (w:real^2->real^K)`;
                 `Z:real^2->bool`] HMRC_L2_DT_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the chain rule part *)
  SUBGOAL_THEN
   `!n. (\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
               (partial_derivative i (f n) x - wan_wd B i (w:real^2->real^K) x))
        IN lspace B (&2) /\
        lnorm B (&2) (\x. frechet_derivative Tr (at (f n x))
                            (partial_derivative i (f n) x - wan_wd B i w x))
        <= L * lnorm B (&2) (\x. partial_derivative i (f n) x - wan_wd B i w x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
             (partial_derivative i (f n) x - wan_wd B i (w:real^2->real^K) x))
      measurable_on B`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HMRC_FD_APPLY_MEAS THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MP_TAC(SPEC `n:num` (ASSUME
       `!n. (\x. partial_derivative i ((f:num->real^2->real^K) n) x -
                 wan_wd B i (w:real^2->real^K) x) IN lspace B (&2)`)) THEN
      REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. L % (partial_derivative i ((f:num->real^2->real^K) n) x -
                wan_wd B i (w:real^2->real^K) x)) IN lspace B (&2)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[LSPACE_CMUL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
             (partial_derivative i (f n) x - wan_wd B i (w:real^2->real^K) x))
      IN lspace B (&2)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`B:real^2->bool`; `&2`;
                     `\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
                            (partial_derivative i (f n) x - wan_wd B i (w:real^2->real^K) x)`;
                     `\x. L % (partial_derivative i ((f:num->real^2->real^K) n) x -
                               wan_wd B i (w:real^2->real^K) x)`]
        LSPACE_BOUNDED_MEASURABLE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[NORM_MUL; real_abs];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm B (&2) (\x. L % (partial_derivative i ((f:num->real^2->real^K) n) x -
                                       wan_wd B i (w:real^2->real^K) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^2->bool` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[NORM_MUL; real_abs];
      ASM_SIMP_TAC[LNORM_MUL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      ASM_SIMP_TAC[real_abs; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the Dirichlet part *)
  SUBGOAL_THEN
   `((\n. lnorm B (&2) (\x. partial_derivative i ((f:num->real^2->real^K) n) x -
                           wan_wd B i (w:real^2->real^K) x)) ---> &0) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMRC_SQ_NULL THEN
    EXISTS_TAC `\n. wan_dir B (\x. (f:num->real^2->real^K) n x - (w:real^2->real^K) x)` THEN
    ASM_REWRITE_TAC[WAN_LNORM2_POS] THEN X_GEN_TAC `n:num` THEN
    ASM_SIMP_TAC[WAN_LNORM2_SQ] THEN MATCH_MP_TAC WAN_WD_DIFF_SQ_LE_DIR THEN
    ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  (* combination *)
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. L * lnorm B (&2) (\x. partial_derivative i ((f:num->real^2->real^K) n) x -
                             wan_wd B i (w:real^2->real^K) x) +
        lnorm B (&2) (\x. frechet_derivative (Tr:real^K->real^K) (at (f n x)) (wan_wd B i w x) -
                          wan_wd B i w x)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_ADD_RID] THEN
    MATCH_MP_TAC REALLIM_ADD THEN ASM_SIMP_TAC[REALLIM_NULL_LMUL]] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. partial_derivative i ((Tr:real^K->real^K) o (f:num->real^2->real^K) n) x -
         wan_wd B i (w:real^2->real^K) x) =
    (\x. frechet_derivative Tr (at (f n x)) (partial_derivative i (f n) x - wan_wd B i w x) +
         (frechet_derivative Tr (at (f n x)) (wan_wd B i w x) - wan_wd B i w x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    SUBGOAL_THEN `(f:num->real^2->real^K) n differentiable at x /\
                  (Tr:real^K->real^K) differentiable at (f n x)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `(:real^2)`; EXISTS_TAC `(:real^K)`] THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PARTIAL_DERIVATIVE_CHAIN] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
           (wan_wd B i (w:real^2->real^K) x) - wan_wd B i w x) IN lspace B (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lnorm")) (concl th) &&
    can (find_term (fun t -> t = `L:real`)) (concl th))) THEN
  MP_TAC(ISPECL
   [`B:real^2->bool`; `&2`;
    `\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
           (partial_derivative i (f n) x - wan_wd B i (w:real^2->real^K) x)`;
    `\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
           (wan_wd B i (w:real^2->real^K) x) - wan_wd B i w x`] LNORM_TRIANGLE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`B:real^2->bool`;
    `\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
           (partial_derivative i (f n) x - wan_wd B i (w:real^2->real^K) x) +
         (frechet_derivative Tr (at (f n x)) (wan_wd B i w x) - wan_wd B i w x)`]
    WAN_LNORM2_POS) THEN
  UNDISCH_TAC
   `lnorm B (&2) (\x. frechet_derivative (Tr:real^K->real^K) (at ((f:num->real^2->real^K) n x))
                        (partial_derivative i (f n) x - wan_wd B i (w:real^2->real^K) x))
    <= L * lnorm B (&2) (\x. partial_derivative i (f n) x - wan_wd B i w x)` THEN
  REAL_ARITH_TAC);;

(* The Euler-Lagrange identity for bounded continuous W_0^(1,2) tests. *)

let HMRC_EL_W120 = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) (B:real^2->bool) (w:real^2->real^K) M.
     cm_target S G d /\ cm_wharmonic S G s u /\ open B /\ bounded B /\ closure B SUBSET s /\
     wan_w120 B w /\ w continuous_on B /\ (!x. x IN B ==> norm(w x) <= M)
     ==> sum(1..2) (\i. drop(integral B
           (\x. lift(hmrm_eld S G (u x) (wan_wd B i u x) (w x) (wan_wd B i w x))))) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `B SUBSET (s:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 B (u:real^2->real^K) /\ (u:real^2->real^K) continuous_on B /\
                (!x. x IN B ==> u x IN S)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `R = abs M + &1` THEN
  SUBGOAL_THEN `&0 < R /\ !x. x IN B ==> norm((w:real^2->real^K) x) < R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "R" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm((w:real^2->real^K) x) <= M` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "R" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `R:real` HMRC_TRUNC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Tr:real^K->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_w120] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_w120")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:num->real^2->real^K` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(!n. (f:num->real^2->real^K) n IN lspace B (&2)) /\
                (w:real^2->real^K) IN lspace B (&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_W12_IMP_LSPACE THEN
      MP_TAC(ISPECL [`B:real^2->bool`; `(f:num->real^2->real^K) n`] WAN_VTEST_W12) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `f:num->real^2->real^K`; `w:real^2->real^K`]
    WAN_L2_AE_SUBSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `Z:real^2->bool` STRIP_ASSUME_TAC))) THEN
  (* the truncated tests *)
  SUBGOAL_THEN
   `!n. wan_vtest B ((Tr:real^K->real^K) o (f:num->real^2->real^K) ((r:num->num) n)) /\
        (Tr o f (r n)) continuous_on B /\
        (!x. norm((Tr o f (r n)) x) <= &2 * R)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `wan_vtest B ((f:num->real^2->real^K) ((r:num->num) n))` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[wan_vtest] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kc:real^2->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `smooth_map_on (:real^2) ((Tr:real^K->real^K) o (f:num->real^2->real^K) ((r:num->num) n))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `kc:real^2->bool` THEN ASM_SIMP_TAC[o_THM];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]];
    ALL_TAC] THEN
  (* the identity along the tests *)
  SUBGOAL_THEN
   `!n. sum(1..2) (\i. drop(integral B (\x. lift(hmrm_eld S G ((u:real^2->real^K) x)
          (wan_wd B i u x) (((Tr:real^K->real^K) o (f:num->real^2->real^K) ((r:num->num) n)) x)
          (partial_derivative i (Tr o f (r n)) x))))) = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HMRM_WHARMONIC_EL THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `s:real^2->bool`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the limits *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> ((\n. drop(integral B (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd B i u x)
               (((Tr:real^K->real^K) o (f:num->real^2->real^K) ((r:num->num) n)) x)
               (partial_derivative i (Tr o f (r n)) x))))) --->
             drop(integral B (\x. lift(hmrm_eld S G (u x) (wan_wd B i u x) ((w:real^2->real^K) x)
               (wan_wd B i w x))))) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B:real^2->bool`; `Tr:real^K->real^K`; `L:real`; `R:real`;
                   `\n. (f:num->real^2->real^K) ((r:num->num) n)`; `w:real^2->real^K`; `Z:real^2->bool`;
                   `i:num`] HMRC_PD_TRUNC_CONV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\m. wan_dir B (\x. (f:num->real^2->real^K) m x - (w:real^2->real^K) x)`;
                     `r:num->num`; `&0`] HMRC_REALLIM_SUBSEQ) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[])] THEN
    MATCH_MP_TAC HMRC_ELD_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `&2 * R`; `Z:real^2->bool`] THEN
    REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm((w:real^2->real^K) x) < R` MP_TAC THENL
       [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC;
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`B:real^2->bool`;
                     `(Tr:real^K->real^K) o (f:num->real^2->real^K) ((r:num->num) n)`; `i:num`]
        HMRC_VTEST_PD_LSPACE) THEN
      ASM_REWRITE_TAC[ETA_AX]] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(Tr:real^K->real^K)((w:real^2->real^K) x) = w x` (fun th ->
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM th]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`Tr:real^K->real^K`; `sequentially`;
                   `\n. (f:num->real^2->real^K) ((r:num->num) n) x`; `(w:real^2->real^K) x`]
      LIM_CONTINUOUS_FUNCTION) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* conclusion *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\n:num. sum(1..2) (\i. drop(integral B (\x. lift(hmrm_eld S G ((u:real^2->real^K) x)
          (wan_wd B i u x) (((Tr:real^K->real^K) o (f:num->real^2->real^K) ((r:num->num) n)) x)
          (partial_derivative i (Tr o f (r n)) x)))))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_2] THEN MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[REALLIM_CONST]]);;

(* ========================================================================= *)
(* The harmonic replacement.  A vector maximum principle; orthogonality of a *)
(* harmonic map to W_0^(1,2) after a constant matrix; the tangential form of *)
(* the Euler-Lagrange identity.                                              *)
(* ========================================================================= *)

let HMRC_HARM_MAX = prove
 (`!(a:real^2) r (h:real^2->real^K) (c:real^K) M.
     &0 < r /\ h continuous_on cball(a,r) /\ smooth_map_on (ball(a,r)) h /\
     (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
            ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
     (!y. y IN sphere(a,r) ==> norm(h y - c) <= M)
     ==> !x. x IN cball(a,r) ==> norm(h x - c) <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(h:real^2->real^K) x = c` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a + r % basis 1:real^2` o check (fun th ->
      can (find_term (fun t -> t = `M:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_SPHERE; NORM_ARITH `dist(a:real^2,a + y) = norm y`; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
      MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  ABBREV_TAC `e = inv(norm((h:real^2->real^K) x - c)) % (h x - c)` THEN
  SUBGOAL_THEN `&0 < norm((h:real^2->real^K) x - c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(e:real^K) = &1 /\ e dot ((h:real^2->real^K) x - c) = norm(h x - c)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[NORM_MUL; DOT_LMUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    REWRITE_TAC[GSYM NORM_POW_2] THEN UNDISCH_TAC `&0 < norm((h:real^2->real^K) x - c)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real^2`; `r:real`; `\y. (e:real^K) dot (h:real^2->real^K) y`;
                `(e:real^K) dot c + M`]
    (REWRITE_RULE[WAN_MAX_PRINCIPLE_DISC_STATEMENT] WAN_MAX_PRINCIPLE_DISC)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      MP_TAC(ISPECL [`ball(a:real^2,r)`; `(\y. e):real^2->real^K`; `h:real^2->real^K`]
        SMOOTH_MAP_ON_DOT_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC WANL_LLAP_DOT_HARMONIC THEN
      EXISTS_TAC `ball(a:real^2,r)` THEN ASM_SIMP_TAC[OPEN_BALL];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm((h:real^2->real^K) y - c) <= M` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`e:real^K`; `(h:real^2->real^K) y - c`] NORM_CAUCHY_SCHWARZ) THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; DOT_RSUB] THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:real^K) dot ((h:real^2->real^K) x - c) = norm(h x - c)` THEN
    REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC]);;

(* A constant matrix applied to a W^(1,2) map. *)

let HMRC_MATRIX_W12 = prove
 (`!(B:real^2->bool) (h:real^2->real^K) (G0:real^K^K).
     open B /\ bounded B /\ wan_w12 B h
     ==> wan_w12 B (\x. G0 ** h x) /\
         !i. 1 <= i /\ i <= 2
             ==> negligible {x | x IN B /\
                                 ~(wan_wd B i (\x. G0 ** h x) x = G0 ** wan_wd B i h x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. frechet_derivative (\y:real^K. (G0:real^K^K) ** y) (at y) = (\y. G0 ** y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `h:real^2->real^K`; `\y:real^K. (G0:real^K^K) ** y`]
    (REWRITE_RULE[WAN_CHAIN_W12_STATEMENT]
      (ISPECL [`(:2)`; `(:K)`; `(:K)`] WAN_CHAIN_W12))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^K)`; `\y:real^K. y`; `\y:real^K. (G0:real^K^K) ** y`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      REWRITE_TAC[OPEN_UNIV; MATRIX_VECTOR_MUL_LINEAR; SMOOTH_MAP_ON_ID; o_DEF] THEN
      SIMP_TAC[smooth_map_on];
      EXISTS_TAC `onorm(\y:real^K. (G0:real^K^K) ** y)` THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `i:num`; `\x. (G0:real^K^K) ** (h:real^2->real^K) x`;
                 `\x. (G0:real^K^K) ** wan_wd B i (h:real^2->real^K) x`] WAN_WD_UNIQUE) THEN
  ASM_SIMP_TAC[DIMINDEX_2]);;

(* Orthogonality of a harmonic map to W_0^(1,2), after a constant matrix. *)

let HMRC_HARM_ORTHO = prove
 (`!(B:real^2->bool) (h:real^2->real^K) (G0:real^K^K) w.
     open B /\ bounded B /\ smooth_map_on B h /\
     (!x j. x IN B /\ 1 <= j /\ j <= dimindex(:K)
            ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
     wan_w12 B h /\ wan_w120 B w
     ==> sum(1..2) (\i. drop(integral B
           (\x. lift((G0 ** wan_wd B i h x) dot wan_wd B i w x)))) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `h:real^2->real^K`; `G0:real^K^K`] HMRC_MATRIX_W12) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `\x. (G0:real^K^K) ** (h:real^2->real^K) x`;
                 `w:real^2->real^K`] WANL_DD_ORTHO) THEN
  REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`B:real^2->bool`; `h:real^2->real^K`; `\y:real^K. (G0:real^K^K) ** y`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `j:num`] THEN STRIP_TAC THEN
      SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; ASSUME `1 <= j`; ASSUME `j <= dimindex(:K)`] THEN
      MATCH_MP_TAC WANL_LLAP_DOT_HARMONIC THEN EXISTS_TAC `B:real^2->bool` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a = &0 ==> b = &0`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN B /\ ~(wan_wd B i (\x. (G0:real^K^K) ** (h:real^2->real^K) x) x =
                              G0 ** wan_wd B i h x)}` THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The density with zero test value, at a tangent q. *)

let HMRC_ELD_TANGENT = prove
 (`!S (G:real^K->real^K^K) d p q k.
     cm_target S G d /\ p IN S /\ jacobian (closest_point S) (at p) ** q = q
     ==> hmrm_eld S G p q (vec 0) k = &2 * (k dot (G p ** q))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point (S:real^K->bool)) (at y))) differentiable (at (p:real^K)) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) differentiable (at p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[hmrm_eld; MATRIX_VECTOR_MUL_RZERO] THEN
  ASM_SIMP_TAC[HMC_MDERIV_ZERO; MATRIX_VECTOR_MUL_LZERO; VECTOR_ADD_LID; DOT_LZERO;
               DOT_RZERO; REAL_ADD_RID] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`]
    HMR_TP_TANGENT) THEN
  ASM_REWRITE_TAC[hmr_tp]);;

(* The tangential form of the Euler-Lagrange identity. *)

let HMRC_EL_TANGENT = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?Ca. &0 <= Ca /\
              !s (u:real^2->real^K) (B:real^2->bool) (w:real^2->real^K) M.
                 cm_wharmonic S G s u /\ open B /\ bounded B /\ closure B SUBSET s /\
                 wan_w120 B w /\ w continuous_on B /\ (!x. x IN B ==> norm(w x) <= M)
                 ==> abs(sum(1..2) (\i. drop(integral B
                       (\x. lift(wan_wd B i w x dot (G(u x) ** wan_wd B i u x))))))
                     <= Ca * M * wan_dir B u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca1:real` (X_CHOOSE_THEN `Cb1:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRC_ELD_BOUND) THEN
  EXISTS_TAC `Ca1 / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `B:real^2->bool`;
                       `w:real^2->real^K`; `M:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `B SUBSET (s:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 B (u:real^2->real^K) /\ (u:real^2->real^K) continuous_on B /\
                (!x. x IN B ==> u x IN S) /\ wan_w12 B (w:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[];
      ASM_MESON_TAC[wan_w120]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^2. vec 0:real^K) continuous_on B` ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_CONST]; ALL_TAC] THEN
  (* per index *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd B i u x)
                                   ((w:real^2->real^K) x) (vec 0))) integrable_on B /\
            (\x. lift(wan_wd B i w x dot (G(u x) ** wan_wd B i u x))) integrable_on B /\
            drop(integral B (\x. lift(hmrm_eld S G (u x) (wan_wd B i u x) (w x)
                                                  (wan_wd B i w x)))) =
            drop(integral B (\x. lift(hmrm_eld S G (u x) (wan_wd B i u x) (w x) (vec 0)))) +
            &2 * drop(integral B (\x. lift(wan_wd B i w x dot (G(u x) ** wan_wd B i u x)))) /\
            abs(drop(integral B (\x. lift(hmrm_eld S G (u x) (wan_wd B i u x) (w x) (vec 0)))))
            <= Ca1 * M * drop(integral B (\x. lift(norm(wan_wd B i u x) pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `wan_wd B i (u:real^2->real^K) IN lspace B (&2) /\
                  wan_wd B i (w:real^2->real^K) IN lspace B (&2) /\
                  (\x:real^2. vec 0:real^K) IN lspace B (&2)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2] THEN MATCH_MP_TAC LSPACE_0 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    (* the three densities are integrable *)
    SUBGOAL_THEN
     `(\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd B i u x) ((w:real^2->real^K) x)
                         (wan_wd B i w x))) integrable_on B /\
      (\x. lift(hmrm_eld S G (u x) (wan_wd B i u x) (w x) (vec 0))) integrable_on B /\
      (\x. lift(hmrm_eld S G (u x) (wan_wd B i u x) (vec 0) (wan_wd B i w x))) integrable_on B`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC HMRC_ELD_INTEGRABLE THENL
       [MAP_EVERY EXISTS_TAC [`d:real`; `M:real`];
        MAP_EVERY EXISTS_TAC [`d:real`; `M:real`];
        MAP_EVERY EXISTS_TAC [`d:real`; `&0`]] THEN
      ASM_REWRITE_TAC[ETA_AX; NORM_0; REAL_LE_REFL];
      ALL_TAC] THEN
    (* the tangent null set *)
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `B:real^2->bool`;
                   `u:real^2->real^K`; `i:num`] HMRM_WD_TANGENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x. x IN B DIFF {x | x IN B /\
                          ~(jacobian (closest_point S) (at ((u:real^2->real^K) x)) **
                            wan_wd B i u x = wan_wd B i u x)}
          ==> lift(wan_wd B i (w:real^2->real^K) x dot (G(u x) ** wan_wd B i u x)) =
              inv(&2) % lift(hmrm_eld S G (u x) (wan_wd B i u x) (vec 0) (wan_wd B i w x))`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `(u:real^2->real^K) x`;
                     `wan_wd B i (u:real^2->real^K) x`; `wan_wd B i (w:real^2->real^K) x`]
        HMRC_ELD_TANGENT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(wan_wd B i (w:real^2->real^K) x dot (G((u:real^2->real^K) x) ** wan_wd B i u x)))
      integrable_on B`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `\x. inv(&2) % lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd B i u x)
                                              (vec 0) (wan_wd B i (w:real^2->real^K) x))` THEN
      EXISTS_TAC `{x | x IN B /\
                       ~(jacobian (closest_point S) (at ((u:real^2->real^K) x)) **
                         wan_wd B i u x = wan_wd B i u x)}` THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; ETA_AX];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `drop(integral B (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd B i u x)
                                              ((w:real^2->real^K) x) (vec 0)) +
                                       lift(hmrm_eld S G (u x) (wan_wd B i u x) (vec 0)
                                              (wan_wd B i w x))))` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM LIFT_ADD] THEN AP_TERM_TAC THEN MATCH_MP_TAC HMRC_ELD_SPLIT THEN
        EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[INTEGRAL_ADD; DROP_ADD] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `drop(integral B (\x. &2 % (inv(&2) %
                    lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd B i u x) (vec 0)
                                      (wan_wd B i (w:real^2->real^K) x)))))` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN
        DISCH_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[VECTOR_MUL_LID];
        ALL_TAC] THEN
      ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_CMUL] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `drop(integral B (\x. inv(&2) %
                    lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd B i u x) (vec 0)
                                      (wan_wd B i (w:real^2->real^K) x))))` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
        EXISTS_TAC `{x | x IN B /\
                         ~(jacobian (closest_point S) (at ((u:real^2->real^K) x)) **
                           wan_wd B i u x = wan_wd B i u x)}` THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]];
      ALL_TAC] THEN
    REWRITE_TAC[ABS_DROP] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral B (\x. (Ca1 * M) % lift(norm(wan_wd B i (u:real^2->real^K) x) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
        ASM_REWRITE_TAC[ETA_AX];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Ca1 * norm((w:real^2->real^K) x) * norm(wan_wd B i (u:real^2->real^K) x) pow 2 +
                  Cb1 * norm(wan_wd B i u x) * norm(vec 0:real^K)` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_ADD_RID; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_POW_2];
      SUBGOAL_THEN `(\x. lift(norm(wan_wd B i (u:real^2->real^K) x) pow 2)) integrable_on B`
      ASSUME_TAC THENL
       [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
      ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the identity *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `B:real^2->bool`; `w:real^2->real^K`; `M:real`]
    HMRC_EL_W120) THEN
  ASM_REWRITE_TAC[SUM_2; wan_dir; DIMINDEX_2] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The comparison estimate.  If u is continuous weakly harmonic, h its       *)
(* harmonic replacement on ball(a,r) and |u - u(a)| <= e0 on the closed      *)
(* disc, then                                                                *)
(*   int |D(u - h)|^2 <= C (e0^2 + e0) int |Du|^2.                          *)
(* ========================================================================= *)

let HMRC_L2_DOT_INT = prove
 (`!(B:real^2->bool) (A:real^2->real^K^K) (p:real^2->real^K) q c.
     open B /\ ((vectorize:real^K^K->real^(K,K)finite_prod) o A) continuous_on B /\ &0 <= c /\
     (!x v. x IN B ==> norm(A x ** v) <= c * norm v) /\
     p IN lspace B (&2) /\ q IN lspace B (&2)
     ==> (\x. lift(p x dot (A x ** q x))) integrable_on B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. c % lift(norm((p:real^2->real^K) x) * norm((q:real^2->real^K) x))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HMC_MEAS_DOT THEN CONJ_TAC THENL
     [UNDISCH_TAC `(p:real^2->real^K) IN lspace B (&2)` THEN
      REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`B:real^2->bool`;
                     `(vectorize:real^K^K->real^(K,K)finite_prod) o (A:real^2->real^K^K)`;
                     `q:real^2->real^K`] HMC_MEAS_MATMUL) THEN
      REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
        UNDISCH_TAC `(q:real^2->real^K) IN lspace B (&2)` THEN
        REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[]]];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
    MAP_EVERY EXISTS_TAC [`&2`; `&2`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((p:real^2->real^K) x) * norm((A:real^2->real^K^K) x ** (q:real^2->real^K) x)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((p:real^2->real^K) x) * (c * norm((q:real^2->real^K) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[NORM_POS_LE];
      REWRITE_TAC[REAL_LE_REFL; REAL_MUL_AC]]]);;

let HMRC_AMGM = prove
 (`!x y t. &0 < t ==> x * y <= (t / &2) * x pow 2 + y pow 2 / (&2 * t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (t * x - y) pow 2 / (&2 * t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(t * x - y) pow 2 / (&2 * t) = (t / &2) * x pow 2 + y pow 2 / (&2 * t) - x * y`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;

let HMRC_COMPARE_ARITH = prove
 (`!lam Ca C3 e0 Dk1 Dk2 Dq1 Dq2 Y1 Y2 Z1 Z2 O1 O2.
     &0 < lam /\ &0 <= Ca /\ &0 <= e0 /\ &0 <= Dq1 /\ &0 <= Dq2 /\
     lam * Dk1 <= Y1 - O1 /\ lam * Dk2 <= Y2 - O2 /\
     &2 * lam * (Y1 - Z1) <= lam pow 2 * Dk1 + (C3 * e0) pow 2 * Dq1 /\
     &2 * lam * (Y2 - Z2) <= lam pow 2 * Dk2 + (C3 * e0) pow 2 * Dq2 /\
     O1 + O2 = &0 /\ abs(Z1 + Z2) <= Ca * (&2 * e0) * (Dq1 + Dq2)
     ==> Dk1 + Dk2 <= (C3 pow 2 / lam pow 2 + &4 * Ca / lam) * (e0 pow 2 + e0) * (Dq1 + Dq2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lam * (lam * Dk1) <= lam * (Y1 - O1) /\ lam * (lam * Dk2) <= lam * (Y2 - O2) /\
                lam * abs(Z1 + Z2) <= lam * (Ca * (&2 * e0) * (Dq1 + Dq2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam pow 2 * (Dk1 + Dk2) <=
                (&4 * lam * Ca * e0 + C3 pow 2 * e0 pow 2) * (Dq1 + Dq2)`
  ASSUME_TAC THENL
   [MP_TAC(REAL_ARITH `abs(Z1 + Z2) >= Z1 + Z2`) THEN
    SUBGOAL_THEN `lam * (Z1 + Z2) <= lam * abs(Z1 + Z2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lam * (O1 + O2) = &0` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_POW_2; REAL_POW_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&4 * lam * Ca * e0 + C3 pow 2 * e0 pow 2) * (Dq1 + Dq2)) / lam pow 2` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `((C3 pow 2 / lam pow 2 + &4 * Ca / lam) * (e0 pow 2 + e0) * (Dq1 + Dq2)) *
                lam pow 2 =
                (C3 pow 2 + &4 * Ca * lam) * (e0 pow 2 + e0) * (Dq1 + Dq2)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C3 pow 2 * e0 * (Dq1 + Dq2) /\ &0 <= Ca * lam * e0 pow 2 * (Dq1 + Dq2)`
  MP_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_LE_ADD];
    REAL_ARITH_TAC]);;

let HMRC_COMPARE = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?C. &0 <= C /\
             !s (u:real^2->real^K) a r (h:real^2->real^K) e0.
                cm_wharmonic S G s u /\ &0 < r /\ cball(a,r) SUBSET s /\
                h continuous_on cball(a,r) /\ smooth_map_on (ball(a,r)) h /\
                (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
                       ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
                wan_w12 (ball(a,r)) h /\ (!x. x IN sphere(a,r) ==> h x = u x) /\
                (!x. x IN cball(a,r) ==> norm(u x - u a) <= e0)
                ==> wan_dir (ball(a,r)) (\x. u x - h x) <=
                    C * (e0 pow 2 + e0) * wan_dir (ball(a,r)) u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam1:real` (X_CHOOSE_THEN `CJ:real`
    (X_CHOOSE_THEN `CG:real` (X_CHOOSE_THEN `C2:real` (X_CHOOSE_THEN `C3:real`
    (X_CHOOSE_THEN `C4:real` STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca:real` STRIP_ASSUME_TAC o MATCH_MP HMRC_EL_TANGENT) THEN
  EXISTS_TAC `C3 pow 2 / lam pow 2 + &4 * Ca / lam` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `a:real^2`; `r:real`;
                       `h:real^2->real^K`; `e0:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `closure(ball(a:real^2,r)) SUBSET (s:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (u:real^2->real^K) /\ (u:real^2->real^K) continuous_on cball(a,r) /\
                (!x. x IN cball(a,r) ==> u x IN S) /\ &0 <= e0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((u:real^2->real^K) a - u a)` THEN
      REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the difference w = u - h *)
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (\x. (u:real^2->real^K) x - h x) /\
                wan_w120 (ball(a,r)) (\x. (u:real^2->real^K) x - h x) /\
                (\x. (u:real^2->real^K) x - h x) continuous_on ball(a,r) /\
                (!x. x IN ball(a,r) ==> norm((u:real^2->real^K) x - h x) <= &2 * e0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `wan_w12 (ball(a,r)) (\x. (u:real^2->real^K) x - h x)` ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. (u:real^2->real^K) x - h x) continuous_on cball(a,r)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[WAN_W120_CONT_STATEMENT]
        (ISPECL [`(:2)`; `(:K)`] WAN_W120_CONT)) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[VECTOR_SUB_REFL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`a:real^2`; `r:real`; `h:real^2->real^K`; `(u:real^2->real^K) a`; `e0:real`]
        HMRC_HARM_MAX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(h:real^2->real^K) y = u y` SUBST1_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC(ISPECL [`a:real^2`; `r:real`] SPHERE_SUBSET_CBALL) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`a:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `norm((u:real^2->real^K) x - u a) <= e0` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC(ISPECL [`a:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  (* the constant matrix *)
  ABBREV_TAC `G0 = (G:real^K->real^K^K)((u:real^2->real^K) a)` THEN
  SUBGOAL_THEN `(u:real^2->real^K) a IN S` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. norm((G0:real^K^K) ** v) <= Lam1 * norm v` ASSUME_TAC THENL
   [EXPAND_TAC "G0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o (\x:real^2. G0:real^K^K))
                continuous_on ball(a,r) /\
                ((vectorize:real^K^K->real^(K,K)finite_prod) o
                 (\x. (G:real^K->real^K^K)((u:real^2->real^K) x))) continuous_on ball(a,r)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; CONTINUOUS_ON_CONST];
      SUBGOAL_THEN
       `((vectorize:real^K^K->real^(K,K)finite_prod) o
         (\x. (G:real^K->real^K^K)((u:real^2->real^K) x))) =
        ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o u`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
        ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!xi. lam * norm xi pow 2 <= xi dot ((G0:real^K^K) ** xi)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "G0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* per index *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> lam * drop(integral (ball(a,r))
                (\x. lift(norm(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x) pow 2)))
            <= drop(integral (ball(a,r))
                 (\x. lift(wan_wd (ball(a,r)) i (\x. u x - h x) x dot
                           ((G0:real^K^K) ** wan_wd (ball(a,r)) i u x)))) -
               drop(integral (ball(a,r))
                 (\x. lift((G0 ** wan_wd (ball(a,r)) i h x) dot
                           wan_wd (ball(a,r)) i (\x. u x - h x) x))) /\
            &2 * lam *
            (drop(integral (ball(a,r))
               (\x. lift(wan_wd (ball(a,r)) i (\x. u x - h x) x dot
                         (G0 ** wan_wd (ball(a,r)) i u x)))) -
             drop(integral (ball(a,r))
               (\x. lift(wan_wd (ball(a,r)) i (\x. u x - h x) x dot
                         (G(u x) ** wan_wd (ball(a,r)) i u x)))))
            <= lam pow 2 * drop(integral (ball(a,r))
                 (\x. lift(norm(wan_wd (ball(a,r)) i (\x. u x - h x) x) pow 2))) +
               (C3 * e0) pow 2 *
               drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) i u x) pow 2))) /\
            &0 <= drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) i u x) pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `wan_wd (ball(a,r)) i (u:real^2->real^K) IN lspace (ball(a,r)) (&2) /\
      wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) IN lspace (ball(a,r)) (&2) /\
      wan_wd (ball(a,r)) i (h:real^2->real^K) IN lspace (ball(a,r)) (&2)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2]; ALL_TAC] THEN
    (* integrability of the dot densities *)
    SUBGOAL_THEN
     `(\x. lift(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x dot
                ((G0:real^K^K) ** wan_wd (ball(a,r)) i (\x. u x - h x) x))) integrable_on ball(a,r) /\
      (\x. lift(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x dot
                ((G0:real^K^K) ** wan_wd (ball(a,r)) i u x))) integrable_on ball(a,r) /\
      (\x. lift(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x dot
                ((G:real^K->real^K^K)(u x) ** wan_wd (ball(a,r)) i u x))) integrable_on ball(a,r) /\
      (\x. lift(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x dot
                ((G0:real^K^K) ** wan_wd (ball(a,r)) i h x))) integrable_on ball(a,r)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC HMRC_L2_DOT_INT THEN EXISTS_TAC `Lam1:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL; ETA_AX] THEN
      X_GEN_TAC `x:real^2` THEN X_GEN_TAC `v:real^K` THEN DISCH_TAC THEN
      TRY(FIRST_X_ASSUM MATCH_ACCEPT_TAC) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t -> t = `Lam1:real`)) (concl th) &&
        can (find_term (fun t -> t = `S:real^K->bool`)) (concl th))) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`a:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x) pow 2))
      integrable_on ball(a,r) /\
      (\x. lift(norm(wan_wd (ball(a,r)) i (u:real^2->real^K) x) pow 2)) integrable_on ball(a,r)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    (* the weak gradient of h is that of u minus that of u - h, a.e. *)
    MP_TAC(SPEC `i:num` (CONJUNCT2 (MATCH_MP WAN_W12_SUB_WD
      (CONJ (ASSUME `wan_w12 (ball(a:real^2,r)) (u:real^2->real^K)`)
            (ASSUME `wan_w12 (ball(a:real^2,r)) (h:real^2->real^K)`))))) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `i:num`; `\x. (u:real^2->real^K) x - h x`;
                   `\x. wan_wd (ball(a,r)) i (u:real^2->real^K) x - wan_wd (ball(a,r)) i h x`]
      WAN_WD_UNIQUE) THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [(* the coercivity part *)
      SUBGOAL_THEN
       `drop(integral (ball(a,r))
          (\x. lift(((G0:real^K^K) ** wan_wd (ball(a,r)) i (h:real^2->real^K) x) dot
                    wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x))) =
        drop(integral (ball(a,r))
          (\x. lift(wan_wd (ball(a,r)) i (\x. u x - h x) x dot (G0 ** wan_wd (ball(a,r)) i u x)))) -
        drop(integral (ball(a,r))
          (\x. lift(wan_wd (ball(a,r)) i (\x. u x - h x) x dot
                    (G0 ** wan_wd (ball(a,r)) i (\x. u x - h x) x))))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM DROP_SUB; GSYM INTEGRAL_SUB] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC INTEGRAL_SPIKE THEN
        EXISTS_TAC `{x | x IN ball(a,r) /\
                         ~(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x =
                           wan_wd (ball(a,r)) i u x - wan_wd (ball(a,r)) i h x)}` THEN
        ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
        SUBGOAL_THEN `wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x =
                      wan_wd (ball(a,r)) i u x - wan_wd (ball(a,r)) i h x` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[GSYM LIFT_SUB] THEN AP_TERM_TAC THEN
        REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_LSUB; DOT_RSUB] THEN
        REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= z - (z - y)`) THEN
      REWRITE_TAC[GSYM DROP_CMUL] THEN ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP];
      (* the coefficient part *)
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `drop(integral (ball(a,r))
          (\x. (&2 * lam) %
               (lift(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x dot
                     ((G0:real^K^K) ** wan_wd (ball(a,r)) i u x)) -
                lift(wan_wd (ball(a,r)) i (\x. u x - h x) x dot
                     ((G:real^K->real^K^K)(u x) ** wan_wd (ball(a,r)) i u x)))))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRABLE_SUB; INTEGRAL_SUB; DROP_CMUL; DROP_SUB] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `drop(integral (ball(a,r))
          (\x. lam pow 2 %
               lift(norm(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x) pow 2) +
               (C3 * e0) pow 2 % lift(norm(wan_wd (ball(a,r)) i u x) pow 2)))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL; DROP_ADD; DROP_CMUL] THEN
        REAL_ARITH_TAC] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_SUB; INTEGRABLE_ADD] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_ADD; LIFT_DROP] THEN
      SUBGOAL_THEN `(x:real^2) IN cball(a,r)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`a:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC `kx = wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - h x) x` THEN
      ABBREV_TAC `qx = wan_wd (ball(a,r)) i (u:real^2->real^K) x` THEN
      SUBGOAL_THEN `(kx:real^K) dot ((G0:real^K^K) ** qx) -
                    kx dot ((G:real^K->real^K^K)((u:real^2->real^K) x) ** qx) <=
                    norm kx * (C3 * e0 * norm(qx:real^K))`
      ASSUME_TAC THENL
       [REWRITE_TAC[GSYM DOT_RSUB; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm(kx:real^K) * norm(((G0:real^K^K) - G((u:real^2->real^K) x)) ** qx)` THEN
        REWRITE_TAC[NORM_CAUCHY_SCHWARZ] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `C3 * norm((u:real^2->real^K) a - u x) * norm(qx:real^K)` THEN
        CONJ_TAC THENL
         [EXPAND_TAC "G0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (lam * norm(kx:real^K) - C3 * e0 * norm(qx:real^K)) pow 2` MP_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * lam * ((kx:real^K) dot ((G0:real^K^K) ** qx) -
                    kx dot ((G:real^K->real^K^K)((u:real^2->real^K) x) ** qx)) <=
                    &2 * lam * (norm kx * (C3 * e0 * norm(qx:real^K)))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]];
    ALL_TAC] THEN
  (* orthogonality and the Euler-Lagrange identity *)
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real^K`; `G0:real^K^K`;
                 `\x. (u:real^2->real^K) x - h x`] HMRC_HARM_ORTHO) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `ball(a:real^2,r)`;
                                `\x. (u:real^2->real^K) x - h x`; `&2 * e0`] o
    check (fun th -> can (find_term (fun t -> t = `Ca:real`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN DISCH_TAC THEN
  FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) o check (fun th ->
    can (find_term (fun t -> t = `lam:real`)) (concl th) && is_forall(concl th) &&
    can (find_term (fun t -> t = `C3:real`)) (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUM_2; wan_dir; DIMINDEX_2]) THEN
  REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2] THEN
  MATCH_MP_TAC HMRC_COMPARE_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`drop(integral (ball(a,r)) (\x. lift(wan_wd (ball(a,r)) 1 (\x. (u:real^2->real^K) x - h x) x dot
                                         ((G0:real^K^K) ** wan_wd (ball(a,r)) 1 u x))))`;
    `drop(integral (ball(a,r)) (\x. lift(wan_wd (ball(a,r)) 2 (\x. (u:real^2->real^K) x - h x) x dot
                                         ((G0:real^K^K) ** wan_wd (ball(a,r)) 2 u x))))`;
    `drop(integral (ball(a,r)) (\x. lift(wan_wd (ball(a,r)) 1 (\x. (u:real^2->real^K) x - h x) x dot
                                         ((G:real^K->real^K^K)(u x) ** wan_wd (ball(a,r)) 1 u x))))`;
    `drop(integral (ball(a,r)) (\x. lift(wan_wd (ball(a,r)) 2 (\x. (u:real^2->real^K) x - h x) x dot
                                         ((G:real^K->real^K^K)(u x) ** wan_wd (ball(a,r)) 2 u x))))`;
    `drop(integral (ball(a,r)) (\x. lift(((G0:real^K^K) ** wan_wd (ball(a,r)) 1 (h:real^2->real^K) x) dot
                                         wan_wd (ball(a,r)) 1 (\x. (u:real^2->real^K) x - h x) x)))`;
    `drop(integral (ball(a,r)) (\x. lift(((G0:real^K^K) ** wan_wd (ball(a,r)) 2 (h:real^2->real^K) x) dot
                                         wan_wd (ball(a,r)) 2 (\x. (u:real^2->real^K) x - h x) x)))`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The Dirichlet integral of a smooth map is the integral of hmr_e; decay of *)
(* the Dirichlet integral of a harmonic map on concentric discs (sub-mean    *)
(* value of the subharmonic hmr_e).                                          *)
(* ========================================================================= *)

let HMRC_DIR_SMOOTH = prove
 (`!(B:real^2->bool) (h:real^2->real^K).
     open B /\ smooth_map_on B h /\ wan_w12 B h
     ==> (\x. lift(hmr_e h x)) integrable_on B /\
         wan_dir B h = drop(integral B (\x. lift(hmr_e h x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 B (h:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> (\x. partial_derivative i (h:real^2->real^K) x) IN lspace B (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(partial_derivative 1 (h:real^2->real^K) x) pow 2)) integrable_on B /\
    (\x. lift(norm(partial_derivative 2 (h:real^2->real^K) x) pow 2)) integrable_on B`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(hmr_e (h:real^2->real^K) x)) =
                (\x. lift(norm(partial_derivative 1 h x) pow 2) +
                     lift(norm(partial_derivative 2 h x) pow 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; hmr_e; GSYM LIFT_ADD; NORM_POW_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRAL_ADD; DROP_ADD] THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `h:real^2->real^K`]
    (REWRITE_RULE[WAN_W12_C1_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_W12_C1))) THEN
  ASM_SIMP_TAC[DIMINDEX_2; WAN_W12_IMP_LSPACE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SUM_2]);;

(* hmr_e of a harmonic map is subharmonic. *)

let HMRC_HARM_E_SUB = prove
 (`!(B:real^2->bool) (h:real^2->real^K).
     open B /\ smooth_map_on B h /\
     (!x j. x IN B /\ 1 <= j /\ j <= dimindex(:K)
            ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0)
     ==> !x. x IN B ==> &0 <= llap (\y:real^2. mat 1) (hmr_e h) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN B ==> hmr_vlap (h:real^2->real^K) y = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B:real^2->bool`; `h:real^2->real^K`; `j:num`; `y:real^2`]
      HMR_LAP_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`B:real^2->bool`; `\y. (h:real^2->real^K) y$j`; `y:real^2`] HMR_LLAP_CML) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `hmr_e (h:real^2->real^K)`; `x:real^2`] HMR_LLAP_CML) THEN
  ASM_SIMP_TAC[HMR_E_SMOOTH; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `h:real^2->real^K`; `x:real^2`] HMR_LAP_E) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!i. partial_derivative i (\y. hmr_vlap (h:real^2->real^K) y) x = vec 0`
  (fun th -> REWRITE_TAC[th; DOT_RZERO; SUM_0; REAL_MUL_RZERO; REAL_ADD_RID]) THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `partial_derivative i (\y:real^2. vec 0:real^K) x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `B:real^2->bool` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[partial_derivative] THEN
      SUBGOAL_THEN `frechet_derivative (\y:real^2. vec 0:real^K) (at x) = (\v. vec 0)`
      (fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DOT_POS_LE]);;

let HMRC_HARM_DECAY = prove
 (`!(a:real^2) r rho (h:real^2->real^K).
     &0 < rho /\ rho <= r /\ smooth_map_on (ball(a,r)) h /\
     (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
            ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
     wan_w12 (ball(a,r)) h
     ==> wan_dir (ball(a,rho)) h <= &4 * (rho / r) pow 2 * wan_dir (ball(a,r)) h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,rho) SUBSET ball(a,r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real^K`] HMRC_DIR_SMOOTH) THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `h:real^2->real^K`] HMRC_DIR_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN `!x. &0 <= drop(lift(hmr_e (h:real^2->real^K) x))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP; HMR_E_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop(integral (ball(a,r)) (\x. lift(hmr_e (h:real^2->real^K) x)))`
  ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `r <= &2 * rho` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(a,r)) (\x. lift(hmr_e (h:real^2->real^K) x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / &2 <= rho / r` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `&1 / &4 <= x ==> &1 <= &4 * x`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* small discs: the sub-mean value inequality *)
  ABBREV_TAC `I0 = drop(integral (ball(a,r)) (\x. lift(hmr_e (h:real^2->real^K) x)))` THEN
  SUBGOAL_THEN `!y. y IN ball(a:real^2,rho)
                    ==> hmr_e (h:real^2->real^K) y <= inv(pi * (r / &2) pow 2) * I0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `cball(y:real^2,r / &2) SUBSET ball(a,r)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN X_GEN_TAC `z:real^2` THEN
      UNDISCH_TAC `(y:real^2) IN ball(a,rho)` THEN REWRITE_TAC[IN_BALL] THEN
      MP_TAC(NORM_ARITH `dist(a:real^2,z) <= dist(a,y) + dist(y,z)`) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`ball(a:real^2,r)`; `hmr_e (h:real^2->real^K)`; `y:real^2`; `r / &2`]
      (REWRITE_RULE[WAN_SUBMEAN_2D_STATEMENT] WAN_SUBMEAN_2D)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_BALL; HMR_E_SMOOTH; REAL_HALF] THEN
      MATCH_MP_TAC HMRC_HARM_E_SUB THEN ASM_REWRITE_TAC[OPEN_BALL];
      DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[PI_POS_LE; REAL_LE_POW_2];
      ALL_TAC] THEN
    EXPAND_TAC "I0" THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`cball(y:real^2,r / &2)`; `ball(a:real^2,r)`] SUBSET_TRANS) THEN
      REWRITE_TAC[BALL_SUBSET_CBALL] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
      MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
        `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH; OPEN_BALL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(a:real^2,rho)) (\y. lift(inv(pi * (r / &2) pow 2) * I0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
      `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
  ASM_SIMP_TAC[AREA_BALL; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MP_TAC PI_POS THEN UNDISCH_TAC `&0 < r` THEN
  CONV_TAC REAL_FIELD);;

(* One Morrey step: comparison with the harmonic replacement. *)

let HMRC_MORREY_STEP = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?C. &0 <= C /\
             !s (u:real^2->real^K) a r rho e0.
                cm_wharmonic S G s u /\ &0 < rho /\ rho <= r /\ cball(a,r) SUBSET s /\
                (!x. x IN cball(a,r) ==> norm(u x - u a) <= e0)
                ==> wan_dir (ball(a,rho)) u <=
                    (&8 * (rho / r) pow 2 + C * (e0 pow 2 + e0)) * wan_dir (ball(a,r)) u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Cc:real` STRIP_ASSUME_TAC o MATCH_MP HMRC_COMPARE) THEN
  EXISTS_TAC `&2 * Cc` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `a:real^2`; `r:real`;
                       `rho:real`; `e0:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on cball(a,r) /\ wan_w12 (ball(a,r)) u /\
                ball(a:real^2,rho) SUBSET ball(a,r) /\ &0 <= e0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      ASM_SIMP_TAC[SUBSET_BALL];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((u:real^2->real^K) a - u a)` THEN
      REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the harmonic replacement *)
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `u:real^2->real^K`]
    (REWRITE_RULE[WAN_DIRICHLET_DISC_STATEMENT] (ISPEC `(:K)` WAN_DIRICHLET_DISC))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (h:real^2->real^K) <= wan_dir (ball(a,r)) (u:real^2->real^K)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN
    MATCH_MP_TAC WAN_VTEST_W120 THEN REWRITE_TAC[OPEN_BALL; wan_vtest; SMOOTH_MAP_ON_CONST] THEN
    EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[COMPACT_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (\x. (u:real^2->real^K) x - h x) <=
                Cc * (e0 pow 2 + e0) * wan_dir (ball(a,r)) u`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,rho)) (h:real^2->real^K) <=
                &4 * (rho / r) pow 2 * wan_dir (ball(a,r)) h`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMRC_HARM_DECAY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (\x. (u:real^2->real^K) x - h x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,rho)) (\x. (u:real^2->real^K) x - h x) <=
                wan_dir (ball(a,r)) (\x. u x - h x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_DIR_SUBSET_LE THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,rho)) (u:real^2->real^K) <=
                &2 * wan_dir (ball(a,rho)) (\x. u x - h x) + &2 * wan_dir (ball(a,rho)) h`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `wan_w12 (ball(a,rho)) (\x. (u:real^2->real^K) x - h x) /\
                  wan_w12 (ball(a,rho)) (\x. --((h:real^2->real^K) x))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
        ASM_REWRITE_TAC[OPEN_BALL];
        MATCH_MP_TAC WAN_W12_NEG THEN MATCH_MP_TAC WAN_W12_SUBSET THEN
        EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[OPEN_BALL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(a:real^2,rho)`; `\x. (u:real^2->real^K) x - h x`;
                   `\x. --((h:real^2->real^K) x)`] HMD_DIR_SUB_LE) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    REWRITE_TAC[VECTOR_ARITH `(u:real^K) - h - --h = u`; ETA_AX] THEN
    MP_TAC(ISPECL [`ball(a:real^2,rho)`; `h:real^2->real^K`; `--(&1)`] WAN_DIR_CMUL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC WAN_W12_SUBSET THEN
      EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `--(&1) % (x:real^K) = --x`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho / r) pow 2 * wan_dir (ball(a,r)) (h:real^2->real^K) <=
                (rho / r) pow 2 * wan_dir (ball(a,r)) (u:real^2->real^K)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Morrey iteration.  A monotone nonnegative function with               *)
(* phi(r/256) <= phi(r)/4096 for r <= R0 satisfies                           *)
(* phi(rho) <= 4096 (rho/r)^(3/2) phi(r) for rho <= r <= R0.                 *)
(* ========================================================================= *)

let HMRC_RPOW_POW_INV = prove
 (`!n. (inv(&256) pow n) rpow (&3 / &2) = inv(&4096) pow n`,
  GEN_TAC THEN REWRITE_TAC[GSYM RPOW_POW] THEN
  SIMP_TAC[RPOW_RPOW; REAL_LE_INV_EQ; REAL_POS] THEN
  SUBGOAL_THEN `inv(&256) = inv(&16) rpow &2` SUBST1_TAC THENL
   [REWRITE_TAC[RPOW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[RPOW_RPOW; REAL_LE_INV_EQ; REAL_POS] THEN
  SUBGOAL_THEN `&2 * &n * &3 / &2 = &3 * &n` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&4096) = inv(&16) rpow &3` SUBST1_TAC THENL
   [REWRITE_TAC[RPOW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[RPOW_RPOW; REAL_LE_INV_EQ; REAL_POS]);;

let HMRC_ITER_MORREY = prove
 (`!(phi:real->real) R0.
     &0 < R0 /\ (!t. &0 < t /\ t <= R0 ==> &0 <= phi t) /\
     (!s t. &0 < s /\ s <= t /\ t <= R0 ==> phi s <= phi t) /\
     (!r. &0 < r /\ r <= R0 ==> phi(r / &256) <= phi r / &4096)
     ==> !rho r. &0 < rho /\ rho <= r /\ r <= R0
                 ==> phi rho <= &4096 * (rho / r) rpow (&3 / &2) * phi r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n r. &0 < r /\ r <= R0
                      ==> &0 < r * inv(&256) pow n /\ r * inv(&256) pow n <= R0 /\
                          r * inv(&256) pow n <= r`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < inv(&256) pow n /\ inv(&256) pow n <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC REAL_POW_1_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `r * inv(&256) pow n <= r` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n r. &0 < r /\ r <= R0
                      ==> phi(r * inv(&256) pow n) <= phi r * inv(&4096) pow n`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL [REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_LE_REFL]; ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
      can (find_term (fun t -> t = `phi:real->real`)) (concl th) &&
      can (find_term (fun t -> t = `n:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ih")] THEN
    MP_TAC(SPECL [`n:num`; `r:real`] (ASSUME
     `!n r. &0 < r /\ r <= R0
            ==> &0 < r * inv(&256) pow n /\ r * inv(&256) pow n <= R0 /\
                r * inv(&256) pow n <= r`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPEC `r * inv(&256) pow n` (ASSUME
     `!r. &0 < r /\ r <= R0 ==> (phi:real->real)(r / &256) <= phi r / &4096`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(r * inv(&256) pow n) / &256 = r * inv(&256) pow SUC n` SUBST1_TAC THENL
     [REWRITE_TAC[real_pow; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ih" MP_TAC THEN REWRITE_TAC[real_pow] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`rho:real`; `r:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?n. r * inv(&256) pow n < rho` MP_TAC THENL
   [MP_TAC(SPECL [`inv(&256)`; `rho / r`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
    UNDISCH_TAC `inv(&256) pow n < rho / r` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
   [REWRITE_TAC[real_pow; REAL_MUL_RID; LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n':num`) THEN REWRITE_TAC[LT; REAL_NOT_LT] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(phi:real->real)(r * inv(&256) pow n')` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `phi:real->real`)) (concl th) &&
      can (find_term (fun t -> t = `s:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(phi:real->real) r * inv(&4096) pow n'` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&4096) pow SUC n' <= (rho / r) rpow (&3 / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HMRC_RPOW_POW_INV] THEN MATCH_MP_TAC RPOW_LE2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (phi:real->real) r` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&4096) pow SUC n' * (phi:real->real) r <=
                (rho / r) rpow (&3 / &2) * phi r` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Morrey decay of the energy of a continuous weakly harmonic map, uniformly *)
(* on compact subsets:                                                       *)
(*   int_{B(x,rho)} |Du|^2 <= Cm rho^(3/2).                                 *)
(* ========================================================================= *)

let HMRC_COMPACT_NBHD = prove
 (`!(s:real^2->bool) K.
     open s /\ compact K /\ K SUBSET s
     ==> ?d0 K'. &0 < d0 /\ compact K' /\ K' SUBSET s /\
                 !x y. x IN K /\ dist(x,y) <= d0 ==> y IN K'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^2->bool`; `(:real^2) DIFF s`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d / &2`; `{x + y:real^2 | x IN K /\ y IN cball(vec 0,d / &2)}`] THEN
  ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL; REAL_HALF] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_CBALL_0] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM IN_DIFF] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `x + y:real^2`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    REWRITE_TAC[NORM_ARITH `dist(x:real^2,x + y) = norm y`] THEN
    ASM_CASES_TAC `(x:real^2) + y IN s` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `y - x:real^2`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0; VECTOR_ARITH `x + y - x:real^2 = y`] THEN
    ASM_MESON_TAC[dist; NORM_SUB]]);;

let HMRC_SMALL_E = prove
 (`!C. &0 <= C ==> ?e. &0 < e /\ e <= &1 /\ C * (e pow 2 + e) <= &1 / &8192`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `inv(&16384 * (C + &1))` THEN
  SUBGOAL_THEN `&1 <= &16384 * (C + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&16384 * (C + &1)) /\ inv(&16384 * (C + &1)) <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `m = inv(&16384 * (C + &1))` THEN
  SUBGOAL_THEN `m pow 2 <= m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * (&2 * m)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * (&2 * m) = (&2 * C) / (&16384 * (C + &1))` SUBST1_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &16384 * (C + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let HMRC_MORREY = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !s (u:real^2->real^K) K.
            open s /\ cm_wharmonic S G s u /\ compact K /\ K SUBSET s
            ==> ?r1 Cm. &0 < r1 /\ &0 <= Cm /\ (!x. x IN K ==> cball(x,r1) SUBSET s) /\
                        !x rho. x IN K /\ &0 < rho /\ rho <= r1
                                ==> wan_dir (ball(x,rho)) u <= Cm * rho rpow (&3 / &2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC o MATCH_MP HMRC_MORREY_STEP) THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `K:real^2->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  MP_TAC(SPEC `C:real` HMRC_SMALL_E) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  (* uniform continuity on a compact neighbourhood *)
  MP_TAC(ISPECL [`s:real^2->bool`; `K:real^2->bool`] HMRC_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `K':real^2->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `K':real^2->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e1:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r1 = min d0 (eta / &2)` THEN
  SUBGOAL_THEN `&0 < r1 /\ r1 <= d0 /\ r1 < eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r1" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN K ==> cball(x:real^2,r1) SUBSET K'` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r1:real`; `&4096 * wan_dir s (u:real^2->real^K) / r1 rpow (&3 / &2)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[WAN_DIR_POS; RPOW_POS_LE; REAL_LT_IMP_LE];
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `rho:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. &0 < t /\ t <= r1 ==> wan_w12 (ball(x:real^2,t)) (u:real^2->real^K)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(x:real^2,r1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^2,r1)` THEN
      ASM_SIMP_TAC[SUBSET_BALL; BALL_SUBSET_CBALL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. wan_dir (ball(x:real^2,t)) (u:real^2->real^K)`; `r1:real`]
    HMRC_ITER_MORREY) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`a1:real`; `b1:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC HMD_DIR_SUBSET_LE THEN
      ASM_SIMP_TAC[OPEN_BALL; SUBSET_BALL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `x:real^2`; `r:real`;
                                    `r / &256`; `e1:real`] o
        check (fun th -> can (find_term (fun t -> t = `C:real`)) (concl th) &&
                         is_forall (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,r1)` THEN
          ASM_SIMP_TAC[SUBSET_CBALL] THEN ASM SET_TAC[];
          X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM dist] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          SUBGOAL_THEN `(x:real^2) IN K' /\ (y:real^2) IN K'` STRIP_ASSUME_TAC THENL
           [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
              can (find_term (fun t -> t = `d0:real`)) (concl th) && is_forall(concl th))) THEN
            EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `y * p <= z ==> x <= y * p ==> x <= z`) THEN
      SUBGOAL_THEN `&0 <= wan_dir (ball(x:real^2,r)) (u:real^2->real^K)` ASSUME_TAC THENL
       [MATCH_MP_TAC WAN_DIR_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(r / &256) / r = &1 / &256` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `(C * (e1 pow 2 + e1)) * wan_dir (ball(x:real^2,r)) (u:real^2->real^K) <=
                    (&1 / &8192) * wan_dir (ball(x,r)) u` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`rho:real`; `r1:real`]) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `wan_dir (ball(x:real^2,r1)) (u:real^2->real^K) <= wan_dir s u` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_DIR_SUBSET_LE THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,r1)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_DIV] THEN
  SUBGOAL_THEN `&0 < r1 rpow (&3 / &2) /\ &0 <= rho rpow (&3 / &2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT; RPOW_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&4096 * rho rpow (&3 / &2) / r1 rpow (&3 / &2) *
                wan_dir (ball(x:real^2,r1)) (u:real^2->real^K) <=
                &4096 * rho rpow (&3 / &2) / r1 rpow (&3 / &2) * wan_dir s u` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
  UNDISCH_TAC `&0 < r1 rpow (&3 / &2)` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Hoelder continuity of a continuous weakly harmonic map with exponent 3/4, *)
(* uniformly on compact subsets (Morrey decay, Poincare inequality,          *)
(* Campanato).                                                               *)
(* ========================================================================= *)

let HMRC_HOLDER_CONT = prove
 (`!(s:real^2->bool) (w:real^2->real^K) L al.
     &0 < al /\ &0 <= L /\
     (!x y. x IN s /\ y IN s ==> norm(w x - w y) <= L * norm(x - y) rpow al)
     ==> w continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_on] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(e / (L + &1)) rpow (inv al)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN REWRITE_TAC[dist] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * norm(y - x:real^2) rpow al` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * e / (L + &1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `e / (L + &1) = ((e / (L + &1)) rpow (inv al)) rpow al` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 <= e / (L + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[RPOW_RPOW; REAL_MUL_LINV; REAL_LT_IMP_NZ; RPOW_POW] THEN
      REWRITE_TAC[REAL_POW_1];
      ALL_TAC] THEN
    MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `dist(y:real^2,x) < (e / (L + &1)) rpow inv al` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < L + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let HMRC_HOLDER = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !s (u:real^2->real^K) K.
            open s /\ cm_wharmonic S G s u /\ compact K /\ K SUBSET s
            ==> ?r2 Ch. &0 < r2 /\ &0 <= Ch /\ (!x. x IN K ==> cball(x,r2) SUBSET s) /\
                        !x y. x IN K /\ y IN cball(x,r2)
                              ==> norm(u y - u x) <= Ch * norm(y - x) rpow (&3 / &4)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `K:real^2->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `K:real^2->bool`] HMRC_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `K2:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")))))) THEN
  SUBGOAL_THEN `!x:real^2. x IN K ==> x IN K2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "nb" MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `K2:real^2->bool`] o
    MATCH_MP HMRC_MORREY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `Cm:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "cb") (LABEL_TAC "mo")))))) THEN
  MP_TAC(REWRITE_RULE[WAN_POINCARE_BALL_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_POINCARE_BALL)) THEN
  DISCH_THEN(X_CHOOSE_THEN `CP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "po"))) THEN
  MP_TAC(SPEC `&3 / &4` (REWRITE_RULE[WAN_CAMPANATO_STATEMENT]
    (ISPECL [`(:2)`; `(:K)`] WAN_CAMPANATO))) THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ca"))) THEN
  ABBREV_TAC `R = min d0 r1` THEN
  SUBGOAL_THEN `&0 < R /\ R <= d0 /\ R <= r1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(CP * Cm) /\ &0 <= CC * sqrt(CP * Cm)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt(CP * Cm)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`R / &4`; `CC * sqrt(CP * Cm)`] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(x:real^2,r1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "cb" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  (* the ball around a *)
  SUBGOAL_THEN `ball(a:real^2,R) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,r1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "cb" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2 rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,R)
                               ==> x IN K2 /\ rho <= r1`
  (LABEL_TAC "in") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET_BALLS] THEN STRIP_TAC THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`x:real^2`; `a:real^2`] DIST_POS_LE) THEN DISCH_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "nb" MATCH_MP_TAC THEN EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the Campanato condition from Poincare and the Morrey decay *)
  SUBGOAL_THEN
   `!x:real^2 rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,R)
                   ==> drop(integral (ball(x,rho))
                         (\z. lift(norm((u:real^2->real^K) z - inv(measure(ball(x,rho))) %
                                        integral (ball(x,rho)) u) pow 2)))
                       <= sqrt(CP * Cm) pow 2 * rho rpow (&7 / &2)`
  (LABEL_TAC "var") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `rho:real`] THEN STRIP_TAC THEN
    USE_THEN "in" (MP_TAC o SPECL [`x:real^2`; `rho:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `ball(x:real^2,rho) SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,r1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "cb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `rho rpow (&7 / &2) = rho pow 2 * rho rpow (&3 / &2)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&7 / &2 = &2 + &3 / &2`] THEN
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(CP * Cm) pow 2 = CP * Cm` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CP * rho pow 2 * wan_dir (ball(x,rho)) (u:real^2->real^K)` THEN CONJ_TAC THENL
     [USE_THEN "po" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(CP * Cm) * rho pow 2 * rho rpow (&3 / &2) =
                  CP * rho pow 2 * Cm * rho rpow (&3 / &2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    USE_THEN "mo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Campanato *)
  USE_THEN "ca" (MP_TAC o SPECL [`a:real^2`; `R:real`; `u:real^2->real^K`; `sqrt(CP * Cm)`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `wan_w12 (ball(a:real^2,R)) (u:real^2->real^K)` MP_TAC THENL
       [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
        ASM_REWRITE_TAC[OPEN_BALL];
        SIMP_TAC[wan_w12]];
      USE_THEN "var" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^2->real^K) continuous_on ball(a,R / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRC_HOLDER_CONT THEN
    MAP_EVERY EXISTS_TAC [`CC * sqrt(CP * Cm)`; `&3 / &4`] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,R / &2) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^2,R)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,R / &2)`; `u:real^2->real^K`; `w:real^2->real^K`]
    WAN_CONT_AE_EQ_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(y:real^2) IN ball(a,R / &2) /\ (a:real^2) IN ball(a,R / &2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^2) IN cball(a,R / &4)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2->real^K) y = w y /\ u a = w a` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Algebra of the ball variances wanl_cp_var (pc_wan_lap2c): an L2 triangle  *)
(* inequality, the variance is at most four times the mean square distance   *)
(* to any constant, quasi-monotonicity in the radius, splitting against a    *)
(* second function, and the decomposition into scalar components.            *)
(* ========================================================================= *)

let HMRC_SQ_TRI = prove
 (`!a b d. &0 <= a /\ a <= b + d /\ &0 <= b /\ &0 <= d
           ==> a pow 2 <= &2 * b pow 2 + &2 * d pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(b + d) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    MP_TAC(SPEC `b - d` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let HMRC_L2_SQ_INTEGRABLE = prove
 (`!(B:real^N->bool) (p:real^N->real^K) q.
     p IN lspace B (&2) /\ q IN lspace B (&2)
     ==> (\y. lift(norm(p y - q y) pow 2)) integrable_on B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
  MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let HMRC_L2_TRI = prove
 (`!(B:real^N->bool) (p:real^N->real^K) q z.
     p IN lspace B (&2) /\ q IN lspace B (&2) /\ z IN lspace B (&2)
     ==> drop(integral B (\y. lift(norm(p y - q y) pow 2))) <=
         &2 * drop(integral B (\y. lift(norm(p y - z y) pow 2))) +
         &2 * drop(integral B (\y. lift(norm(z y - q y) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift(norm((p:real^N->real^K) y - q y) pow 2)) integrable_on B /\
                (\y. lift(norm((p:real^N->real^K) y - z y) pow 2)) integrable_on B /\
                (\y. lift(norm((z:real^N->real^K) y - q y) pow 2)) integrable_on B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HMRC_L2_SQ_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * drop(integral B (\y. lift(norm((p:real^N->real^K) y - z y) pow 2))) +
    &2 * drop(integral B (\y. lift(norm((z:real^N->real^K) y - q y) pow 2))) =
    drop(integral B (\y. &2 % lift(norm((p:real^N->real^K) y - z y) pow 2) +
                         &2 % lift(norm((z:real^N->real^K) y - q y) pow 2)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL; DROP_ADD; DROP_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN MATCH_MP_TAC HMRC_SQ_TRI THEN
  REWRITE_TAC[NORM_POS_LE] THEN CONV_TAC NORM_ARITH);;

(* The variance is at most four times the mean square distance to c. *)

let HMRC_VAR_LE4 = prove
 (`!(f:real^N->real^K) a r x rho c.
     &0 < rho /\ f IN lspace (ball(a,r)) (&2) /\ ball(x,rho) SUBSET ball(a,r)
     ==> wanl_cp_var f x rho <=
         &4 * drop(integral (ball(x,rho)) (\y. lift(norm(f y - c) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `a:real^N`; `r:real`; `x:real^N`; `rho:real`; `c:real^K`]
    WANL_CP_MEAN_DEV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) IN lspace (ball(x,rho)) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(x:real^N,rho)`; `f:real^N->real^K`;
                 `\y:real^N. wanl_cp_mean (f:real^N->real^K) x rho`; `\y:real^N. (c:real^K)`]
    HMRC_L2_TRI) THEN
  ASM_SIMP_TAC[LSPACE_CONST; MEASURABLE_BALL] THEN
  REWRITE_TAC[GSYM wanl_cp_var] THEN
  ASM_SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; LIFT_DROP; DROP_CMUL] THEN
  ABBREV_TAC `mu = measure(ball(x:real^N,rho))` THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN ASM_REWRITE_TAC[MEASURE_BALL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `mu * norm(c - wanl_cp_mean (f:real^N->real^K) x rho) pow 2 <=
                drop(integral (ball(x,rho)) (\y. lift(norm(f y - c) pow 2)))`
  MP_TAC THENL
   [SUBGOAL_THEN `norm(c - wanl_cp_mean (f:real^N->real^K) x rho) =
                  norm(wanl_cp_mean f x rho - c)` SUBST1_TAC THENL
     [MATCH_ACCEPT_TAC NORM_SUB; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mu * inv mu * drop(integral (ball(x,rho))
                  (\y. lift(norm((f:real^N->real^K) y - c) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID;
                   REAL_LE_REFL]];
    REAL_ARITH_TAC]);;

let HMRC_VAR_POS = prove
 (`!(f:real^N->real^K) a r x rho.
     f IN lspace (ball(a,r)) (&2) /\ ball(x,rho) SUBSET ball(a,r)
     ==> &0 <= wanl_cp_var f x rho`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_cp_var] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC WANL_CP_SQ_INTEGRABLE THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[]);;

let HMRC_VAR_MONO4 = prove
 (`!(f:real^N->real^K) a r x rho t.
     &0 < rho /\ rho <= t /\ f IN lspace (ball(a,r)) (&2) /\ ball(x,t) SUBSET ball(a,r)
     ==> wanl_cp_var f x rho <= &4 * wanl_cp_var f x t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ball(x:real^N,rho) SUBSET ball(x,t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET_BALL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * drop(integral (ball(x,rho))
                (\y. lift(norm((f:real^N->real^K) y - wanl_cp_mean f x t) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HMRC_VAR_LE4 THEN MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; wanl_cp_var] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  CONJ_TAC THEN MATCH_MP_TAC WANL_CP_SQ_INTEGRABLE THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Splitting the variance of f against a second function g. *)

let HMRC_VAR_SPLIT = prove
 (`!(f:real^N->real^K) g a r x rho.
     &0 < rho /\ f IN lspace (ball(a,r)) (&2) /\ g IN lspace (ball(a,r)) (&2) /\
     ball(x,rho) SUBSET ball(a,r)
     ==> wanl_cp_var f x rho <=
         &8 * drop(integral (ball(x,rho)) (\y. lift(norm(f y - g y) pow 2))) +
         &8 * wanl_cp_var g x rho`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) IN lspace (ball(x,rho)) (&2) /\
                (g:real^N->real^K) IN lspace (ball(x,rho)) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * drop(integral (ball(x,rho))
                (\y. lift(norm((f:real^N->real^K) y - wanl_cp_mean g x rho) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HMRC_VAR_LE4 THEN MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(x:real^N,rho)`; `f:real^N->real^K`;
                 `\y:real^N. wanl_cp_mean (g:real^N->real^K) x rho`; `g:real^N->real^K`]
    HMRC_L2_TRI) THEN
  ASM_SIMP_TAC[LSPACE_CONST; MEASURABLE_BALL] THEN
  REWRITE_TAC[GSYM wanl_cp_var] THEN REAL_ARITH_TAC);;

(* Scalar components. *)

let HMRC_LSPACE_COMPONENT = prove
 (`!(s:real^N->bool) (f:real^N->real^K) k.
     f IN lspace s (&2) /\ 1 <= k /\ k <= dimindex(:K)
     ==> (\y. lift(f y$k)) IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(INST_TYPE [`:K`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
  EXISTS_TAC `f:real^N->real^K` THEN
  ASM_REWRITE_TAC[NORM_LIFT; COMPONENT_LE_NORM; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_LSPACE_MEASURABLE) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o GEN_REWRITE_RULE I [MEASURABLE_ON_COMPONENTWISE]) THEN
  ASM_REWRITE_TAC[]);;

let HMRC_VAR_COMPONENTS = prove
 (`!(f:real^N->real^K) a r x rho.
     f IN lspace (ball(a,r)) (&2) /\ ball(x,rho) SUBSET ball(a,r)
     ==> wanl_cp_var f x rho =
         sum(1..dimindex(:K)) (\k. wanl_cp_var (\y. lift(f y$k)) x rho)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) IN lspace (ball(x,rho)) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^K) integrable_on ball(x,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_INTEGRABLE_MEAS THEN ASM_REWRITE_TAC[MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. wanl_cp_mean (\y. lift((f:real^N->real^K) y$k)) x rho =
                    lift((wanl_cp_mean f x rho)$k)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wanl_cp_mean; VECTOR_MUL_COMPONENT; LIFT_CMUL] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[INTEGRAL_COMPONENT; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wanl_cp_var] THEN
  ABBREV_TAC `m = wanl_cp_mean (f:real^N->real^K) x rho` THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; REAL_POW2_ABS] THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= dimindex(:K)
                    ==> (\y. lift(((f:real^N->real^K) y$k - (m:real^K)$k) pow 2)) integrable_on
                        ball(x,rho)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(x:real^N,rho)`; `\y. lift((f:real^N->real^K) y$k)`;
                   `\y:real^N. lift((m:real^K)$k)`] HMRC_L2_SQ_INTEGRABLE) THEN
    ASM_SIMP_TAC[HMRC_LSPACE_COMPONENT; LSPACE_CONST; MEASURABLE_BALL] THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; REAL_POW2_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. norm((f:real^N->real^K) y - m) pow 2 =
                    sum(1..dimindex(:K)) (\k. (f y$k - m$k) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2; dot; VECTOR_SUB_COMPONENT; REAL_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\k:num y:real^N. lift(((f:real^N->real^K) y$k - (m:real^K)$k) pow 2)`;
                 `ball(x:real^N,rho)`; `1..dimindex(:K)`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF]);;

let HMRC_VAR_EQ_ON = prove
 (`!(f:real^N->real^K) g x rho.
     (!y. y IN ball(x,rho) ==> f y = g y)
     ==> wanl_cp_var f x rho = wanl_cp_var g x rho`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `wanl_cp_mean (f:real^N->real^K) x rho = wanl_cp_mean g x rho` ASSUME_TAC THENL
   [REWRITE_TAC[wanl_cp_mean] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wanl_cp_var] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Campanato decay of the partial derivatives of a smooth harmonic map       *)
(* (componentwise WAN_HARM_GRAD_OSC).                                        *)
(* ========================================================================= *)

let HMRC_DPART_CML = prove
 (`!i (u:real^2->real) z. wan_dpart i u z = cml_d i u z`,
  REWRITE_TAC[wan_dpart; cml_d; partial_derivative]);;

let HMRC_HARM_COMP_FACTS = prove
 (`!(s:real^2->bool) (h:real^2->real^K) a r k.
     open s /\ cball(a,r) SUBSET s /\ smooth_map_on s h /\
     (!x j. x IN s /\ 1 <= j /\ j <= dimindex(:K)
            ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
     1 <= k /\ k <= dimindex(:K)
     ==> smooth_map_on s (\x. lift(h x$k)) /\
         (!x. x IN s ==> llap (\y:real^2. mat 1) (\y. h y$k) x = &0) /\
         wan_grad (\y. h y$k) IN lspace (ball(a,r)) (&2) /\
         (!x i. x IN s /\ 1 <= i /\ i <= 2
                ==> wan_grad (\y. h y$k) x$i = (partial_derivative i h x)$k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (\x. lift((h:real^2->real^K) x$k))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN s ==> llap (\y:real^2. mat 1) (\y. (h:real^2->real^K) y$k) x = &0`
  ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\y. (h:real^2->real^K) y$k`] WANL_GRAD_FACTS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMR_LSPACE_CBALL THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HMRC_DPART_CML] THEN
  MATCH_MP_TAC HMR_D_COMPONENT THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[]);;

let HMRC_HARM_PD_VAR = prove
 (`!(s:real^2->bool) (h:real^2->real^K) a r t.
     open s /\ cball(a,r) SUBSET s /\ smooth_map_on s h /\
     (!x j. x IN s /\ 1 <= j /\ j <= dimindex(:K)
            ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
     &0 < t /\ t <= r
     ==> sum(1..2) (\i. wanl_cp_var (partial_derivative i h) a t) =
         sum(1..dimindex(:K)) (\k. wanl_cp_var (wan_grad (\y. h y$k)) a t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ball(a:real^2,t) SUBSET ball(a,r) /\ ball(a:real^2,r) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. partial_derivative i (h:real^2->real^K) IN lspace (ball(a,r)) (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HMR_LSPACE_CBALL THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. wanl_cp_var (partial_derivative i (h:real^2->real^K)) a t =
        sum(1..dimindex(:K)) (\k. wanl_cp_var (\y. lift(partial_derivative i h y$k)) a t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC HMRC_VAR_COMPONENTS THEN
    MAP_EVERY EXISTS_TAC [`a:real^2`; `r:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real^K`; `a:real^2`; `r:real`; `k:num`]
    HMRC_HARM_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wan_grad (\y. (h:real^2->real^K) y$k)`; `a:real^2`; `r:real`; `a:real^2`;
                 `t:real`] HMRC_VAR_COMPONENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIMINDEX_2] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HMRC_VAR_EQ_ON THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let HMRC_HARM_PD_DECAY = prove
 (`?C. &0 <= C /\
       !(s:real^2->bool) (h:real^2->real^K) a r rho.
          open s /\ &0 < rho /\ rho <= r /\ cball(a,r) SUBSET s /\ smooth_map_on s h /\
          (!x j. x IN s /\ 1 <= j /\ j <= dimindex(:K)
                 ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0)
          ==> sum(1..2) (\i. wanl_cp_var (partial_derivative i h) a rho) <=
              C * (rho / r) pow 4 *
              sum(1..2) (\i. wanl_cp_var (partial_derivative i h) a r)`,
  MP_TAC(REWRITE_RULE[WAN_HARM_GRAD_OSC_STATEMENT] (ISPEC `(:2)` WAN_HARM_GRAD_OSC)) THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "osc"))) THEN
  EXISTS_TAC `C:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `h:real^2->real^K`; `a:real^2`; `r:real`;
                       `rho:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real^K`; `a:real^2`; `r:real`; `rho:real`]
    HMRC_HARM_PD_VAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real^K`; `a:real^2`; `r:real`; `r:real`]
    HMRC_HARM_PD_VAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real^K`; `a:real^2`; `r:real`; `k:num`]
    HMRC_HARM_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "osc" (MP_TAC o SPECL [`s:real^2->bool`; `\y. (h:real^2->real^K) y$k`;
                                  `a:real^2`; `r:real`; `rho:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[wanl_cp_var; wanl_cp_mean; REAL_MUL_ASSOC]]);;

(* ========================================================================= *)
(* One decay step for the variances of the weak partial derivatives, by      *)
(* comparison with the harmonic replacement on a disc (HMRC_COMPARE,         *)
(* HMRC_HARM_PD_DECAY).                                                      *)
(* ========================================================================= *)

let HMRC_SMOOTH_WPD = prove
 (`!(B:real^2->bool) (h:real^2->real^K) i.
     open B /\ smooth_map_on B h /\ wan_w12 B h /\ 1 <= i /\ i <= 2
     ==> wan_wpd B i h (partial_derivative i h) /\
         partial_derivative i h IN lspace B (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wpd B i (h:real^2->real^K) (partial_derivative i h)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`B:real^2->bool`; `h:real^2->real^K`; `i:num`] WAN_WPD_C1) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `smooth_map_on B (h:real^2->real^K)` THEN SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMC_LSPACE_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`wan_wd B i (h:real^2->real^K)`;
    `{x | x IN B /\ ~(wan_wd B i (h:real^2->real^K) x = partial_derivative i h x)}`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`B:real^2->bool`; `i:num`; `h:real^2->real^K`] WAN_WD_WORKS) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN SIMP_TAC[];
    MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_REWRITE_TAC[DIMINDEX_2; ETA_AX];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]]);;

let HMRC_DIFF_DIR = prove
 (`!(s:real^2->bool) (u:real^2->real^K) (h:real^2->real^K) a r.
     open s /\ wan_w12 s u /\ ball(a,r) SUBSET s /\ smooth_map_on (ball(a,r)) h /\
     wan_w12 (ball(a,r)) h
     ==> wan_dir (ball(a,r)) (\x. u x - h x) =
         sum(1..2) (\i. drop(integral (ball(a,r))
                    (\y. lift(norm(wan_wd s i u y - partial_derivative i h y) pow 2))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x. (u:real^2->real^K) x - h x`;
                 `\i x. wan_wd s i (u:real^2->real^K) x -
                        partial_derivative i (h:real^2->real^K) x`]
    WAN_DIR_EQ) THEN
  REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real^K`; `i:num`] HMRC_SMOOTH_WPD) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `u:real^2->real^K`] WAN_WD_WORKS) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_WPD_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let HMRC_PD_STEP_ARITH = prove
 (`!Pr Ph Ph2 Pu2 Pu Dr D2 W q C0.
     &0 <= C0 /\ &0 <= q /\ q <= &1 /\ &0 <= W /\
     Pr <= &8 * Dr + &8 * Ph /\ Ph <= C0 * (&16 * q) * Ph2 /\ Ph2 <= &8 * D2 + &8 * Pu2 /\
     Pu2 <= &4 * Pu /\ Dr <= W /\ D2 <= W
     ==> Pr <= (&4096 * C0) * q * Pu + (&8 + &1024 * C0) * W`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C0 * (&16 * q) * Ph2 <= C0 * (&16 * q) * (&8 * W + &32 * Pu)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(C0 * W) * q <= (C0 * W) * &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let HMRC_PD_STEP_ARITH2 = prove
 (`!X C0 Cc q Pu E W.
     &0 <= C0 /\ &0 <= Cc /\ &0 <= q /\ &0 <= Pu /\ &0 <= E /\ W <= Cc * E /\
     X <= (&4096 * C0) * q * Pu + (&8 + &1024 * C0) * W
     ==> X <= (&4096 * C0 + (&8 + &1024 * C0) * Cc) * q * Pu +
              (&4096 * C0 + (&8 + &1024 * C0) * Cc) * E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= ((&8 + &1024 * C0) * Cc) * (q * Pu) /\ &0 <= (&4096 * C0) * E /\
                (&8 + &1024 * C0) * W <= (&8 + &1024 * C0) * (Cc * E)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let HMRC_PD_STEP = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?A. &0 <= A /\
             !s (u:real^2->real^K) a r rho e0.
                open s /\ cm_wharmonic S G s u /\ &0 < rho /\ rho <= r / &2 /\
                cball(a,r) SUBSET s /\ (!x. x IN cball(a,r) ==> norm(u x - u a) <= e0)
                ==> sum(1..2) (\i. wanl_cp_var (wan_wd s i u) a rho) <=
                    A * (rho / r) pow 4 * sum(1..2) (\i. wanl_cp_var (wan_wd s i u) a r) +
                    A * (e0 pow 2 + e0) * wan_dir (ball(a,r)) u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Cc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cmp")) o
    MATCH_MP HMRC_COMPARE) THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hd")) HMRC_HARM_PD_DECAY THEN
  EXISTS_TAC `&4096 * C0 + (&8 + &1024 * C0) * Cc` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `a:real^2`; `r:real`;
                       `rho:real`; `e0:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `&0 < r /\ rho <= r /\ &0 < r / &2 /\ r / &2 <= r` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,r) SUBSET s /\ (u:real^2->real^K) continuous_on cball(a,r) /\
                wan_w12 (ball(a,r)) u /\ &0 <= e0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((u:real^2->real^K) a - u a)` THEN
      REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,rho) SUBSET ball(a,r) /\ ball(a:real^2,r / &2) SUBSET ball(a,r)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SUBSET_BALL]; ALL_TAC] THEN
  (* the harmonic replacement *)
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `u:real^2->real^K`]
    (REWRITE_RULE[WAN_DIRICHLET_DISC_STATEMENT] (ISPEC `(:K)` WAN_DIRICHLET_DISC))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (\x. (u:real^2->real^K) x - h x) <=
                Cc * (e0 pow 2 + e0) * wan_dir (ball(a,r)) u`
  ASSUME_TAC THENL
   [USE_THEN "cmp" MATCH_MP_TAC THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> wan_wd s i (u:real^2->real^K) IN lspace (ball(a,r)) (&2) /\
                        partial_derivative i (h:real^2->real^K) IN lspace (ball(a,r)) (&2)`
  (LABEL_TAC "ls") THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; WAN_WD_WORKS; DIMINDEX_2];
      MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real^K`; `i:num`] HMRC_SMOOTH_WPD) THEN
      ASM_SIMP_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  (* the comparison integrals on smaller balls *)
  SUBGOAL_THEN
   `!t. &0 < t /\ t <= r
        ==> sum(1..2) (\i. drop(integral (ball(a,t))
                 (\y. lift(norm(wan_wd s i (u:real^2->real^K) y -
                                partial_derivative i (h:real^2->real^K) y) pow 2)))) <=
            wan_dir (ball(a,r)) (\x. u x - h x)`
  (LABEL_TAC "dt") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `h:real^2->real^K`; `a:real^2`;
                   `r:real`] HMRC_DIFF_DIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "ls" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `ball(a:real^2,t) SUBSET ball(a,r)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SUBSET_BALL]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    CONJ_TAC THEN MATCH_MP_TAC HMRC_L2_SQ_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  (* the variance estimates *)
  SUBGOAL_THEN
   `sum(1..2) (\i. wanl_cp_var (wan_wd s i (u:real^2->real^K)) a rho) <=
    &8 * sum(1..2) (\i. drop(integral (ball(a,rho))
           (\y. lift(norm(wan_wd s i u y - partial_derivative i (h:real^2->real^K) y) pow 2)))) +
    &8 * sum(1..2) (\i. wanl_cp_var (partial_derivative i h) a rho)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "ls" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC HMRC_VAR_SPLIT THEN MAP_EVERY EXISTS_TAC [`a:real^2`; `r:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. wanl_cp_var (partial_derivative i (h:real^2->real^K)) a rho) <=
    C0 * (&16 * (rho / r) pow 4) *
    sum(1..2) (\i. wanl_cp_var (partial_derivative i h) a (r / &2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&16 * (rho / r) pow 4 = (rho / (r / &2)) pow 4` SUBST1_TAC THENL
     [SUBGOAL_THEN `rho / (r / &2) = &2 * (rho / r)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "hd" MATCH_MP_TAC THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. wanl_cp_var (partial_derivative i (h:real^2->real^K)) a (r / &2)) <=
    &8 * sum(1..2) (\i. drop(integral (ball(a,r / &2))
           (\y. lift(norm(wan_wd s i (u:real^2->real^K) y - partial_derivative i h y) pow 2)))) +
    &8 * sum(1..2) (\i. wanl_cp_var (wan_wd s i u) a (r / &2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "ls" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `!y. norm(wan_wd s i (u:real^2->real^K) y -
                           partial_derivative i (h:real^2->real^K) y) =
                      norm(partial_derivative i h y - wan_wd s i u y)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_ACCEPT_TAC NORM_SUB; ALL_TAC] THEN
    MATCH_MP_TAC HMRC_VAR_SPLIT THEN MAP_EVERY EXISTS_TAC [`a:real^2`; `r:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. wanl_cp_var (wan_wd s i (u:real^2->real^K)) a (r / &2)) <=
    &4 * sum(1..2) (\i. wanl_cp_var (wan_wd s i u) a r)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "ls" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC HMRC_VAR_MONO4 THEN MAP_EVERY EXISTS_TAC [`a:real^2`; `r:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  (* nonnegativity *)
  SUBGOAL_THEN
   `&0 <= sum(1..2) (\i. wanl_cp_var (wan_wd s i (u:real^2->real^K)) a r) /\
    &0 <= wan_dir (ball(a,r)) (\x. u x - (h:real^2->real^K) x) /\
    &0 <= (e0 pow 2 + e0) * wan_dir (ball(a,r)) u /\
    &0 <= (rho / r) pow 4 /\ (rho / r) pow 4 <= &1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN USE_THEN "ls" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN MATCH_MP_TAC HMRC_VAR_POS THEN
      MAP_EVERY EXISTS_TAC [`a:real^2`; `r:real`] THEN ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[WAN_DIR_POS; REAL_LE_ADD; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_1_LE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRC_PD_STEP_ARITH2 THEN
  EXISTS_TAC `wan_dir (ball(a,r)) (\x. (u:real^2->real^K) x - h x)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HMRC_PD_STEP_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`sum(1..2) (\i. wanl_cp_var (partial_derivative i (h:real^2->real^K)) a rho)`;
    `sum(1..2) (\i. wanl_cp_var (partial_derivative i (h:real^2->real^K)) a (r / &2))`;
    `sum(1..2) (\i. wanl_cp_var (wan_wd s i (u:real^2->real^K)) a (r / &2))`;
    `sum(1..2) (\i. drop(integral (ball(a,rho))
           (\y. lift(norm(wan_wd s i (u:real^2->real^K) y -
                          partial_derivative i (h:real^2->real^K) y) pow 2))))`;
    `sum(1..2) (\i. drop(integral (ball(a,r / &2))
           (\y. lift(norm(wan_wd s i (u:real^2->real^K) y -
                          partial_derivative i (h:real^2->real^K) y) pow 2))))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "dt" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Iteration lemmas.  A general discrete iteration (phi(tau t) <= q phi(t),  *)
(* quasi-monotone phi), the conversion of q^n into a power of the radius for *)
(* tau = tt^8, q = tt^17, and the inhomogeneous decay lemma (exponent 4 with *)
(* a forcing term r^(9/4) gives the exponent 17/8).                          *)
(* ========================================================================= *)

let HMRC_ITER_GEN = prove
 (`!(phi:real->real) R0 tau q M0.
     &0 < R0 /\ &0 < tau /\ tau < &1 /\ &0 <= q /\ &0 <= M0 /\
     (!t. &0 < t /\ t <= R0 ==> &0 <= phi t) /\
     (!s t. &0 < s /\ s <= t /\ t <= R0 ==> phi s <= M0 * phi t) /\
     (!t. &0 < t /\ t <= R0 ==> phi(tau * t) <= q * phi t)
     ==> !rho. &0 < rho /\ rho <= R0
               ==> ?n. tau pow (n + 1) * R0 < rho /\ phi rho <= M0 * q pow n * phi R0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "nn") (CONJUNCTS_THEN2 (LABEL_TAC "mono")
      (LABEL_TAC "dec")))))))) THEN
  SUBGOAL_THEN `!n. &0 < tau pow n * R0 /\ tau pow n * R0 <= R0` (LABEL_TAC "pos") THENL
   [GEN_TAC THEN SUBGOAL_THEN `&0 < tau pow n /\ tau pow n <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (phi:real->real)(tau pow n * R0) <= q pow n * phi R0` (LABEL_TAC "it") THENL
   [INDUCT_TAC THENL [REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_LE_REFL]; ALL_TAC] THEN
    USE_THEN "pos" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q * (phi:real->real)(tau pow n * R0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN USE_THEN "dec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. tau pow (n + 1) * R0 < rho` MP_TAC THENL
   [MP_TAC(SPECL [`tau:real`; `rho / R0`] REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    EXISTS_TAC `m:num` THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `tau pow m * R0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      UNDISCH_TAC `tau pow m < rho / R0` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rho <= tau pow n * R0` ASSUME_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID];
      USE_THEN "min" (MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`; REAL_NOT_LT]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M0 * (phi:real->real)(tau pow n * R0)` THEN
  CONJ_TAC THENL
   [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let HMRC_ITER_EXP = prove
 (`!tt n rho R0.
     &0 < tt /\ &0 < rho /\ &0 < R0 /\ (tt pow 8) pow (n + 1) * R0 < rho
     ==> (tt pow 17) pow n <= inv(tt pow 17) * (rho / R0) rpow (&17 / &8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(tt pow 17) pow (n + 1) = ((tt pow 8) pow (n + 1)) rpow (&17 / &8)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_POW; GSYM RPOW_POW] THEN
    ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(tt pow 17) pow (n + 1) <= (rho / R0) rpow (&17 / &8)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_IMP_LE];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tt pow 17` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(tt pow 17) pow n = inv(tt pow 17) * (tt pow 17) pow (n + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN UNDISCH_TAC `&0 < tt pow 17` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let HMRC_TT_FACTS = prove
 (`!A. &0 <= A
       ==> &0 < inv(A + &2) /\ inv(A + &2) <= inv(&2) /\
           A * inv(A + &2) pow 32 <= inv(A + &2) pow 17 /\
           inv(A + &2) pow 18 < inv(A + &2) pow 17`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv(A + &2) /\ inv(A + &2) <= inv(&2) /\ A * inv(A + &2) <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < A + &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `tt = inv(A + &2)` THEN
  SUBGOAL_THEN `tt < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2)` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tt pow 31` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `tt pow 32 = tt * tt pow 31` SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `32 = SUC 31`; real_pow]; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC];
    SUBGOAL_THEN `tt pow 18 = tt * tt pow 17` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `18 = SUC 17`; real_pow]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LT]]);;

let HMRC_RPOW_TT = prove
 (`!tt t. &0 <= tt ==> (tt pow 8 * t) rpow (&9 / &4) = tt pow 18 * t rpow (&9 / &4)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RPOW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM RPOW_POW] THEN ASM_SIMP_TAC[RPOW_RPOW] THEN AP_TERM_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let HMRC_ITER_INHOM = prove
 (`!A. &0 <= A
       ==> ?C. &0 <= C /\
               !(psi:real->real) E R1.
                  &0 < R1 /\ &0 <= E /\
                  (!t. &0 < t /\ t <= R1 ==> &0 <= psi t) /\
                  (!s t. &0 < s /\ s <= t /\ t <= R1 ==> psi s <= &4 * psi t) /\
                  (!rho r. &0 < rho /\ rho <= r / &2 /\ r <= R1
                           ==> psi rho <= A * (rho / r) pow 4 * psi r + E * r rpow (&9 / &4))
                  ==> !rho. &0 < rho /\ rho <= R1
                            ==> psi rho <= C * (psi R1 + E * R1 rpow (&9 / &4)) *
                                           (rho / R1) rpow (&17 / &8)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `A:real` HMRC_TT_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tt = inv(A + &2)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `tt < &1 /\ &0 < tt pow 17 /\ &0 < tt pow 17 - tt pow 18 /\
                tt pow 17 - tt pow 18 <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `tt < &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2)` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `a <= &1 /\ &0 <= b ==> a - b <= &1`) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; REAL_POW_1_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `c1 = inv(tt pow 17 - tt pow 18)` THEN
  SUBGOAL_THEN `&1 <= c1 /\ c1 * (tt pow 17 - tt pow 18) = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `&4 * inv(tt pow 17) * c1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`psi:real->real`; `E:real`; `R1:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "nn") (CONJUNCTS_THEN2 (LABEL_TAC "mono")
       (LABEL_TAC "step"))))) THEN
  ABBREV_TAC `Kk = c1 * E` THEN
  SUBGOAL_THEN `&0 <= Kk /\ E + Kk * tt pow 18 = Kk * tt pow 17` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kk" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `c1 * (tt pow 17 - tt pow 18) = &1` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (psi:real->real) t + Kk * t rpow (&9 / &4)`; `R1:real`; `tt pow 8`;
                 `tt pow 17`; `&4`] HMRC_ITER_GEN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_POW_LT];
      MATCH_MP_TAC REAL_POW_1_LT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE]];
      MAP_EVERY X_GEN_TAC [`s':real`; `t:real`] THEN STRIP_TAC THEN
      USE_THEN "mono" (MP_TAC o SPECL [`s':real`; `t:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `Kk * s' rpow (&9 / &4) <= Kk * t rpow (&9 / &4) /\
                    &0 <= Kk * t rpow (&9 / &4)` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_LE2 THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_POS_LE THEN
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < tt pow 8 * t /\ tt pow 8 * t <= t / &2` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT] THEN
        SUBGOAL_THEN `tt pow 8 <= inv(&2)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tt pow 1` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC;
            ASM_REWRITE_TAC[REAL_POW_1]];
          ALL_TAC] THEN
        SUBGOAL_THEN `tt pow 8 * t <= inv(&2) * t` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
        ALL_TAC] THEN
      USE_THEN "step" (MP_TAC o SPECL [`tt pow 8 * t`; `t:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(tt pow 8 * t) / t = tt pow 8` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[HMRC_RPOW_TT; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(A * tt pow 32) * (psi:real->real) t <= tt pow 17 * psi t` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN USE_THEN "nn" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `E * t rpow (&9 / &4) + Kk * tt pow 18 * t rpow (&9 / &4) =
                    tt pow 17 * Kk * t rpow (&9 / &4)` ASSUME_TAC THENL
       [UNDISCH_TAC `E + Kk * tt pow 18 = Kk * tt pow 17` THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "it") THEN X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  USE_THEN "it" (MP_TAC o SPEC `rho:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`tt:real`; `n:num`; `rho:real`; `R1:real`] HMRC_ITER_EXP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= (psi:real->real) R1` ASSUME_TAC THENL
   [USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ABBREV_TAC `X = (psi:real->real) R1 + Kk * R1 rpow (&9 / &4)` THEN
  ABBREV_TAC `w = (rho / R1) rpow (&17 / &8)` THEN
  SUBGOAL_THEN `&0 <= X /\ X <= c1 * ((psi:real->real) R1 + E * R1 rpow (&9 / &4)) /\
                &0 <= Kk * rho rpow (&9 / &4) /\ &0 <= w`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
      EXPAND_TAC "X" THEN EXPAND_TAC "Kk" THEN
      SUBGOAL_THEN `&1 * (psi:real->real) R1 <= c1 * psi R1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
      EXPAND_TAC "w" THEN MATCH_MP_TAC RPOW_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * (tt pow 17) pow n * X` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * (inv(tt pow 17) * w) * X` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * (inv(tt pow 17) * w) * c1 * ((psi:real->real) R1 + E * R1 rpow (&9 / &4))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The variances of the weak partials decay like rho^(17/8), uniformly on    *)
(* compact subsets.                                                          *)
(* ========================================================================= *)

let HMRC_E0_ARITH = prove
 (`!r Ch Cm D.
     &0 < r /\ r <= &1 /\ &0 <= Ch /\ &0 <= Cm /\ &0 <= D /\ D <= Cm * r rpow (&3 / &2)
     ==> ((Ch * r rpow (&3 / &4)) pow 2 + Ch * r rpow (&3 / &4)) * D <=
         ((Ch pow 2 + Ch) * Cm) * r rpow (&9 / &4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r rpow (&3 / &2) = r rpow (&3 / &4) * r rpow (&3 / &4) /\
                r rpow (&9 / &4) = r rpow (&3 / &4) * r rpow (&3 / &4) * r rpow (&3 / &4)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r rpow (&3 / &4) /\ r rpow (&3 / &4) <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 rpow (&3 / &4)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        REWRITE_TAC[RPOW_ONE; REAL_LE_REFL]]];
    ALL_TAC] THEN
  ABBREV_TAC `p = r rpow (&3 / &4)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((Ch * p) pow 2 + Ch * p) * (Cm * (p * p))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ch pow 2 * Cm * p pow 3) * p <= (Ch pow 2 * Cm * p pow 3) * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let HMRC_PSI_LE_DIR = prove
 (`!(s:real^2->bool) (u:real^2->real^K) x R.
     open s /\ wan_w12 s u /\ &0 < R /\ ball(x,R) SUBSET s
     ==> sum(1..2) (\i. wanl_cp_var (wan_wd s i u) x R) <= &4 * wan_dir (ball(x,R)) u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> wan_wd s i (u:real^2->real^K) IN lspace (ball(x,R)) (&2) /\
                        wan_wpd (ball(x,R)) i u (wan_wd s i u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `u:real^2->real^K`] WAN_WD_WORKS) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
      MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(x:real^2,R)`; `u:real^2->real^K`; `\i. wan_wd s i (u:real^2->real^K)`]
    WAN_DIR_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ASM_SIMP_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIMINDEX_2; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`wan_wd s i (u:real^2->real^K)`; `x:real^2`; `R:real`; `x:real^2`; `R:real`;
                 `vec 0:real^K`] HMRC_VAR_LE4) THEN
  ASM_SIMP_TAC[SUBSET_REFL; VECTOR_SUB_RZERO]);;

let HMRC_PD_MORREY = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !s (u:real^2->real^K) K.
            open s /\ cm_wharmonic S G s u /\ compact K /\ K SUBSET s
            ==> ?r3 C3. &0 < r3 /\ &0 <= C3 /\ (!x. x IN K ==> cball(x,r3) SUBSET s) /\
                        !x rho. x IN K /\ &0 < rho /\ rho <= r3
                                ==> sum(1..2) (\i. wanl_cp_var (wan_wd s i u) x rho)
                                    <= C3 * rho rpow (&17 / &8)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `K:real^2->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `K:real^2->bool`] o
    MATCH_MP HMRC_HOLDER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `Ch:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "cb2") (LABEL_TAC "ho")))))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `K:real^2->bool`] o
    MATCH_MP HMRC_MORREY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `Cm:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "cb1") (LABEL_TAC "mo")))))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `A:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")) o
    MATCH_MP HMRC_PD_STEP) THEN
  MP_TAC(SPEC `A:real` HMRC_ITER_INHOM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CI:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inh"))) THEN
  ABBREV_TAC `R1 = min r1 (min r2 (&1))` THEN
  SUBGOAL_THEN `&0 < R1 /\ R1 <= r1 /\ R1 <= r2 /\ R1 <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B0 = (Ch pow 2 + Ch) * Cm` THEN
  SUBGOAL_THEN `&0 <= B0` ASSUME_TAC THENL
   [EXPAND_TAC "B0" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN K ==> cball(x,R1) SUBSET s` (LABEL_TAC "cbR") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(x:real^2,r1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "cb1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * Cm * R1 rpow (&3 / &2) + (A * B0) * R1 rpow (&9 / &4) /\
                &0 < R1 rpow (&17 / &8)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; REAL_POS];
      MATCH_MP_TAC RPOW_POS_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `R1:real` THEN
  EXISTS_TAC `CI * (&4 * Cm * R1 rpow (&3 / &2) + (A * B0) * R1 rpow (&9 / &4)) *
              inv(R1 rpow (&17 / &8))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    USE_THEN "cbR" ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `rho:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(x:real^2,R1) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,R1)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN USE_THEN "cbR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t i. &0 < t /\ t <= R1 /\ 1 <= i /\ i <= 2
                      ==> wan_wd s i (u:real^2->real^K) IN lspace (ball(x,t)) (&2)`
  (LABEL_TAC "lsx") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; WAN_WD_WORKS; DIMINDEX_2] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^2,R1)` THEN
    ASM_SIMP_TAC[SUBSET_BALL];
    ALL_TAC] THEN
  USE_THEN "inh" (MP_TAC o SPECL
   [`\t. sum(1..2) (\i. wanl_cp_var (wan_wd s i (u:real^2->real^K)) x t)`;
    `A * B0`; `R1:real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC HMRC_VAR_POS THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN REWRITE_TAC[SUBSET_REFL] THEN
      USE_THEN "lsx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s':real`; `t:real`] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HMRC_VAR_MONO4 THEN MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN USE_THEN "lsx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`rho':real`; `r:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < r /\ r <= r1 /\ r <= r2 /\ r <= &1 /\ cball(x:real^2,r) SUBSET s`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,R1)` THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
          USE_THEN "cbR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      USE_THEN "st" (MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `x:real^2`; `r:real`;
                                     `rho':real`; `Ch * r rpow (&3 / &4)`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ch * norm(y - x:real^2) rpow (&3 / &4)` THEN
        CONJ_TAC THENL
         [USE_THEN "ho" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(y:real^2) IN cball(x,r)` THEN REWRITE_TAC[IN_CBALL] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_LE2 THEN
          REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
           [UNDISCH_TAC `(y:real^2) IN cball(x,r)` THEN REWRITE_TAC[IN_CBALL; dist] THEN
            MP_TAC(ISPECL [`x:real^2`; `y:real^2`] NORM_SUB) THEN REAL_ARITH_TAC;
            CONV_TAC REAL_RAT_REDUCE_CONV]];
        ALL_TAC] THEN
      SUBGOAL_THEN `((Ch * r rpow (&3 / &4)) pow 2 + Ch * r rpow (&3 / &4)) *
                    wan_dir (ball(x,r)) (u:real^2->real^K) <= B0 * r rpow (&9 / &4)`
      ASSUME_TAC THENL
       [EXPAND_TAC "B0" THEN MATCH_MP_TAC HMRC_E0_ARITH THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUBSET THEN
          EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,r)` THEN
          ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
          USE_THEN "mo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `A * ((Ch * r rpow (&3 / &4)) pow 2 + Ch * r rpow (&3 / &4)) *
                    wan_dir (ball(x,r)) (u:real^2->real^K) <= A * B0 * r rpow (&9 / &4)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(rho / R1) rpow (&17 / &8) = rho rpow (&17 / &8) * inv(R1 rpow (&17 / &8))`
  SUBST1_TAC THENL [REWRITE_TAC[RPOW_DIV] THEN REWRITE_TAC[real_div]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `x:real^2`; `R1:real`] HMRC_PSI_LE_DIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "mo" (MP_TAC o SPECL [`x:real^2`; `R1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ABBREV_TAC `P1 = sum(1..2) (\i. wanl_cp_var (wan_wd s i (u:real^2->real^K)) x R1)` THEN
  ABBREV_TAC `Z = rho rpow (&17 / &8) * inv(R1 rpow (&17 / &8))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Z` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `CI * (P1 + (A * B0) * R1 rpow (&9 / &4)) * Z` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `CI * (&4 * Cm * R1 rpow (&3 / &2) + (A * B0) * R1 rpow (&9 / &4)) * Z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    EXPAND_TAC "Z" THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The weak partial derivatives of a continuous weakly harmonic map are a.e. *)
(* equal to Hoelder maps (exponent 1/16) on small balls around the points of *)
(* a compact set (Campanato), so they are locally essentially bounded.       *)
(* ========================================================================= *)

let HMRC_WD_HOLDER = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !s (u:real^2->real^K) K.
            open s /\ cm_wharmonic S G s u /\ compact K /\ K SUBSET s
            ==> ?r4 C4. &0 < r4 /\ &0 <= C4 /\ (!x. x IN K ==> ball(x,r4) SUBSET s) /\
                        !a i. a IN K /\ 1 <= i /\ i <= 2
                              ==> ?w. (!x y. x IN ball(a,r4) /\ y IN ball(a,r4)
                                             ==> norm(w x - w y) <=
                                                 C4 * norm(x - y) rpow (&1 / &16)) /\
                                      negligible {x | x IN ball(a,r4) /\
                                                      ~(wan_wd s i u x = w x)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `K:real^2->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `K:real^2->bool`] HMRC_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `K2:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")))))) THEN
  SUBGOAL_THEN `!x:real^2. x IN K ==> x IN K2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "nb" MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `K2:real^2->bool`] o
    MATCH_MP HMRC_PD_MORREY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` (X_CHOOSE_THEN `C3:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "cb") (LABEL_TAC "pm")))))) THEN
  MP_TAC(SPEC `&1 / &16` (REWRITE_RULE[WAN_CAMPANATO_STATEMENT]
    (ISPECL [`(:2)`; `(:K)`] WAN_CAMPANATO))) THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ca"))) THEN
  ABBREV_TAC `R = min d0 r3` THEN
  SUBGOAL_THEN `&0 < R /\ R <= d0 /\ R <= r3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt C3 /\ &0 <= CC * sqrt C3` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt C3` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN K ==> ball(x,R) SUBSET s` (LABEL_TAC "bR") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(x:real^2,r3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "cb" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`R / &2`; `CC * sqrt C3`] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(x:real^2,R)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      USE_THEN "bR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `i:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(a:real^2,R) SUBSET s` ASSUME_TAC THENL
   [USE_THEN "bR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2 rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,R)
                               ==> x IN K2 /\ rho <= r3`
  (LABEL_TAC "in") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET_BALLS] THEN STRIP_TAC THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`x:real^2`; `a:real^2`] DIST_POS_LE) THEN DISCH_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "nb" MATCH_MP_TAC THEN EXISTS_TAC `a:real^2` THEN ASM_SIMP_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= 2
                    ==> wan_wd s j (u:real^2->real^K) IN lspace (ball(a,R)) (&2)`
  (LABEL_TAC "ls") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; WAN_WD_WORKS; DIMINDEX_2];
    ALL_TAC] THEN
  USE_THEN "ca" (MP_TAC o SPECL [`a:real^2`; `R:real`; `wan_wd s i (u:real^2->real^K)`;
                                 `sqrt C3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `rho:real`] THEN STRIP_TAC THEN
    USE_THEN "in" (MP_TAC o SPECL [`x:real^2`; `rho:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[GSYM wanl_cp_mean] THEN REWRITE_TAC[GSYM wanl_cp_var] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..2) (\j. wanl_cp_var (wan_wd s j (u:real^2->real^K)) x rho)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&0 <= wanl_cp_var (wan_wd s 1 (u:real^2->real^K)) x rho /\
                    &0 <= wanl_cp_var (wan_wd s 2 (u:real^2->real^K)) x rho` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC HMRC_VAR_POS THEN
        MAP_EVERY EXISTS_TAC [`a:real^2`; `R:real`] THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "ls" MATCH_MP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUM_2] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2] THEN USE_THEN "pm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^2->real^K` THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[]);;

let HMRC_WD_LOCBOUND = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !s (u:real^2->real^K) a i.
            open s /\ cm_wharmonic S G s u /\ a IN s /\ 1 <= i /\ i <= 2
            ==> ?r M N. &0 < r /\ ball(a,r) SUBSET s /\ negligible N /\
                        !x. x IN ball(a,r) /\ ~(x IN N) ==> norm(wan_wd s i u x) <= M`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `{a:real^2}`] o
    MATCH_MP HMRC_WD_HOLDER) THEN
  ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `r4:real` (X_CHOOSE_THEN `C4:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL [`a:real^2`; `i:num`])))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real^K` (CONJUNCTS_THEN2 (LABEL_TAC "hw") ASSUME_TAC)) THEN
  SUBGOAL_THEN `ball(a:real^2,r4) SUBSET s` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`r4:real`; `norm((w:real^2->real^K) a) + C4 * r4 rpow (&1 / &16)`;
    `{x | x IN ball(a,r4) /\ ~(wan_wd s i (u:real^2->real^K) x = w x)}`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd s i (u:real^2->real^K) x = w x` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((w:real^2->real^K) x - w a) <= C4 * norm(x - a) rpow (&1 / &16)`
  ASSUME_TAC THENL
   [USE_THEN "hw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `C4 * norm(x - a:real^2) rpow (&1 / &16) <= C4 * r4 rpow (&1 / &16)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_LE2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN ball(a,r4)` THEN REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(ISPECL [`a:real^2`; `x:real^2`] NORM_SUB) THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(NORM_ARITH `norm((w:real^2->real^K) x) <= norm(w a) + norm(w x - w a)`) THEN
  ASM_REAL_ARITH_TAC);;

