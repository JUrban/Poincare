(* ========================================================================= *)
(* Unit pc_hm_reg_smth (a unit of the harmonic map regularity chain of       *)
(* pc_hm_regularity): continuous weakly harmonic maps are smooth (CM_REG01). *)
(* The right-hand side of the weak Laplace system (HMRW_LAP_C1) is a smooth  *)
(* function of (u, du); the local Hoelder classes of pc_hm_reg_hold are      *)
(* stable under it, and WAN_SCHAUDER_2D raises the regularity by one order   *)
(* at a time, starting from HMRW_C1A.                                        *)
(* ========================================================================= *)

needs "src/pc_hm_reg_wlap.ml";;
needs "src/pc_hm_reg_hold.ml";;
needs "src/pc_wan_pot2e.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the density hmrw_fq in (p, q).                              *)
(* ------------------------------------------------------------------------- *)

let HMRS_SMOOTH_MATVEC = prove
 (`!(s:real^M->bool) (A:real^M->real^N^N) (v:real^M->real^N).
     open s /\ smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o A) /\
     smooth_map_on s v
     ==> smooth_map_on s (\z. A z ** v z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`;
                 `\(m:real^(N,N)finite_prod) (x:real^N). (matrify m:real^N^N) ** x`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
                 `v:real^M->real^N`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_MATRIX_VECTOR_MUL; o_THM; MATRIFY_VECTORIZE]);;

(* HMR_MDERIV_SMOOTH (pc_hm_reg_cov) for an arbitrary domain real^P. *)

let HMRS_MDERIV_SMOOTH = prove
 (`!V W (M:real^N->real^N^N) (w:real^P->real^N) (A:real^P->real^N).
     open V /\ open W /\ smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o M) /\
     smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\ smooth_map_on W A
     ==> smooth_map_on W ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          (\z. mderiv M (w z) (A z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. vsum(1..dimindex(:N))
                    (\k. drop(lift((A:real^P->real^N) z$k)) %
                         partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                               (M:real^N->real^N^N)) ((w:real^P->real^N) z))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^P` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; mderiv; VECTORIZE_MATRIFY; LIFT_DROP; partial_derivative] THEN
    SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o M) differentiable
                  at ((w:real^P->real^N) z)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
  SUBGOAL_THEN
   `(\z. partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               (M:real^N->real^N^N)) ((w:real^P->real^N) z)) =
    partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o M) o w`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

let HMRS_FQ_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d j.
     cm_target S G d /\ 1 <= j /\ j <= dimindex(:K)
     ==> smooth_map_on (cm_tube S d PCROSS (:real^K))
           (\z. lift(hmrw_fq S G j (fstcart z) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  ABBREV_TAC `W = cm_tube (S:real^K->bool) d PCROSS (:real^K)` THEN
  SUBGOAL_THEN `open (W:real^(K,K)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE fstcart (W:real^(K,K)finite_sum->bool) SUBSET cm_tube S d /\
                !z:real^(K,K)finite_sum. z IN W ==> fstcart z IN cm_tube S d`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (fstcart:real^(K,K)finite_sum->real^K) /\
                smooth_map_on W (sndcart:real^(K,K)finite_sum->real^K)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`W:real^(K,K)finite_sum->bool`; `\z:real^(K,K)finite_sum. z`;
                     `fstcart:real^(K,K)finite_sum->real^K`] SMOOTH_MAP_ON_LINEAR_O);
      MP_TAC(ISPECL [`W:real^(K,K)finite_sum->bool`; `\z:real^(K,K)finite_sum. z`;
                     `sndcart:real^(K,K)finite_sum->real^K`] SMOOTH_MAP_ON_LINEAR_O)] THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) (hmrw_gj (G:real^K->real^K^K) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRW_GJ_SMOOTH THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the fields along fstcart *)
  SUBGOAL_THEN
   `smooth_map_on W (\z:real^(K,K)finite_sum. hmrw_gj (G:real^K->real^K^K) j (fstcart z)) /\
    smooth_map_on W ((vectorize:real^K^K->real^(K,K)finite_prod) o
                     (\z:real^(K,K)finite_sum. jacobian (closest_point S) (at (fstcart z)))) /\
    smooth_map_on W ((vectorize:real^K^K->real^(K,K)finite_prod) o
                     (\z:real^(K,K)finite_sum. (G:real^K->real^K^K) (fstcart z))) /\
    smooth_map_on W ((vectorize:real^K^K->real^(K,K)finite_prod) o
                     (\z:real^(K,K)finite_sum.
                        matrix(frechet_derivative (hmrw_gj (G:real^K->real^K^K) j)
                                 (at (fstcart z)))))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^(K,K)finite_sum. hmrw_gj (G:real^K->real^K^K) j (fstcart z)) =
                    hmrw_gj G j o fstcart` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
      SUBGOAL_THEN
       `(vectorize:real^K^K->real^(K,K)finite_prod) o
        (\z:real^(K,K)finite_sum. jacobian (closest_point S) (at (fstcart z))) =
        ((vectorize:real^K^K->real^(K,K)finite_prod) o
         (\y. jacobian (closest_point S) (at y))) o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(vectorize:real^K^K->real^(K,K)finite_prod) o
        (\z:real^(K,K)finite_sum. (G:real^K->real^K^K) (fstcart z)) =
        ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
      SUBGOAL_THEN
       `(vectorize:real^K^K->real^(K,K)finite_prod) o
        (\z:real^(K,K)finite_sum.
           matrix(frechet_derivative (hmrw_gj (G:real^K->real^K^K) j) (at (fstcart z)))) =
        ((vectorize:real^K^K->real^(K,K)finite_prod) o
         (\y. matrix(frechet_derivative (hmrw_gj G j) (at y)))) o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; LRG_SMOOTH_JACOBIAN]];
    ALL_TAC] THEN
  (* the two second-order fields *)
  SUBGOAL_THEN
   `smooth_map_on W
      (\z:real^(K,K)finite_sum. jacobian (closest_point S) (at (fstcart z)) **
                                hmrw_gj (G:real^K->real^K^K) j (fstcart z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMRS_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on W ((vectorize:real^K^K->real^(K,K)finite_prod) o
      (\z:real^(K,K)finite_sum.
         mderiv (\y. jacobian (closest_point S) (at y)) (fstcart z)
                (hmrw_gj (G:real^K->real^K^K) j (fstcart z)))) /\
    smooth_map_on W ((vectorize:real^K^K->real^(K,K)finite_prod) o
      (\z:real^(K,K)finite_sum.
         mderiv G (fstcart z)
                (jacobian (closest_point S) (at (fstcart z)) **
                 hmrw_gj (G:real^K->real^K^K) j (fstcart z))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMRS_MDERIV_SMOOTH THENL
     [EXISTS_TAC `cm_tube (S:real^K->bool) d`; EXISTS_TAC `(:real^K)`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the density *)
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\z:real^(K,K)finite_sum.
      &2 % lift((mderiv (\y. jacobian (closest_point S) (at y)) (fstcart z)
                   (hmrw_gj (G:real^K->real^K^K) j (fstcart z)) ** sndcart z) dot
                (G (fstcart z) ** sndcart z)) +
      lift(sndcart z dot
           (mderiv G (fstcart z)
              (jacobian (closest_point S) (at (fstcart z)) ** hmrw_gj G j (fstcart z)) **
            sndcart z)) +
      &2 % lift((matrix(frechet_derivative (hmrw_gj G j) (at (fstcart z))) ** sndcart z) dot
                (G (fstcart z) ** sndcart z))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^(K,K)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[hmrw_fq; hmrm_eld; MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `linear(frechet_derivative (hmrw_gj (G:real^K->real^K^K) j)
                          (at (fstcart (z:real^(K,K)finite_sum))))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC HMRS_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[ETA_AX]) THEN
  ASM_REWRITE_TAC[ETA_AX]);;

(* ========================================================================= *)
(* The right-hand side inherits the local Hoelder class one order below the  *)
(* map, and one Schauder step.                                               *)
(* ========================================================================= *)

let HMRS_RHS_HK = prove
 (`!S (G:real^K->real^K^K) d (B:real^2->bool) (u:real^2->real^K) n j.
     cm_target S G d /\ open B /\ (!x. x IN B ==> u x IN S) /\
     hmrh_hk (SUC n) B (&1 / &2) u /\ 1 <= j /\ j <= dimindex(:K)
     ==> hmrh_hk n B (&1 / &2)
           (\x. lift(inv(&2) * sum(1..2) (\i. hmrw_fq S G j (u x) (partial_derivative i u x))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `&0 < &1 / &2 /\ &1 / &2 <= &1` STRIP_ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `hmrh_hk n B (&1 / &2) (u:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRH_HK_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> hmrh_hk n B (&1 / &2)
              (\x. lift(hmrw_fq S G j ((u:real^2->real^K) x) (partial_derivative i u x)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `B:real^2->bool`; `&1 / &2`;
                   `cm_tube (S:real^K->bool) d PCROSS (:real^K)`;
                   `\x. pastecart ((u:real^2->real^K) x) (partial_derivative i u x)`;
                   `\z:real^(K,K)finite_sum. lift(hmrw_fq S G j (fstcart z) (sndcart z))`]
      HMRH_HK_COMPOSE) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV];
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN ASM SET_TAC[];
      MATCH_MP_TAC HMRS_FQ_SMOOTH THEN ASM_MESON_TAC[];
      MATCH_MP_TAC HMRH_HK_PASTECART THEN ASM_REWRITE_TAC[ETA_AX] THEN
      UNDISCH_TAC `hmrh_hk (SUC n) B (&1 / &2) (u:real^2->real^K)` THEN
      REWRITE_TAC[hmrh_hk; DIMINDEX_2] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRH_HK_EQ THEN
  EXISTS_TAC
   `\x. inv(&2) %
        (lift(hmrw_fq S G j ((u:real^2->real^K) x) (partial_derivative 1 u x)) +
         lift(hmrw_fq S G j (u x) (partial_derivative 2 u x)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_2; LIFT_CMUL; LIFT_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC HMRH_HK_CMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HMRH_HK_ADD THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* One Schauder step for a scalar function. *)

let HMRS_SCHAUDER_STEP = prove
 (`!(a:real^2) rho (v:real^2->real) (f:real^2->real) n A.
     &0 < rho /\
     continuously_differentiable n (ball(a,rho)) (\x. lift(f x)) /\
     wan_ckal (ball(a,rho)) n (&1 / &2) rho (\x. lift(f x)) A /\
     (\x. lift(v x)) continuous_on cball(a,rho) /\
     wan_w12 (ball(a,rho)) (\x. lift(v x)) /\
     (!phi. wan_test (ball(a,rho)) phi
            ==> vsum(1..2) (\i. integral (ball(a,rho))
                   (\x. wan_dpart i phi x % wan_wd (ball(a,rho)) i (\y. lift(v y)) x)) =
                --(integral (ball(a,rho)) (\x. lift(f x * phi x))))
     ==> hmrh_hk (SUC(SUC n)) (ball(a,rho / &2)) (&1 / &2) (\x. lift(v x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?U. !x. x IN ball(a,rho) ==> abs((v:real^2->real) x) <= U` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift((v:real^2->real) x)`; `cball(a:real^2,rho)`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `&1 / &2`] (REWRITE_RULE[WAN_SCHAUDER_2D_STATEMENT] WAN_SCHAUDER_2D)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL
    [`a:real^2`; `rho:real`; `v:real^2->real`; `f:real^2->real`; `A:real`; `U:real`]))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN ball(a,rho / &2) ==> lift((w:real^2->real) x) = lift(v x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,rho / &2)`; `\x. lift((v:real^2->real) x)`;
                   `\x. lift((w:real^2->real) x)`] WAN_CONT_AE_EQ_OPEN) THEN
    REWRITE_TAC[LIFT_EQ; OPEN_BALL] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,rho)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `ball(a:real^2,rho)` THEN REWRITE_TAC[BALL_SUBSET_CBALL] THEN
        MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        EXISTS_TAC `n + 2` THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRH_HK_EQ THEN EXISTS_TAC `\x. lift((w:real^2->real) x)` THEN
  ASM_SIMP_TAC[OPEN_BALL] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  MATCH_MP_TAC HMRH_HK_FROM_HOL THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRH_CKAL_HOL THEN
  MAP_EVERY EXISTS_TAC [`n + 2`; `rho:real`; `C * (rho pow 2 * A + U)`] THEN
  ASM_REWRITE_TAC[OPEN_BALL]);;

(* One order more: from hk (n + 1) on a disc to hk (n + 2) on a smaller one. *)

let HMRS_STEP = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a r n.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ &0 < r /\ ball(a,r) SUBSET s /\
     hmrh_hk (SUC n) (ball(a,r)) (&1 / &2) u
     ==> ?r'. &0 < r' /\ ball(a,r') SUBSET s /\
              hmrh_hk (SUC(SUC n)) (ball(a,r')) (&1 / &2) u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `&0 < &1 / &2 /\ &1 / &2 <= &1` STRIP_ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2) IN ball(a,r) /\
                (!x. x IN ball(a:real^2,r) ==> (u:real^2->real^K) x IN S)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r)) (u:real^2->real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `SUC n` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HMRH_HK_CD THEN EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. ?rj. 1 <= j /\ j <= dimindex(:K)
             ==> &0 < rj /\ rj <= r /\
                 hmrh_hk (SUC(SUC n)) (ball(a,rj)) (&1 / &2)
                   (\x. lift((u:real^2->real^K) x$j))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `1 <= j /\ j <= dimindex(:K)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`;
                   `u:real^2->real^K`; `n:num`; `j:num`] HMRS_RHS_HK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL]; DISCH_TAC] THEN
    MP_TAC(ISPECL
     [`n:num`; `ball(a:real^2,r)`; `&1 / &2`;
      `\x. lift(inv(&2) * sum(1..2) (\i. hmrw_fq S G j ((u:real^2->real^K) x)
                                            (partial_derivative i u x)))`;
      `a:real^2`] HMRH_HK_CKAL) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `cball(a:real^2,rho) SUBSET s /\ ball(a:real^2,rho) SUBSET ball(a,r) /\
                  rho <= r`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,rho)` THEN
        ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
        UNDISCH_TAC `cball(a:real^2,rho) SUBSET ball(a,r)` THEN
        REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `u:real^2->real^K`; `a:real^2`; `rho:real`; `j:num`] HMRW_LAP_C1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    EXISTS_TAC `rho / &2` THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HMRS_SCHAUDER_STEP THEN
    EXISTS_TAC `\x. inv(&2) * sum(1..2) (\i. hmrw_fq S G j ((u:real^2->real^K) x)
                                               (partial_derivative i u x))` THEN
    EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HMRH_HK_CD THEN EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `rr:num->real`) THEN
  MP_TAC(ISPECL [`1..dimindex(:K)`; `rr:num->real`] HMRH_FINITE_MIN_INV) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r' = inv(&1 + sum(1..dimindex(:K)) (\j. inv((rr:num->real) j)))` THEN
  STRIP_TAC THEN EXISTS_TAC `r':real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(a:real^2,r') SUBSET ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(rr:num->real) 1` THEN
    SUBGOAL_THEN `1 <= 1 /\ 1 <= dimindex(:K)` MP_TAC THENL
     [REWRITE_TAC[LE_REFL; DIMINDEX_GE_1]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HMRH_HK_COMPONENTWISE THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC HMRH_HK_SUBSET THEN
  EXISTS_TAC `ball(a:real^2,(rr:num->real) j)` THEN
  ASM_SIMP_TAC[OPEN_BALL; SUBSET_BALL]);;

(* ========================================================================= *)
(* All orders, smoothness, CM_REG01.                                        *)
(* ========================================================================= *)

let HMRS_BASE = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ a IN s
     ==> ?r. &0 < r /\ ball(a,r) SUBSET s /\ hmrh_hk (SUC 0) (ball(a,r)) (&1 / &2) u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `a:real^2`] HMRW_C1A) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
  MATCH_MP_TAC HMRH_HK_FROM_HOL THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?i. l = [i:num]` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `LENGTH(l:num list) = 1` THEN
    REWRITE_TAC[ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:2)) [i:num]` THEN
  REWRITE_TAC[ALL; DIMINDEX_2; iterated_partial] THEN STRIP_TAC THEN
  MATCH_MP_TAC HMRH_HOL_UNIFORM THEN EXISTS_TAC `L:real` THEN ASM_SIMP_TAC[OPEN_BALL]);;

let HMRS_ALL_ORDERS = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ open s /\ cm_wharmonic S G s u
     ==> !n a. a IN s
               ==> ?r. &0 < r /\ ball(a,r) SUBSET s /\
                       hmrh_hk (SUC n) (ball(a,r)) (&1 / &2) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRS_BASE THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HMRS_STEP THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `r:real`] THEN
  ASM_REWRITE_TAC[]);;

let HMRS_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ open s /\ cm_wharmonic S G s u ==> smooth_map_on s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`] HMRS_ALL_ORDERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN] THEN
  X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `SUC n` THEN
  CONJ_TAC THENL
   [ARITH_TAC;
    MATCH_MP_TAC HMRH_HK_CD THEN EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[OPEN_BALL]]);;

(* REG01: continuous weakly harmonic maps are harmonic (smooth). *)

let CM_REG01 = prove
 (`!kk:K->bool. CM_REG01_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_REG01_STATEMENT] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cm_harmonic] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMRS_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
  ASM_REWRITE_TAC[]);;

