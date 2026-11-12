(* ========================================================================= *)
(* Unit pc_p3_s13close (Part 3 proofs; MT Ch 13, Thm 13.2(4)):              *)
(* the closeness clause of P3_THM_13_2_STATEMENT.  For necks gN with        *)
(* dl -> 0 the rescaled surgery metrics h^-2 gS converge to g0 in every C^m *)
(* uniformly on compact sets: where s1 > 2 gS is a conformal multiple of    *)
(* g0 with factor tending to 1 in C^inf (P2CI_LCK_COMPACT of             *)
(* pc_p2c_cgcinf); where s1 < 3 the blend a T + b g0 is controlled by a     *)
(* Leibniz bound of every order, with a -> alpha(s1) and b -> 0 in C^inf    *)
(* and T the pulled-back neck metric, at C^k distance at most dl from g0.   *)
(* The modulus p3s_md is then obtained by contradiction (P3S_MD).            *)
(*                                                                           *)
(* Contents: convergence in one variable; the neck bound and the cap region; *)
(* the blend region; compact sets and the modulus.                           *)
(* ========================================================================= *)

needs "src/pc_p3_s13pinch.ml";;
needs "src/pc_p2c_cgcinf.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* C-infinity convergence in one variable.  With c_n -> 0 and               *)
(* dl_n -> 0: f_n = c_n cutoff_flat(s/q) -> 0, phi_n -> 1, phi_n alpha ->   *)
(* alpha and phi_n (alpha + (1 - alpha)(1 - dl_n)) -> 1 near every point,  *)
(* in the sense of p2ci_near (uniform bounds on all jets plus uniform     *)
(* convergence).                                                            *)
(* ------------------------------------------------------------------------- *)

let P3S_JETN_CONST = prove
 (`!m (c:real^P) (y:real^M). pde_jetn m (\z:real^M. c) y = norm c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jetn; P2CT_ITERATED_PARTIAL_CONST] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; NORM_0] THEN
  SIMP_TAC[SUM_DELTA; PDE_INDEX_LISTS_NIL]);;

let P3S_NEAR_CONSTSEQ = prove
 (`!(z0:real^M) (k:num->real^N) k0.
     (!e. &0 < e ==> ?N. !n. N <= n ==> norm(k n - k0) < e)
     ==> p2ci_near z0 (\n z. k n) (\z. k0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ci_near] THEN EXISTS_TAC `&1` THEN
  REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST; P3S_JETN_CONST] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MAP_EVERY EXISTS_TAC [`norm(k0:real^N) + &1`; `N:num`] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[]]);;

let P3S_NEAR_SCALE = prove
 (`!(z0:real^M) (c:num->real) (Fm:real^M->real^N) r.
     &0 < r /\ smooth_map_on (ball(z0,r)) Fm /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(c n) < e)
     ==> p2ci_near z0 (\n z. c n % Fm z) (\z. vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(a:real^1) (v:real^N). drop a % v`; `&1`; `z0:real^M`;
                 `\n:num z:real^M. lift(c n)`; `\z:real^M. vec 0:real^1`;
                 `\n:num. (Fm:real^M->real^N)`; `Fm:real^M->real^N`] P2CI_NEAR_BILINEAR) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; REAL_POS; LIFT_DROP; DROP_VEC; VECTOR_MUL_LZERO] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_MUL_LID] THEN REPEAT GEN_TAC THEN
      REWRITE_TAC[GSYM NORM_1] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`z0:real^M`; `\n:num. lift(c n)`; `vec 0:real^1`] P3S_NEAR_CONSTSEQ) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[ETA_AX]]);;

let P3S_NEAR_FSEQ = prove
 (`!(c:num->real) q (z0:real^1).
     ~(q = &0) /\ (!e. &0 < e ==> ?N. !n. N <= n ==> abs(c n) < e)
     ==> p2ci_near z0 (\n. lift o p3s_f (c n) q o drop) (\z. vec 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC [`\n z. (c:num->real) n % (lift o p3s_f (&1) q o drop) z`;
                        `\z:real^1. vec 0:real^1`; `&1`; `0`] THEN
  REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3S_NEAR_SCALE THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[P3S_F_SMOOTH; SUBSET_UNIV];
    REWRITE_TAC[o_THM; p3s_f; GSYM LIFT_CMUL; REAL_MUL_LID]]);;

let P3S_NEAR_COMPOSE_FIXED = prove
 (`!(z0:real^M) (As:num->real^M->real^N) A (E:real^N->real^P) r.
     p2ci_near z0 As A /\ &0 < r /\ smooth_map_on (ball(A z0,r)) E
     ==> p2ci_near z0 (\n. E o As n) (E o A)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]);;

let P3S_EXPM1_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o (\t. exp(--(&2 * t)) - &1) o drop)`,
  MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST] THEN
  MATCH_MP_TAC P2C_S1_EXP THEN REWRITE_TAC[OPEN_UNIV] THEN
  SUBGOAL_THEN `(\t:real. --(&2 * t)) = (\t. --(&2) * (\u. u) t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_CMUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_ID]);;

let P3S_NEAR_PHISEQ = prove
 (`!(c:num->real) q A0 r0 (z0:real^1).
     &0 < q /\ &0 < r0 /\ (!e. &0 < e ==> ?N. !n. N <= n ==> abs(c n) < e)
     ==> p2ci_near z0 (\n. lift o (\s. p3s_phi (c n) q A0 r0 s - &1) o drop) (\z. vec 0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `E = lift o (\t. exp(--(&2 * t)) - &1) o drop` THEN
  SUBGOAL_THEN `!r. smooth_map_on (ball(vec 0:real^1,r)) (E:real^1->real^1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[P3S_EXPM1_SMOOTH; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^1->real^1) (vec 0) = vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[o_THM; DROP_VEC; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0;
                                   REAL_SUB_REFL; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2ci_near (z0:real^1) (\n. (E:real^1->real^1) o (lift o p3s_f (c n) q o drop))
                          ((E:real^1->real^1) o (\z:real^1. vec 0:real^1))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_NEAR_COMPOSE_FIXED THEN EXISTS_TAC `&1` THEN
    ASM_SIMP_TAC[P3S_NEAR_FSEQ; REAL_LT_IMP_NZ; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2ci_near (z0:real^1)
                  (\n. (E:real^1->real^1) o (\z:real^1. (c:num->real) n % lift(p3s_f (&1) q (A0 + &4))))
                  ((E:real^1->real^1) o (\z:real^1. vec 0:real^1))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_NEAR_COMPOSE_FIXED THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC P3S_NEAR_SCALE THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `smooth_map_on (ball(z0:real^1,&1)) (lift o p3s_beta A0 r0 o drop) /\
                smooth_map_on (ball(z0:real^1,&1)) (lift o (\s. &1 - p3s_beta A0 r0 s) o drop)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2C_S1_SUB THEN ASM_REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^1`; `\n:num. (E:real^1->real^1) o (lift o p3s_f ((c:num->real) n) q o drop)`;
                 `(E:real^1->real^1) o (\z:real^1. vec 0:real^1)`; `lift o p3s_beta A0 r0 o drop`; `&1`]
         P2CI_NEAR_SMUL) THEN
  MP_TAC(ISPECL [`z0:real^1`;
                 `\n:num. (E:real^1->real^1) o (\z:real^1. (c:num->real) n % lift(p3s_f (&1) q (A0 + &4)))`;
                 `(E:real^1->real^1) o (\z:real^1. vec 0:real^1)`;
                 `lift o (\s. &1 - p3s_beta A0 r0 s) o drop`; `&1`] P2CI_NEAR_SMUL) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n z. drop((lift o p3s_beta A0 r0 o drop) z) %
           ((E:real^1->real^1) o (lift o p3s_f ((c:num->real) n) q o drop)) (z:real^1) +
           drop((lift o (\s. &1 - p3s_beta A0 r0 s) o drop) z) %
           ((E:real^1->real^1) o (\z:real^1. c n % lift(p3s_f (&1) q (A0 + &4)))) z`;
    `\z. drop((lift o p3s_beta A0 r0 o drop) z) % ((E:real^1->real^1) o (\z:real^1. vec 0:real^1)) (z:real^1) +
         drop((lift o (\s. &1 - p3s_beta A0 r0 s) o drop) z) %
         ((E:real^1->real^1) o (\z:real^1. vec 0:real^1)) z`;
    `&1`; `0`] THEN
  REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_ADD THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM; VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  EXPAND_TAC "E" THEN
  REWRITE_TAC[o_THM; LIFT_DROP; DROP_CMUL; p3s_phi; p3s_f; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REPEAT STRIP_TAC THEN
  REAL_ARITH_TAC);;

let P3S_NEAR_ADD_CONST = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f k.
     p2ci_near z0 Fs f ==> p2ci_near z0 (\n z. Fs n z + k) (\z. f z + k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN
  REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST]);;

let P3S_NEAR_MUL1 = prove
 (`!(z0:real^M) (As:num->real^M->real^1) A (Bs:num->real^M->real^N) B.
     p2ci_near z0 As A /\ p2ci_near z0 Bs B
     ==> p2ci_near z0 (\n z. drop(As n z) % Bs n z) (\z. drop(A z) % B z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(a:real^1) (v:real^N). drop a % v`; `&1`; `z0:real^M`;
                 `As:num->real^M->real^1`; `A:real^M->real^1`;
                 `Bs:num->real^M->real^N`; `B:real^M->real^N`] P2CI_NEAR_BILINEAR) THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL; REAL_POS] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_MUL_LID] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM NORM_1] THEN REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

let P3S_NEAR_PHI1 = prove
 (`!(c:num->real) q A0 r0 (z0:real^1).
     &0 < q /\ &0 < r0 /\ (!e. &0 < e ==> ?N. !n. N <= n ==> abs(c n) < e)
     ==> p2ci_near z0 (\n. lift o p3s_phi (c n) q A0 r0 o drop) (lift o (\s. &1) o drop)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num->real`; `q:real`; `A0:real`; `r0:real`; `z0:real^1`]
         P3S_NEAR_PHISEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P3S_NEAR_ADD_CONST) THEN
  DISCH_THEN(MP_TAC o SPEC `lift(&1)`) THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_ADD; VECTOR_ADD_LID] THEN
  REWRITE_TAC[REAL_SUB_ADD]);;

let P3S_NEAR_KSEQ = prove
 (`!(dl:num->real) (z0:real^1).
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e)
     ==> p2ci_near z0
           (\n. lift o (\s. p3s_alpha s + (&1 - p3s_alpha s) * (&1 - dl n)) o drop)
           (lift o (\s. &1) o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (ball(z0:real^1,&1)) (lift o (\s. &1 - p3s_alpha s) o drop)`
  ASSUME_TAC THENL
   [MP_TAC P3S_ALPHA THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC P2C_S1_SUB THEN ASM_REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^1`; `\n:num. --((dl:num->real) n)`;
                 `lift o (\s. &1 - p3s_alpha s) o drop`; `&1`] P3S_NEAR_SCALE) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_ABS_NEG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P3S_NEAR_ADD_CONST) THEN
  DISCH_THEN(MP_TAC o SPEC `lift(&1)`) THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_ADD; GSYM LIFT_CMUL; VECTOR_ADD_LID; LIFT_EQ] THEN
  REAL_ARITH_TAC);;

let P3S_NEAR_ASEQ = prove
 (`!(c:num->real) q A0 r0 (z0:real^1).
     &0 < q /\ &0 < r0 /\ (!e. &0 < e ==> ?N. !n. N <= n ==> abs(c n) < e)
     ==> p2ci_near z0
           (\n. lift o (\s. p3s_phi (c n) q A0 r0 s * p3s_alpha s - p3s_alpha s) o drop)
           (lift o (\s. &0) o drop)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num->real`; `q:real`; `A0:real`; `r0:real`; `z0:real^1`]
         P3S_NEAR_PHISEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^1`; `\n:num. lift o (\s. p3s_phi ((c:num->real) n) q A0 r0 s - &1) o drop`;
                 `\z:real^1. vec 0:real^1`; `lift o p3s_alpha o drop`; `&1`] P2CI_NEAR_SMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN MP_TAC P3S_ALPHA THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; GSYM LIFT_CMUL; VECTOR_MUL_RZERO; LIFT_EQ;
              LIFT_NUM] THEN
  REAL_ARITH_TAC);;

let P3S_NEAR_BSEQ = prove
 (`!(c:num->real) (dl:num->real) q A0 r0 (z0:real^1).
     &0 < q /\ &0 < r0 /\ (!e. &0 < e ==> ?N. !n. N <= n ==> abs(c n) < e) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e)
     ==> p2ci_near z0
           (\n. lift o (\s. p3s_phi (c n) q A0 r0 s *
                            (p3s_alpha s + (&1 - p3s_alpha s) * (&1 - dl n)) - &1) o drop)
           (lift o (\s. &0) o drop)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num->real`; `q:real`; `A0:real`; `r0:real`; `z0:real^1`]
         P3S_NEAR_PHI1) THEN
  MP_TAC(ISPECL [`dl:num->real`; `z0:real^1`] P3S_NEAR_KSEQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^1`; `\n:num. lift o p3s_phi ((c:num->real) n) q A0 r0 o drop`;
    `lift o (\s:real. &1) o drop`;
    `\n:num. lift o (\s. p3s_alpha s + (&1 - p3s_alpha s) * (&1 - (dl:num->real) n)) o drop`;
    `lift o (\s:real. &1) o drop`] P3S_NEAR_MUL1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP P2CI_NEAR_TO_ZERO) THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; VECTOR_MUL_LID; GSYM LIFT_CMUL; GSYM LIFT_SUB;
              VECTOR_SUB_REFL] THEN
  REWRITE_TAC[LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The neck bound for the pulled-back neck metric T_n (C^k                  *)
(* distance to g0 at most dl^2 where s1 < 3), uniform convergence extracted *)
(* from p2ci_near, one-dimensional families composed with s1, and the       *)
(* local convergence of h^-2 gS to g0 in every C^m near points with s1 > 2 *)
(* (the cap and the tip, where gS is a conformal multiple of g0).          *)
(* ========================================================================= *)

let P3S_MPULLBACK_CMUL = prove
 (`!(f:real^N->real^N) (G:real^N->real^N^N) c z.
     mpullback f (\y. c %% G y) z = c %% mpullback f G z`,
  REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P3S_TN_BOUND = prove
 (`!g0 A0 dl h (gN:real^3->real^3^3) k (y:real^3).
     p3_std_initial g0 A0 /\ &0 < dl /\ dl <= &1 / &4 /\ &0 < h /\ k <= rfs_kreg dl /\
     metric_field (rfs_neck_dom dl) gN /\
     rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                  (\y. inv(h pow 2) %% gN y) /\
     --(inv dl) < A0 + &4 - p3_std_dist g0 y /\ A0 + &4 - p3_std_dist g0 y < &3
     ==> lck_dist2 k g0 (\z. inv(h pow 2) %% mpullback (p3_std_nc g0 A0) gN z) y
         <= dl pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&4 <= inv dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &4)` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `--(inv dl)`; `&3`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `W = {x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x < &3}` THEN
  ABBREV_TAC `Ann = {y:real^3 | exp(--(inv dl) / sqrt(&2)) < norm y /\
                                norm y < exp(&3 / sqrt(&2))}` THEN
  SUBGOAL_THEN `open(W:real^3->bool) /\ open(Ann:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Ann SUBSET rfs_neck_dom dl` ASSUME_TAC THENL
   [EXPAND_TAC "Ann" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(MP_TAC o MATCH_MP P3S_ANN_GEN) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[P3S_NECK_DOM_S; GSYM P3S_SY_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Ann (cylinder_flow (&0)) /\
                metric_field Ann (\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_SIMP_TAC[P3S_NECK_CYL_FIELD] THEN MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; ETA_AX; REAL_LT_INV_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `g0:real^3->real^3^3`;
                 `mpullback (p3_std_nc g0 A0) (cylinder_flow (&0))`;
                 `\z:real^3. inv(h pow 2) %% mpullback (p3_std_nc g0 A0) (gN:real^3->real^3^3) z`;
                 `mpullback (p3_std_nc g0 A0) (\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y)`;
                 `W:real^3->bool`; `y:real^3`] LCK_DIST2_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P3S_MPULLBACK_CMUL] THEN X_GEN_TAC `z:real^3` THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[p3_std_initial]) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `Ann:real^3->bool`; `W:real^3->bool`; `p3_std_nc g0 A0`;
                 `p3s_ncinv g0 A0`; `cylinder_flow (&0)`;
                 `\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y`; `y:real^3`] LCK_DIST2_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`Ann:real^3->bool`; `W:real^3->bool`; `p3_std_nc g0 A0`;
                 `p3s_ncinv g0 A0`; `y:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_exists o concl) o
      REWRITE_RULE[rfs_close_on] o check (can (find_term (fun t -> try fst(dest_const t) =
        "rfs_close_on" with Failure _ -> false)) o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                (\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y) (p3_std_nc g0 A0 y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_SIMP_TAC[P3S_NECK_CYL_FIELD] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; ETA_AX; REAL_LT_INV_EQ; REAL_POW_LT];
      ASM SET_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                    ASM_SIMP_TAC[REAL_LT_IMP_LE]]]);;

let P3S_NEAR_UNIF = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f.
     p2ci_near z0 Fs f
     ==> ?r. &0 < r /\
             !e. &0 < e ==> ?N. !n y. N <= n /\ y IN ball(z0,r) ==> norm(Fs n y - f y) < e`,
  REWRITE_TAC[p2ci_near] THEN MESON_TAC[]);;

let P3S_NEAR_S1 = prove
 (`!g0 A0 (Fs:num->real^1->real^1) f (z0:real^3).
     p3_std_initial g0 A0 /\ ~(z0 = vec 0) /\
     p2ci_near (lift(A0 + &4 - p3_std_dist g0 z0)) Fs f
     ==> p2ci_near z0 (\n. Fs n o (\x. lift(A0 + &4 - p3_std_dist g0 x)))
                      (f o (\x. lift(A0 + &4 - p3_std_dist g0 x)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `norm(z0:real^3)` THEN
  ASM_REWRITE_TAC[NORM_POS_LT] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_SIMP_TAC[P3S_S1_SMOOTH] THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[DIST_0] THEN REAL_ARITH_TAC);;

let P3S_NEAR_QSEQ = prove
 (`!(c:num->real) (dl:num->real) q A0 r0 (z0:real^1).
     &0 < q /\ &0 < r0 /\ (!e. &0 < e ==> ?N. !n. N <= n ==> abs(c n) < e) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e)
     ==> p2ci_near z0 (\n. lift o (\s. p3s_phi (c n) q A0 r0 s * (&1 - dl n)) o drop)
                      (lift o (\s. &1) o drop)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num->real`; `q:real`; `A0:real`; `r0:real`; `z0:real^1`]
         P3S_NEAR_PHI1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`z0:real^1`; `\n:num. lift(&1 - (dl:num->real) n)`;
                 `lift(&1)`] P3S_NEAR_CONSTSEQ)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^1`; `\n:num. lift o p3s_phi ((c:num->real) n) q A0 r0 o drop`;
                 `lift o (\s:real. &1) o drop`;
                 `\n:num z:real^1. lift(&1 - (dl:num->real) n)`;
                 `\z:real^1. lift(&1)`] P3S_NEAR_MUL1) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; GSYM LIFT_CMUL; REAL_MUL_LID]);;

let P3S_CAP_METRIC_NEAR = prove
 (`!g0 A0 q C0 r0 (dl:num->real) (h:num->real) (gN:num->real^3->real^3^3) (z0:real^3) S.
     p3_std_initial g0 A0 /\ &0 < q /\ &0 < r0 /\ &0 < A0 /\
     metric_field (:real^3) g0 /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(C0 * dl n) < e) /\
     {z:real^3 | &2 < A0 + &4 - p3_std_dist g0 z} = S /\ open S /\ z0 IN S /\
     (!n z. z IN S
            ==> inv(h n pow 2) %% p3s_gs g0 A0 (C0 * dl n) q r0 (dl n) (h n) (gN n) z =
                (p3s_phi (C0 * dl n) q A0 r0 (A0 + &4 - p3_std_dist g0 z) * (&1 - dl n)) %%
                g0 z)
     ==> p2ci_near (z0:real^3)
           (\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                (\z. inv(h n pow 2) %%
                     p3s_gs g0 A0 (C0 * dl n) q r0 (dl n) (h n) (gN n) z))
           (vectorize o g0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. smooth_map_on (ball(z0:real^3,r))
                  ((vectorize:real^3^3->real^(3,3)finite_prod) o (g0:real^3->real^3^3))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real^3->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z0:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `z0:real^3 = vec 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0 / &2`] P3S_TIP_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`\n:num. C0 * (dl:num->real) n`; `dl:num->real`; `q:real`; `A0:real`;
                   `r0:real`; `lift(A0 + &4)`] P3S_NEAR_QSEQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP P3S_NEAR_UNIF) THEN
    DISCH_THEN(X_CHOOSE_THEN `rq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QU"))) THEN
    MP_TAC(BETA_RULE(ISPECL [`vec 0:real^3`;
      `\n:num. lift(p3s_phi (C0 * (dl:num->real) n) q A0 r0 (A0 + &4) * (&1 - dl n))`;
      `lift(&1)`] P3S_NEAR_CONSTSEQ)) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `e:real` THEN DISCH_TAC THEN REMOVE_THEN "QU" (MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_THEN(fun th -> X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`n:num`; `lift(A0 + &4)`] th)) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; o_THM; LIFT_DROP];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`vec 0:real^3`;
      `\n:num z:real^3. lift(p3s_phi (C0 * (dl:num->real) n) q A0 r0 (A0 + &4) * (&1 - dl n))`;
      `\z:real^3. lift(&1)`;
      `\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o (g0:real^3->real^3^3)`;
      `(vectorize:real^3^3->real^(3,3)finite_prod) o (g0:real^3->real^3^3)`] P3S_NEAR_MUL1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2CI_NEAR_CONST THEN
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01];
      ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[LIFT_DROP; VECTOR_MUL_LID; o_THM]) THEN
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\n:num z:real^3. (p3s_phi (C0 * (dl:num->real) n) q A0 r0 (A0 + &4) * (&1 - dl n)) %
                        (vectorize:real^3^3->real^(3,3)finite_prod) ((g0:real^3->real^3^3) z)`;
      `\z:real^3. (vectorize:real^3^3->real^(3,3)finite_prod) ((g0:real^3->real^3^3) z)`;
      `min r1 (p3s_rad_rinv g0 (r0 / &2))`; `0`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; LIFT_DROP; VECTOR_MUL_LID; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN S` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^3,r1) SUBSET S` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p3_std_dist g0 (z:real^3) < r0 / &2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[IN_BALL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[VECTORIZE_CMUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`C0 * (dl:num->real) n`; `q:real`; `A0:real`; `r0:real`;
                  `A0 + &4 - p3_std_dist g0 (z:real^3)`] P3S_PHI_HIGH) THEN
    MP_TAC(SPECL [`C0 * (dl:num->real) n`; `q:real`; `A0:real`; `r0:real`;
                  `A0 + &4`] P3S_PHI_HIGH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num. C0 * (dl:num->real) n`; `dl:num->real`; `q:real`; `A0:real`;
                 `r0:real`; `lift(A0 + &4 - p3_std_dist g0 (z0:real^3))`] P3S_NEAR_QSEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
    `\n:num. lift o (\s. p3s_phi (C0 * (dl:num->real) n) q A0 r0 s * (&1 - dl n)) o drop`;
    `lift o (\s:real. &1) o drop`; `z0:real^3`] P3S_NEAR_S1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^3`;
    `\n:num. (lift o (\s. p3s_phi (C0 * (dl:num->real) n) q A0 r0 s * (&1 - dl n)) o drop) o
             (\x:real^3. lift(A0 + &4 - p3_std_dist g0 x))`;
    `(lift o (\s:real. &1) o drop) o (\x:real^3. lift(A0 + &4 - p3_std_dist g0 x))`;
    `\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o (g0:real^3->real^3^3)`;
    `(vectorize:real^3^3->real^(3,3)finite_prod) o (g0:real^3->real^3^3)`] P3S_NEAR_MUL1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2CI_NEAR_CONST THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[LIFT_DROP; VECTOR_MUL_LID; o_THM]) THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n:num z:real^3.
       (p3s_phi (C0 * (dl:num->real) n) q A0 r0 (A0 + &4 - p3_std_dist g0 z) * (&1 - dl n)) %
       (vectorize:real^3^3->real^(3,3)finite_prod) ((g0:real^3->real^3^3) z)`;
    `\z:real^3. (vectorize:real^3^3->real^(3,3)finite_prod) ((g0:real^3->real^3^3) z)`;
    `r1:real`; `0`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN S` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z0:real^3,r1) SUBSET S` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[VECTORIZE_CMUL]);;


(* ========================================================================= *)
(* The blend region.  A Leibniz bound of every order for                    *)
(* a T + b G0 (T the difference of a metric Gt from G0, a and b scalar      *)
(* functions), its sequence form (P3S_BLEND_CONV: uniform C^m smallness on  *)
(* a compact set when a converges to a fixed smooth function, b to 0 and Gt *)
(* to G0), and its application to h^-2 gS where s1 < 3 (P3S_CLOSE_BODY),   *)
(* with the neck bound of the previous section.                              *)
(* ========================================================================= *)

let P3S_EVENTUALLY_UPTO = prove
 (`!(P:num->num->bool) m.
     (!i. i <= m ==> ?N. !n. N <= n ==> P i n)
     ==> ?N. !i n. i <= m /\ N <= n ==> P i n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`; `P:num->num->bool`; `0..m`] EVENTUALLY_FORALL) THEN
  REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; ARITH_RULE `~(m < 0)`] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; IN_NUMSEG; LE_0] THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

let P3S_BLEND_GEN = prove
 (`!j. ?c. &0 <= c /\
     !U (G0:real^N->real^N^N) Gt (a:real^N->real) (b:real^N->real) z.
       metric_field U G0 /\ metric_field U Gt /\
       smooth_map_on U (\z. lift(a z)) /\ smooth_map_on U (\z. lift(b z)) /\ z IN U
       ==> ltnorm2 (2 + j) G0
             (lnabla_iter 2 j G0
                (\z u. a z * (lmetric2 Gt z u - lmetric2 G0 z u) + b z * lmetric2 G0 z u)) z <=
           c * sum(0..j)
                 (\i. ltnorm2 i G0 (lnabla_iter 0 i G0 (\z u. a z)) z *
                      ltnorm2 (2 + (j - i)) G0
                        (lnabla_iter 2 (j - i) G0 (\z u. lmetric2 Gt z u - lmetric2 G0 z u)) z +
                      ltnorm2 i G0 (lnabla_iter 0 i G0 (\z u. b z)) z *
                      ltnorm2 (2 + (j - i)) G0 (lnabla_iter 2 (j - i) G0 (lmetric2 G0)) z)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`j:num`; `0 + 2`; `0`; `2`;
    `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
      (tg:real^N->(num->real^N)->real). ltprod 0 tf tg`] P3S_LEIBNIZ) THEN
  REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `&2 * c` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `Gt:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real^N->real`] P3S_SCALAR_FIELD0) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `b:real^N->real`] P3S_SCALAR_FIELD0) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `X = ltprod 0 (\z (u:num->real^N). (a:real^N->real) z)
                    (\z u. lmetric2 (Gt:real^N->real^N^N) z u - lmetric2 G0 z u)` THEN
  ABBREV_TAC `Y = ltprod 0 (\z (u:num->real^N). (b:real^N->real) z)
                    (lmetric2 (G0:real^N->real^N^N))` THEN
  SUBGOAL_THEN
   `(\z u. (a:real^N->real) z * (lmetric2 (Gt:real^N->real^N^N) z u - lmetric2 G0 z u) +
           (b:real^N->real) z * lmetric2 G0 z u) =
    (\z u. &1 * (X:real^N->(num->real^N)->real) z u + &1 * Y z u)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    REWRITE_TAC[FUN_EQ_THM; ltprod; ADD_CLAUSES; ETA_AX; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(ltensor_field 2 U (X:real^N->(num->real^N)->real) /\
     !u. smooth_map_on U (\y. lift(X y u))) /\
    (ltensor_field 2 U (Y:real^N->(num->real^N)->real) /\
     !u. smooth_map_on U (\y. lift(Y y u)))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `2 = 0 + 2` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTPROD_SMOOTH THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `2 = 0 + 2` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTPROD_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `Y:real^N->(num->real^N)->real`;
                 `&1`; `&1`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 (2 + j) G0
      (lnabla_iter 2 j G0 (\z u. (X:real^N->(num->real^N)->real) z u + Y z u)) z =
    ltnorm2 (2 + j) G0 (\y u. lnabla_iter 2 j G0 X y u + lnabla_iter 2 j G0 Y y u) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `Y:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * ltnorm2 (2 + j) G0
                     (lnabla_iter 2 j G0 (X:real^N->(num->real^N)->real)) z +
              &2 * ltnorm2 (2 + j) G0
                     (lnabla_iter 2 j G0 (Y:real^N->(num->real^N)->real)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "L" (MP_TAC o SPECL [`U:real^N->bool`; `G0:real^N->real^N^N`;
    `\z (u:num->real^N). (a:real^N->real) z`;
    `\z u. lmetric2 (Gt:real^N->real^N^N) z u - lmetric2 G0 z u`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "L" (MP_TAC o SPECL [`U:real^N->bool`; `G0:real^N->real^N^N`;
    `\z (u:num->real^N). (b:real^N->real) z`;
    `lmetric2 (G0:real^N->real^N^N)`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= c * a /\ y <= c * b ==> &2 * x + &2 * y <= (&2 * c) * a + (&2 * c) * b`) THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let P3S_SCALAR_NABLA_UNIF = prove
 (`!U K (G0:real^N->real^N^N) (f:num->real^N->real).
     open U /\ compact K /\ K SUBSET U /\ metric_field U G0 /\
     (!n. smooth_map_on U (\z. lift(f n z))) /\
     (!z. z IN K ==> p2ci_near z (\n y. lift(f n y)) (\y. vec 0))
     ==> !i e. &0 < e
               ==> ?N. !n y. N <= n /\ y IN K
                             ==> ltnorm2 i G0 (lnabla_iter 0 i G0 (\z u. f n z)) y < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\n:num y:real^N. lift(ltnorm2 i (G0:real^N->real^N^N)
                       (lnabla_iter 0 i G0 (\z (u:num->real^N). (f:num->real^N->real) n z)) y)`;
    `\y:real^N. vec 0:real^1`] P2CI_NEAR_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `0 + i`; `w:real^N`;
      `\n:num. lnabla_iter 0 i (G0:real^N->real^N^N)
                 (\z (u:num->real^N). (f:num->real^N->real) n z)`]
      P2CI_LTNORM2_NEAR) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `0`; `w:real^N`;
      `\n:num z:real^N (u:num->real^N). (f:num->real^N->real) n z`] P2CI_TNEAR_ITER) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN ANTS_TAC THENL
     [REWRITE_TAC[p2ci_tnear] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [`r:real`; `0`] THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`ball(w:real^N,r)`; `(f:num->real^N->real) n`] P3S_SCALAR_FIELD0) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
          ASM_REWRITE_TAC[];
          SIMP_TAC[]];
        REPEAT GEN_TAC THEN ASM_SIMP_TAC[]];
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3S_CONT_BOUND = prove
 (`!U K (G0:real^N->real^N^N) (f:real^N->real) m.
     open U /\ compact K /\ K SUBSET U /\ metric_field U G0 /\
     smooth_map_on U (\z. lift(f z))
     ==> ?M. !i y. i <= m /\ y IN K
                   ==> ltnorm2 i G0 (lnabla_iter 0 i G0 (\z (u:num->real^N). f z)) y <= M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. ?B. !y. y IN K
                ==> ltnorm2 i (G0:real^N->real^N^N)
                      (lnabla_iter 0 i G0 (\z (u:num->real^N). (f:real^N->real) z)) y <= B`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z (u:num->real^N). (f:real^N->real) z`] LRG_LNABLA_ITER_FIELD) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] P3S_SCALAR_FIELD0) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`i:num`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla_iter 0 i (G0:real^N->real^N^N)
                      (\z (u:num->real^N). (f:real^N->real) z)`] LRG_LTNORM2_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    DISCH_THEN(MP_TAC o ISPEC `K:real^N->bool` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y. lift(ltnorm2 i (G0:real^N->real^N^N)
                     (lnabla_iter 0 i G0 (\z (u:num->real^N). (f:real^N->real) z)) y)`;
                   `K:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `B:num->real`) THEN
  EXISTS_TAC `sum(0..m) (\i. abs((B:num->real) i))` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B:num->real) i` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((B:num->real) i)` THEN
  REWRITE_TAC[REAL_ABS_LE] THEN
  MP_TAC(ISPECL [`\i. abs((B:num->real) i)`; `m:num`; `i:num`] P2CI_SUM_TERM_LE) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

let P3S_SCALAR_SPLIT = prove
 (`!U (G0:real^N->real^N^N) (f:real^N->real) g i y.
     metric_field U G0 /\ smooth_map_on U (\z. lift(f z)) /\
     smooth_map_on U (\z. lift(g z)) /\ y IN U
     ==> ltnorm2 i G0 (lnabla_iter 0 i G0 (\z (u:num->real^N). f z)) y <=
         &2 * ltnorm2 i G0 (lnabla_iter 0 i G0 (\z (u:num->real^N). f z - g z)) y +
         &2 * ltnorm2 i G0 (lnabla_iter 0 i G0 (\z (u:num->real^N). g z)) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift((f:real^N->real) z - g z))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] P3S_SCALAR_FIELD0) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `g:real^N->real`] P3S_SCALAR_FIELD0) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z. (f:real^N->real) z - g z`] P3S_SCALAR_FIELD0) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z (u:num->real^N). (f:real^N->real) z) =
    (\z u. &1 * (\z (u:num->real^N). f z - g z) z u + &1 * (\z (u:num->real^N). g z) z u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z (u:num->real^N). (f:real^N->real) z - g z`;
                 `\z (u:num->real^N). (g:real^N->real) z`; `&1`; `&1`]
         LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z (u:num->real^N). (f:real^N->real) z - g z`] LRG_LNABLA_ITER_FIELD) THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z (u:num->real^N). (g:real^N->real) z`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ltnorm2 i G0 (\y u. lnabla_iter 0 i G0
                (\z (u:num->real^N). (f:real^N->real) z - g z) y u +
              lnabla_iter 0 i G0 (\z (u:num->real^N). (g:real^N->real) z) y u) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0 + i`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla_iter 0 i G0 (\z (u:num->real^N). (f:real^N->real) z - g z)`;
                 `lnabla_iter 0 i G0 (\z (u:num->real^N). (g:real^N->real) z)`;
                 `y:real^N`] RFA_LTNORM2_ADD_LE) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let P3S_MG_BOUND = prove
 (`!U (G0:real^N->real^N^N) l y.
     metric_field U G0 /\ y IN U
     ==> ltnorm2 (2 + l) G0 (lnabla_iter 2 l G0 (lmetric2 G0)) y <= &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC(SPEC `l:num` num_CASES) THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
           LRG_LTNORM2_METRIC) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LNABLA_ITER_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[ltnorm2] THEN ASM_SIMP_TAC[REAL_MUL_LZERO; SUM_0; REAL_POS]);;

let P3S_BLEND_SUM_BOUND = prove
 (`!(c:num->real) (X:num->num->real) m Y.
     (!j. &0 <= c j) /\ (!i j. i <= j /\ j <= m ==> X i j <= Y)
     ==> sum(0..m) (\j. c j * sum(0..j) (\i. X i j)) <=
         sum(0..m) (\j. c j * &(j + 1)) * Y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..m) (\j. (c:num->real) j * &(j + 1) * Y)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..j) (\i:num. Y:real)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; REAL_LE_REFL]];
    REWRITE_TAC[GSYM SUM_RMUL; GSYM REAL_MUL_ASSOC; REAL_LE_REFL]]);;

let P3S_BLEND_TENSOR = prove
 (`!(G0:real^N->real^N^N) Gt (a:real^N->real) b.
     (\z u. lmetric2 (\z. a z %% Gt z + (&1 - a z + b z) %% G0 z) z u - lmetric2 G0 z u) =
     (\z u. a z * (lmetric2 Gt z u - lmetric2 G0 z u) + b z * lmetric2 G0 z u)`,
  REWRITE_TAC[FUN_EQ_THM; lmetric2; MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
              DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC);;

let P3S_XARITH = prove
 (`!A A' T B M D eps.
     &0 <= A /\ A <= A' /\ &0 <= T /\ T <= eps /\ &0 <= B /\ B <= eps /\
     &0 <= M /\ M <= D
     ==> A * T + B * M <= eps * (A' + D)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= A' * eps /\ y <= eps * D ==> x + y <= eps * (A' + D)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let P3S_BLEND_POINT = prove
 (`?c. (!j. &0 <= c j) /\
       !m U (G0:real^N->real^N^N) Gt (a:real^N->real) b ainf y MA eps.
         metric_field U G0 /\ metric_field U Gt /\
         smooth_map_on U (\z. lift(a z)) /\ smooth_map_on U (\z. lift(b z)) /\
         smooth_map_on U (\z. lift(ainf z)) /\ y IN U /\
         (!i. i <= m ==> ltnorm2 i G0 (lnabla_iter 0 i G0 (\z u. a z - ainf z)) y < &1) /\
         (!i. i <= m ==> ltnorm2 i G0 (lnabla_iter 0 i G0 (\z u. ainf z)) y <= MA) /\
         (!i. i <= m ==> ltnorm2 i G0 (lnabla_iter 0 i G0 (\z u. b z)) y <= eps) /\
         lck_dist2 m G0 Gt y <= eps
         ==> lck_dist2 m G0 (\z. a z %% Gt z + (&1 - a z + b z) %% G0 z) y <=
             sum(0..m) (\j. c j * &(j + 1)) *
             (eps * ((&2 + &2 * abs MA) + &(dimindex(:N))))`,
  MP_TAC(REWRITE_RULE[SKOLEM_THM] P3S_BLEND_GEN) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:num->real` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[lck_dist2; P3S_BLEND_TENSOR] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0..m) (\j. (c:num->real) j *
      sum(0..j) (\i. ltnorm2 i G0 (lnabla_iter 0 i G0 (\z (u:num->real^N). (a:real^N->real) z)) y *
                     ltnorm2 (2 + (j - i)) G0
                       (lnabla_iter 2 (j - i) G0
                          (\z u. lmetric2 (Gt:real^N->real^N^N) z u - lmetric2 G0 z u)) y +
                     ltnorm2 i G0 (lnabla_iter 0 i G0 (\z (u:num->real^N). (b:real^N->real) z)) y *
                     ltnorm2 (2 + (j - i)) G0 (lnabla_iter 2 (j - i) G0 (lmetric2 G0)) y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `j:num` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `c:num->real`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `Gt:real^N->real^N^N`;
                               `a:real^N->real`; `b:real^N->real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P3S_BLEND_SUM_BOUND THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i:num <= m /\ j - i <= m` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `i:num <= j` THEN UNDISCH_TAC `j:num <= m` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real^N->real`] P3S_SCALAR_FIELD0) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `b:real^N->real`] P3S_SCALAR_FIELD0) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z (u:num->real^N). (a:real^N->real) z`] LRG_LNABLA_ITER_FIELD) THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z (u:num->real^N). (b:real^N->real) z`] LRG_LNABLA_ITER_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G0:real^N->real^N^N`; `lmetric2 (G0:real^N->real^N^N)`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN(MP_TAC o SPEC `j - i:num`) THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  MATCH_MP_TAC P3S_XARITH THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * ltnorm2 i G0 (lnabla_iter 0 i G0
                  (\z (u:num->real^N). (a:real^N->real) z - ainf z)) y +
                &2 * ltnorm2 i G0 (lnabla_iter 0 i G0
                  (\z (u:num->real^N). (ainf:real^N->real) z)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3S_SCALAR_SPLIT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x < &1 /\ y <= M ==> &2 * x + &2 * y <= &2 + &2 * abs M`) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lck_dist2 m G0 (Gt:real^N->real^N^N) y` THEN
    ASM_REWRITE_TAC[lck_dist2] THEN
    MP_TAC(ISPECL [`\l. ltnorm2 (2 + l) G0 (lnabla_iter 2 l G0
                      (\z u. lmetric2 (Gt:real^N->real^N^N) z u - lmetric2 G0 z u)) y`;
                   `m:num`; `j - i:num`] P2CI_SUM_TERM_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_MG_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let P3S_BLEND_CONV = prove
 (`!U K (G0:real^N->real^N^N) (Gt:num->real^N->real^N^N) (a:num->real^N->real) b ainf m.
     open U /\ compact K /\ K SUBSET U /\ metric_field U G0 /\
     (?N0. !n. N0 <= n ==> metric_field U (Gt n)) /\
     (!n. smooth_map_on U (\z. lift(a n z))) /\ (!n. smooth_map_on U (\z. lift(b n z))) /\
     smooth_map_on U (\z. lift(ainf z)) /\
     (!z. z IN K ==> p2ci_near z (\n y. lift(a n y - ainf y)) (\y. vec 0)) /\
     (!z. z IN K ==> p2ci_near z (\n y. lift(b n y)) (\y. vec 0)) /\
     (!e. &0 < e ==> ?N. !n y. N <= n /\ y IN K ==> lck_dist2 m G0 (Gt n) y < e)
     ==> !e. &0 < e
             ==> ?N. !n y. N <= n /\ y IN K
                           ==> lck_dist2 m G0
                                 (\z. a n z %% Gt n z + (&1 - a n z + b n z) %% G0 z) y < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`) (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "NA") (CONJUNCTS_THEN2 (LABEL_TAC "NB")
    (LABEL_TAC "LCK"))))))))))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  X_CHOOSE_THEN `c:num->real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PT"))
    (INST_TYPE [`:N`,`:N`] P3S_BLEND_POINT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `G0:real^N->real^N^N`;
                 `ainf:real^N->real`; `m:num`] P3S_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `MA:real` (LABEL_TAC "MA")) THEN
  ABBREV_TAC `K0 = (&2 + &2 * abs MA) + &(dimindex(:N))` THEN
  ABBREV_TAC `Cs = sum(0..m) (\j. (c:num->real) j * &(j + 1))` THEN
  SUBGOAL_THEN `&0 <= K0 /\ &0 <= Cs` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K0"; "Cs"] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `MA:real` REAL_ABS_POS) THEN
      MP_TAC(SPEC `dimindex(:N)` REAL_POS) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  ABBREV_TAC `eps1 = e / (Cs * K0 + &1)` THEN
  SUBGOAL_THEN `&0 < Cs * K0 + &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`Cs:real`; `K0:real`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps1 /\ (Cs * K0 + &1) * eps1 = e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "LCK" (MP_TAC o SPEC `eps1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `G0:real^N->real^N^N`;
                 `\n:num z:real^N. (a:num->real^N->real) n z - ainf z`]
         P3S_SCALAR_NABLA_UNIF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LIFT_SUB; SMOOTH_MAP_ON_SUB_OPEN]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "UA") THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `G0:real^N->real^N^N`;
                 `b:num->real^N->real`] P3S_SCALAR_NABLA_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "UB") THEN
  MP_TAC(ISPECL [`\i n. !y. y IN K
                     ==> ltnorm2 i (G0:real^N->real^N^N)
                           (lnabla_iter 0 i G0
                              (\z (u:num->real^N). (a:num->real^N->real) n z - ainf z)) y < &1`;
                 `m:num`] P3S_EVENTUALLY_UPTO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "UA" (MP_TAC o SPECL [`i:num`; `&1`]) THEN REWRITE_TAC[REAL_LT_01] THEN
    MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Na:num` (LABEL_TAC "Na"))] THEN
  MP_TAC(ISPECL [`\i n. !y. y IN K
                     ==> ltnorm2 i (G0:real^N->real^N^N)
                           (lnabla_iter 0 i G0
                              (\z (u:num->real^N). (b:num->real^N->real) n z)) y < eps1`;
                 `m:num`] P3S_EVENTUALLY_UPTO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "UB" (MP_TAC o SPECL [`i:num`; `eps1:real`]) THEN
    REWRITE_TAC[ASSUME `&0 < eps1`] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Nb:num` (LABEL_TAC "Nb"))] THEN
  EXISTS_TAC `N0 + N1 + Na + Nb:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `N0 <= n:num /\ N1 <= n /\ Na <= n /\ Nb <= n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N0 + N1 + Na + Nb <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U ((Gt:num->real^N->real^N^N) n)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i <= m ==> ltnorm2 i (G0:real^N->real^N^N)
                      (lnabla_iter 0 i G0
                         (\z (u:num->real^N). (a:num->real^N->real) n z - ainf z)) y < &1) /\
    (!i. i <= m ==> ltnorm2 i (G0:real^N->real^N^N)
                      (lnabla_iter 0 i G0 (\z (u:num->real^N). (ainf:real^N->real) z)) y <= MA) /\
    (!i. i <= m ==> ltnorm2 i (G0:real^N->real^N^N)
                      (lnabla_iter 0 i G0 (\z (u:num->real^N). (b:num->real^N->real) n z)) y
                    <= eps1) /\
    lck_dist2 m G0 ((Gt:num->real^N->real^N^N) n) y <= eps1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "Na" (MP_TAC o SPECL [`i:num`; `n:num`]) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "MA" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "Nb" (MP_TAC o SPECL [`i:num`; `n:num`]) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Cs * (eps1 * K0)` THEN CONJ_TAC THENL
   [REMOVE_THEN "PT" (MP_TAC o SPECL
     [`m:num`; `U:real^N->bool`; `G0:real^N->real^N^N`; `(Gt:num->real^N->real^N^N) n`;
      `(a:num->real^N->real) n`; `(b:num->real^N->real) n`; `ainf:real^N->real`;
      `y:real^N`; `MA:real`; `eps1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    UNDISCH_TAC `(Cs * K0 + &1) * eps1 = e` THEN UNDISCH_TAC `&0 < eps1` THEN
    REAL_ARITH_TAC]);;

let P3S_AB_SMOOTH1 = prove
 (`!c q A0 r0 dl.
     &0 < q /\ &0 < r0
     ==> smooth_map_on (:real^1) (lift o (\s. p3s_phi c q A0 r0 s * p3s_alpha s) o drop) /\
         smooth_map_on (:real^1)
           (lift o (\s. p3s_phi c q A0 r0 s *
                        (p3s_alpha s + (&1 - p3s_alpha s) * (&1 - dl)) - &1) o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC P3S_ALPHA THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`] P3S_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^1)
      (lift o (\s. p3s_alpha s + (&1 - p3s_alpha s) * (&1 - dl)) o drop)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_S1_ADD THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST] THEN
    MATCH_MP_TAC P2C_S1_SUB THEN ASM_REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2C_S1_MUL THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX];
    MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST] THEN
    MATCH_MP_TAC P2C_S1_MUL THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX]]);;

let P3S_GS_BLEND_FORM = prove
 (`!g0 A0 c q r0 dl h (gN:real^3->real^3^3) (z:real^3).
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < h /\ ~(z = vec 0) /\
     A0 + &4 - p3_std_dist g0 z < &3
     ==> inv(h pow 2) %% p3s_gs g0 A0 c q r0 dl h gN z =
         (p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) *
          p3s_alpha(A0 + &4 - p3_std_dist g0 z)) %%
         (inv(h pow 2) %% mpullback (p3_std_nc g0 A0) gN z) +
         (&1 - p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) *
               p3s_alpha(A0 + &4 - p3_std_dist g0 z) +
          (p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) *
           (p3s_alpha(A0 + &4 - p3_std_dist g0 z) +
            (&1 - p3s_alpha(A0 + &4 - p3_std_dist g0 z)) * (&1 - dl)) - &1)) %% g0 z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                 `dl:real`; `h:real`; `gN:real^3->real^3^3`; `z:real^3`] P3S_GS_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(g0:real^3->real^3^3) z = mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) z`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[p3_std_initial]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_SY_NC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[mpullback; P3S_CFR_EXP] THEN
  ABBREV_TAC `J = matrix(frechet_derivative (p3_std_nc g0 A0) (at (z:real^3)))` THEN
  ABBREV_TAC `t = A0 + &4 - p3_std_dist g0 (z:real^3)` THEN
  REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB; MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
  SUBGOAL_THEN `~(h pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ]; ALL_TAC] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(h pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let P3S_SEQ_SCALE = prove
 (`!(dl:num->real) C.
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e)
     ==> (!e. &0 < e ==> ?N. !n. N <= n ==> abs(C * dl n) < e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs C + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs C + &1`; REAL_ABS_MUL] THEN
  MP_TAC(SPEC `C:real` REAL_ABS_POS) THEN
  MP_TAC(SPEC `(dl:num->real) n` REAL_ABS_POS) THEN
  SUBGOAL_THEN `&0 <= abs C * abs((dl:num->real) n)` MP_TAC THENL
   [SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P3S_KREG_GE = prove
 (`!m dl. &0 < dl /\ dl < inv(&m + &1) ==> m <= rfs_kreg dl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[RFS_KREG; REAL_LE_FLOOR; INTEGER_CLOSED] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&m + &1` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&m + &1 = inv(inv(&m + &1))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P3S_CLOSE_BODY = prove
 (`!g0 A0 q C0 r0 (dl:num->real) (h:num->real) (gN:num->real^3->real^3^3) K a0 m.
     p3_std_initial g0 A0 /\ &0 < q /\ &0 < r0 /\ &0 <= C0 /\ a0 < &3 /\
     (!n. &0 < dl n /\ dl n <= &1 / &4) /\ (!n. &0 < h n) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e) /\
     (!n. metric_field (rfs_neck_dom (dl n)) (gN n)) /\
     (!n. rfs_close_on (rfs_kreg (dl n)) (dl n) (rfs_neck_dom (dl n)) (cylinder_flow (&0))
                       (\y. inv(h n pow 2) %% gN n y)) /\
     compact K /\
     K SUBSET {z | a0 < A0 + &4 - p3_std_dist g0 z /\ A0 + &4 - p3_std_dist g0 z < &3}
     ==> !e. &0 < e
             ==> ?N. !n y. N <= n /\ y IN K
                           ==> lck_dist2 m g0
                                 (\z. inv(h n pow 2) %%
                                      p3s_gs g0 A0 (C0 * dl n) q r0 (dl n) (h n) (gN n) z)
                                 y < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?N. !n. N <= n ==> abs((dl:num->real) n) < e`
  (LABEL_TAC "DL") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?N. !n. N <= n ==> abs(C0 * (dl:num->real) n) < e`
  (LABEL_TAC "CDL") THENL
   [MATCH_MP_TAC P3S_SEQ_SCALE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `a0:real`; `&3`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `W = {x:real^3 | a0 < A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x < &3}` THEN
  ABBREV_TAC `Ann = {y:real^3 | exp(a0 / sqrt(&2)) < norm y /\
                                norm y < exp(&3 / sqrt(&2))}` THEN
  SUBGOAL_THEN `open(W:real^3->bool) /\ open(Ann:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `W SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN W ==> ~(z = vec 0) /\ a0 < A0 + &4 - p3_std_dist g0 z /\
                                      A0 + &4 - p3_std_dist g0 z < &3`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `(z:real^3) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?N0. !n. N0 <= n ==> --(inv((dl:num->real) n)) < a0` (X_CHOOSE_TAC `N0:num`)
  THENL
   [USE_THEN "DL" (MP_TAC o SPEC `inv(abs a0 + &1)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < abs a0 + &1`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (dl:num->real) n` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs a0 + &1 < inv((dl:num->real) n)` MP_TAC THENL
     [SUBGOAL_THEN `abs a0 + &1 = inv(inv(abs a0 + &1))` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. N0 <= n ==> Ann SUBSET rfs_neck_dom ((dl:num->real) n)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (dl:num->real) n /\ dl n <= &1 / &4` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&4 <= inv((dl:num->real) n)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &4)` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `--(inv((dl:num->real) n)) < a0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Ann" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(MP_TAC o MATCH_MP P3S_ANN_GEN) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[P3S_NECK_DOM_S; GSYM P3S_SY_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `K:real^3->bool`; `g0:real^3->real^3^3`;
    `\n:num z:real^3. inv((h:num->real) n pow 2) %%
                       mpullback (p3_std_nc g0 A0) ((gN:num->real^3->real^3^3) n) z`;
    `\n:num z:real^3. p3s_phi (C0 * (dl:num->real) n) q A0 r0 (A0 + &4 - p3_std_dist g0 z) *
                       p3s_alpha (A0 + &4 - p3_std_dist g0 z)`;
    `\n:num z:real^3. p3s_phi (C0 * (dl:num->real) n) q A0 r0 (A0 + &4 - p3_std_dist g0 z) *
                       (p3s_alpha (A0 + &4 - p3_std_dist g0 z) +
                        (&1 - p3s_alpha (A0 + &4 - p3_std_dist g0 z)) * (&1 - dl n)) - &1`;
    `\z:real^3. p3s_alpha (A0 + &4 - p3_std_dist g0 z)`; `m:num`] P3S_BLEND_CONV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(\z:real^3. inv((h:num->real) n pow 2) %%
                    mpullback (p3_std_nc g0 A0) ((gN:num->real^3->real^3^3) n) z) =
        mpullback (p3_std_nc g0 A0) (\y. inv(h n pow 2) %% gN n y)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; P3S_MPULLBACK_CMUL; ETA_AX]; ALL_TAC] THEN
      MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`Ann:real^3->bool`; `p3s_ncinv g0 A0`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `rfs_neck_dom ((dl:num->real) n)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; ETA_AX; REAL_LT_INV_EQ; REAL_POW_LT];
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
        `\s. p3s_phi (C0 * (dl:num->real) n) q A0 r0 s * p3s_alpha s`;
        `W:real^3->bool`] P3S_S1_COMP_SMOOTH) THEN
      ASM_SIMP_TAC[P3S_AB_SMOOTH1];
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
        `\s. p3s_phi (C0 * (dl:num->real) n) q A0 r0 s *
             (p3s_alpha s + (&1 - p3s_alpha s) * (&1 - dl n)) - &1`;
        `W:real^3->bool`] P3S_S1_COMP_SMOOTH) THEN
      ASM_SIMP_TAC[P3S_AB_SMOOTH1];
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_alpha`;
        `W:real^3->bool`] P3S_S1_COMP_SMOOTH) THEN
      ASM_SIMP_TAC[P3S_ALPHA];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(BETA_RULE(ISPECL [`\n:num. C0 * (dl:num->real) n`; `q:real`; `A0:real`;
        `r0:real`; `lift(A0 + &4 - p3_std_dist g0 (z:real^3))`] P3S_NEAR_ASEQ)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
        `\n:num. lift o (\s. p3s_phi (C0 * (dl:num->real) n) q A0 r0 s * p3s_alpha s -
                             p3s_alpha s) o drop`;
        `lift o (\s:real. &0) o drop`; `z:real^3`] P3S_NEAR_S1) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; LIFT_NUM];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(BETA_RULE(ISPECL [`\n:num. C0 * (dl:num->real) n`; `dl:num->real`; `q:real`;
        `A0:real`; `r0:real`; `lift(A0 + &4 - p3_std_dist g0 (z:real^3))`] P3S_NEAR_BSEQ)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
        `\n:num. lift o (\s. p3s_phi (C0 * (dl:num->real) n) q A0 r0 s *
                             (p3s_alpha s + (&1 - p3s_alpha s) * (&1 - dl n)) - &1) o drop`;
        `lift o (\s:real. &0) o drop`; `z:real^3`] P3S_NEAR_S1) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; LIFT_NUM];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "DL" (MP_TAC o SPEC `min e (inv(&m + &1))`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
      EXISTS_TAC `N0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `N0 <= n:num /\ N1 <= n` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `N0 + N1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (dl:num->real) n /\ dl n <= &1 / &4` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(dl:num->real) n < e /\ dl n < inv(&m + &1)` STRIP_ASSUME_TAC THENL
       [REMOVE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        UNDISCH_TAC `&0 < (dl:num->real) n` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `a0 < A0 + &4 - p3_std_dist g0 (y:real^3) /\
                    A0 + &4 - p3_std_dist g0 y < &3` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `(y:real^3) IN W` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      SUBGOAL_THEN `--(inv((dl:num->real) n)) < a0` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `N0:num`)) (concl th) &&
          not(can (find_term ((=) `Ann:real^3->bool`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(dl:num->real) n pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P3S_TN_BOUND THEN ASM_SIMP_TAC[P3S_KREG_GE] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(dl:num->real) n * dl n <= dl n * (&1 / &4)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH
         `x * x <= x * (&1 / &4) /\ &0 < x /\ x < e ==> x pow 2 < e`) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ee:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(fun th -> MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `y:real^3`] th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `W:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3S_GS_BLEND_FORM THEN
  SUBGOAL_THEN `&0 < (dl:num->real) n` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* Uniform C^m closeness of h^-2 gS to g0 on compact sets for               *)
(* sequences of necks with dl -> 0 (the cap region from P2CI_LCK_COMPACT,   *)
(* the rest from P3S_CLOSE_BODY), and the modulus p3s_md of MT Thm 13.2(4) *)
(* by contradiction (P3S_MD: clause (e) of P3_THM_13_2_STATEMENT).          *)
(* ========================================================================= *)

let P3S_CLOSE_CAPK = prove
 (`!g0 A0 q C0 r0 (dl:num->real) (h:num->real) (gN:num->real^3->real^3^3) K m.
     p3_std_initial g0 A0 /\ &0 < q /\ &0 < r0 /\ (!n. &0 < h n) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e) /\
     compact K /\ K SUBSET {z | &2 < A0 + &4 - p3_std_dist g0 z}
     ==> !e. &0 < e
             ==> ?N. !n y. N <= n /\ y IN K
                           ==> lck_dist2 m g0
                                 (\z. inv(h n pow 2) %%
                                      p3s_gs g0 A0 (C0 * dl n) q r0 (dl n) (h n) (gN n) z)
                                 y < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `C0:real` o MATCH_MP P3S_SEQ_SCALE) THEN
  ABBREV_TAC `S = {z:real^3 | &2 < A0 + &4 - p3_std_dist g0 z}` THEN
  SUBGOAL_THEN `open(S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n z. z IN S
                 ==> inv(h n pow 2) %%
                     p3s_gs g0 A0 (C0 * (dl:num->real) n) q r0 (dl n) (h n) (gN n) z =
                     (p3s_phi (C0 * dl n) q A0 r0 (A0 + &4 - p3_std_dist g0 z) *
                      (&1 - dl n)) %% g0 z` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `C0 * (dl:num->real) n`; `q:real`;
                  `r0:real`; `(dl:num->real) n`; `(h:num->real) n`;
                  `(gN:num->real^3->real^3^3) n`; `z:real^3`] P3S_GS_FAR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~((h:num->real) n pow 2 = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`;
    `\n:num z:real^3. inv((h:num->real) n pow 2) %%
        p3s_gs g0 A0 (C0 * (dl:num->real) n) q r0 (dl n) (h n) ((gN:num->real^3->real^3^3) n) z`;
    `K:real^3->bool`] P2CI_LCK_COMPACT) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`; `C0:real`; `r0:real`;
                  `dl:num->real`; `h:num->real`; `gN:num->real^3->real^3^3`; `z:real^3`;
                  `S:real^3->bool`] P3S_CAP_METRIC_NEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[]]);;

let P3S_CLOSE_SEQ = prove
 (`!g0 A0 q C0 r0 (dl:num->real) (h:num->real) (gN:num->real^3->real^3^3) rr m.
     p3_std_initial g0 A0 /\ &0 < q /\ &0 < r0 /\ &0 <= C0 /\ &0 <= rr /\
     (!n. &0 < dl n /\ dl n <= &1 / &4) /\ (!n. &0 < h n) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dl n) < e) /\
     (!n. metric_field (rfs_neck_dom (dl n)) (gN n)) /\
     (!n. rfs_close_on (rfs_kreg (dl n)) (dl n) (rfs_neck_dom (dl n)) (cylinder_flow (&0))
                       (\y. inv(h n pow 2) %% gN n y))
     ==> !e. &0 < e
             ==> ?N. !n y. N <= n /\ norm y <= rr
                           ==> lck_dist2 m g0
                                 (\z. inv(h n pow 2) %%
                                      p3s_gs g0 A0 (C0 * dl n) q r0 (dl n) (h n) (gN n) z)
                                 y < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &3 / &2`] P3S_RINV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `r1 = p3s_rad_rinv g0 (A0 + &3 / &2)` THEN
  SUBGOAL_THEN `!y:real^3. p3_std_dist g0 y = p3s_rad_rho g0 (norm y)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P3S_ROT_DIST THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`; `C0:real`; `r0:real`;
                `dl:num->real`; `h:num->real`; `gN:num->real^3->real^3^3`;
                `cball(vec 0:real^3,min r1 rr)`; `m:num`] P3S_CLOSE_CAPK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_ELIM_THM; REAL_LE_MIN] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`; `r1:real`]
           P3S_RHO_LT_EQ) THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1"))] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`; `C0:real`; `r0:real`;
                `dl:num->real`; `h:num->real`; `gN:num->real^3->real^3^3`;
                `cball(vec 0:real^3,rr) DIFF ball(vec 0,r1)`;
                `min (A0 + &3 - p3s_rad_rho g0 rr) (&2)`; `m:num`] P3S_CLOSE_BODY) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM; REAL_NOT_LT] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r1:real`; `norm(y:real^3)`]
           P3S_RHO_LT_EQ) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`; `rr:real`]
           P3S_RHO_LT_EQ) THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2"))] THEN
  EXISTS_TAC `N1 + N2:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `N1 <= n:num /\ N2 <= n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `norm(y:real^3) < r1` THENL
   [REMOVE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_CBALL_0; REAL_LE_MIN] THEN
    ASM_REAL_ARITH_TAC;
    REMOVE_THEN "N2" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0]]);;

let P3S_MD_EXISTS = prove
 (`!g0 A0 q C0 r0 dd.
     p3_std_initial g0 A0 /\ &0 < q /\ &0 < r0 /\ &0 <= C0 /\ &0 < dd
     ==> ?m. &0 < m /\ m <= dd /\
             !dl h (gN:real^3->real^3^3).
               &0 < dl /\ dl <= m /\ dl <= &1 / &4 /\ &0 < h /\
               metric_field (rfs_neck_dom dl) gN /\
               rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                            (\y. inv(h pow 2) %% gN y)
               ==> rfs_close_on (rfs_kreg dd) dd
                     {x | p3_std_dist g0 x < inv dd /\
                          --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                     g0 (\x. inv(h pow 2) %% p3s_gs g0 A0 (C0 * dl) q r0 dl h gN x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(fun th ->
    MP_TAC(REWRITE_RULE[SKOLEM_THM] (GEN `n:num`
     (REWRITE_RULE[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL; REAL_LT_INV_EQ;
                   REAL_ARITH `&0 < &n + &1`; ASSUME `&0 < dd`]
       (SPEC `min dd (inv(&n + &1))`
         (REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`;
                       NOT_FORALL_THM; NOT_IMP] th)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:num->real` (X_CHOOSE_THEN `h:num->real`
    (X_CHOOSE_THEN `gN:num->real^3->real^3^3` (LABEL_TAC "BAD")))) THEN
  SUBGOAL_THEN
   `(!n. &0 < (dl:num->real) n /\ dl n <= &1 / &4) /\ (!n. &0 < (h:num->real) n) /\
    (!n. metric_field (rfs_neck_dom (dl n)) ((gN:num->real^3->real^3^3) n)) /\
    (!n. rfs_close_on (rfs_kreg (dl n)) (dl n) (rfs_neck_dom (dl n)) (cylinder_flow (&0))
                      (\y. inv(h n pow 2) %% gN n y)) /\
    (!n. dl n <= inv(&n + &1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN GEN_TAC THEN USE_THEN "BAD" (MP_TAC o SPEC `n:num`) THEN
    SIMP_TAC[REAL_LE_MIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?N. !n. N <= n ==> abs((dl:num->real) n) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(dl:num->real) n <= inv(&N)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `N <= n:num` THEN UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (dl:num->real) n` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `inv(&N) < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `inv dd`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`; `C0:real`; `r0:real`;
                `dl:num->real`; `h:num->real`; `gN:num->real^3->real^3^3`;
                `p3s_rad_rinv g0 (inv dd)`; `rfs_kreg dd`] P3S_CLOSE_SEQ) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(MP_TAC o SPEC `dd pow 2 / &2`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "GOOD")) THEN
  USE_THEN "BAD" (MP_TAC o CONJUNCT2 o SPEC `N:num`) THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN REWRITE_TAC[rfs_close_on] THEN
  EXISTS_TAC `dd pow 2 / &2` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`dd:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN REMOVE_THEN "GOOD" MATCH_MP_TAC THEN
  REWRITE_TAC[LE_REFL] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`;
                `p3s_rad_rinv g0 (inv dd)`] P3S_RHO_LT_EQ) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_ROT_DIST) THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `p3_std_dist g0 (y:real^3) < inv dd` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let p3s_md = new_definition
 `p3s_md g0 A0 q C0 r0 (dd:real) =
    @m. &0 < m /\ m <= dd /\
        !dl h (gN:real^3->real^3^3).
          &0 < dl /\ dl <= m /\ dl <= &1 / &4 /\ &0 < h /\
          metric_field (rfs_neck_dom dl) gN /\
          rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                       (\y. inv(h pow 2) %% gN y)
          ==> rfs_close_on (rfs_kreg dd) dd
                {x | p3_std_dist g0 x < inv dd /\ --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                g0 (\x. inv(h pow 2) %% p3s_gs g0 A0 (C0 * dl) q r0 dl h gN x)`;;

let P3S_MD = prove
 (`!g0 A0 q C0 r0.
     p3_std_initial g0 A0 /\ &0 < q /\ &0 < r0 /\ &0 <= C0
     ==> p3_modulus (p3s_md g0 A0 q C0 r0) /\
         !dd dl h (gN:real^3->real^3^3).
           &0 < dd /\ &0 < dl /\ dl <= p3s_md g0 A0 q C0 r0 dd /\ dl <= &1 / &4 /\
           &0 < h /\ metric_field (rfs_neck_dom dl) gN /\
           rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                        (\y. inv(h pow 2) %% gN y)
           ==> rfs_close_on (rfs_kreg dd) dd
                 {x | p3_std_dist g0 x < inv dd /\ --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                 g0 (\x. inv(h pow 2) %% p3s_gs g0 A0 (C0 * dl) q r0 dl h gN x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!dd. &0 < dd
         ==> &0 < p3s_md g0 A0 q C0 r0 dd /\ p3s_md g0 A0 q C0 r0 dd <= dd /\
             !dl h (gN:real^3->real^3^3).
               &0 < dl /\ dl <= p3s_md g0 A0 q C0 r0 dd /\ dl <= &1 / &4 /\ &0 < h /\
               metric_field (rfs_neck_dom dl) gN /\
               rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                            (\y. inv(h pow 2) %% gN y)
               ==> rfs_close_on (rfs_kreg dd) dd
                     {x | p3_std_dist g0 x < inv dd /\
                          --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                     g0 (\x. inv(h pow 2) %% p3s_gs g0 A0 (C0 * dl) q r0 dl h gN x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p3s_md] THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC P3S_MD_EXISTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3_modulus] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `dd:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;

