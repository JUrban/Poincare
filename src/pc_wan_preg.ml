(* ========================================================================= *)
(* pc_wan_preg: parabolic interior regularity, MT Prop 9.20. The weak form   *)
(* wan_pweak on om is localised to the whole-space form wan_gweak for chi U  *)
(* (coefficients a = theta A / rho + (1 - theta) I, b = c = 0, all           *)
(* lower-order terms in the forcing f); the spatial bootstrap WAN_PSTEP_BOOT *)
(* and the time bootstrap WAN_TIME_BOOT run over all cutoffs;                *)
(* WAN_HD_ALL_SMOOTH gives local smooth representatives and                  *)
(* WAN_LOCAL_SMOOTH_AE glues them. Main theorems: WAN_PAR_REG_W, WAN_PAR_REG *)
(* and WAN_CONJ_HEAT_REG.                                                    *)
(*                                                                           *)
(* First: space-time partials, test functions, cutoffs, coefficients.        *)
(* ========================================================================= *)

needs "src/pc_wan_psmooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The partials of wan_pweak are coordinate partials (time = basis N+1).    *)
(* ------------------------------------------------------------------------- *)

let WAN_TDER_DPART = prove
 (`!(phi:real^(N,1)finite_sum->real) z.
     wan_tder phi z = wan_dpart (dimindex(:N) + 1) phi z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_tder; wan_dpart] THEN
  MP_TAC(ISPEC `1` (INST_TYPE [`:N`,`:M`; `:1`,`:N`] TEXT_BASIS_HIGH)) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `basis(dimindex(:N) + 1):real^(N,1)finite_sum =
                pastecart (vec 0:real^N) (lift(&1))`
  (fun th -> REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
  ASM_REWRITE_TAC[PDE_BASIS1_REAL1]);;

let WAN_XDER_DPART = prove
 (`!i (phi:real^(N,1)finite_sum->real) z.
     1 <= i /\ i <= dimindex(:N) ==> wan_xder i phi z = wan_dpart i phi z`,
  SIMP_TAC[wan_xder; wan_dpart; TEXT_PASTECART_BASIS_LOW]);;

(* ------------------------------------------------------------------------- *)
(* Test functions: supports of derivatives, products with maps smooth on    *)
(* the open set, derivatives, membership in all Sobolev classes.            *)
(* ------------------------------------------------------------------------- *)

let WAN_TEST_SUPPORT = prove
 (`!(s:real^M->bool) phi.
     wan_test s phi
     ==> ?k. compact k /\ k SUBSET s /\ (!x. ~(x IN k) ==> phi x = &0) /\
             (!i x. ~(x IN k) ==> wan_dpart i phi x = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_REWRITE_TAC[]);;

let WAN_TEST_SMUL = prove
 (`!(s:real^M->bool) phi g.
     open s /\ wan_test s phi /\ smooth_map_on s (\x. lift(g x))
     ==> wan_test s (\x. phi x * g x) /\
         !i x. wan_dpart i (\x. phi x * g x) x =
               wan_dpart i phi x * g x + phi x * wan_dpart i g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `phi:real^M->real`; `g:real^M->real`]
                WAN_TEST_MUL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. if x IN s then (phi:real^M->real) x * g x else &0) = (\x. phi x * g x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((x:real^M) IN k)` (fun th -> ASM_SIMP_TAC[th; REAL_MUL_LZERO]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:real^M`] THEN
  ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `~((x:real^M) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO] THEN
  UNDISCH_TAC `wan_test (s:real^M->bool) (\x. (phi:real^M->real) x * g x)` THEN
  SIMP_TAC[wan_test]);;

let WAN_TEST_DPART_OPEN = prove
 (`!(s:real^M->bool) phi i. wan_test s phi ==> wan_test s (wan_dpart i phi)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wan_test (:real^M) (wan_dpart i (phi:real^M->real))` MP_TAC THENL
   [MATCH_MP_TAC WAN_TEST_DPART_TEST THEN MATCH_MP_TAC WAN_TEST_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[wan_test] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[]);;

let WAN_TEST_LSPACE2 = prove
 (`!phi:real^M->real.
     wan_test (:real^M) phi ==> (\x. lift(phi x)) IN lspace (:real^M) (&2)`,
  GEN_TAC THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON; LIFT_NUM]);;

let WAN_HD_TEST = prove
 (`!d s (phi:real^M->real).
     wan_test (:real^M) phi ==> wan_hd d s (\x. lift(phi x))`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[wan_hd; WAN_TEST_LSPACE2] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  EXISTS_TAC `\x. lift(wan_dpart k (phi:real^M->real) x)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^M)`; `phi:real^M->real`; `lift(&1)`; `k:num`]
                  WAN_WPD_TEST_VEC) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; GSYM LIFT_CMUL; REAL_MUL_RID];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC WAN_TEST_DPART_TEST THEN ASM_REWRITE_TAC[]]);;

let WAN_HT_TEST = prove
 (`!m (phi:real^(N,1)finite_sum->real).
     wan_test (:real^(N,1)finite_sum) phi ==> wan_ht m (\x. lift(phi x))`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[wan_ht; wan_hxa; WAN_HD_TEST] THEN
  EXISTS_TAC
   `\x. lift(wan_dpart (dimindex(:N) + 1) (phi:real^(N,1)finite_sum->real) x)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `phi:real^(N,1)finite_sum->real`;
                   `lift(&1)`; `dimindex(:N) + 1`] WAN_WPD_TEST_VEC) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; GSYM LIFT_CMUL; REAL_MUL_RID];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC WAN_TEST_DPART_TEST THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Cutoffs of local L^2 maps are in L^2 of the whole space.                 *)
(* ------------------------------------------------------------------------- *)

let WAN_LSPACE_ZERO_EXTEND = prove
 (`!(f:real^M->real^K) k p.
     &0 < p /\ f IN lspace k p /\ (!x. ~(x IN k) ==> f x = vec 0)
     ==> f IN lspace (:real^M) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LSPACE_ALT; IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(f:real^M->real^K) = (\x. if x IN k then f x else vec 0)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[MEASURABLE_ON_UNIV]];
    SUBGOAL_THEN
     `(\x. lift(norm((f:real^M->real^K) x) rpow p)) =
      (\x. if x IN k then lift(norm(f x) rpow p) else vec 0)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM];
      ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV]]]);;

let WAN_L2LOC_CUTOFF = prove
 (`!(s:real^M->bool) (u:real^M->real^K) chi.
     wan_l2loc s u /\ wan_test s chi
     ==> (\x. chi x % u x) IN lspace (:real^M) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wan_cc (chi:real^M->real)` MP_TAC THENL
   [MATCH_MP_TAC WAN_TEST_CC THEN MATCH_MP_TAC WAN_TEST_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WAN_CC_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) ASSUME_TAC))) THEN
  MATCH_MP_TAC WAN_LSPACE_ZERO_EXTEND THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; REAL_ARITH `&0 < &2`] THEN
  MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    UNDISCH_TAC `wan_l2loc (s:real^M->bool) (u:real^M->real^K)` THEN
    REWRITE_TAC[wan_l2loc] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let WAN_L2LOC_LLOC = prove
 (`!(s:real^M->bool) (u:real^M->real^K). wan_l2loc s u ==> wan_lloc s u`,
  REWRITE_TAC[wan_l2loc; wan_lloc] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^M->real^K) IN lspace k (&1)` MP_TAC THENL
   [MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `&2` THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[LSPACE_1; IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Uniform ellipticity on a compact set, and the extension of A / rho to   *)
(* the whole space by a convex combination with the identity.  (A version  *)
(* of GRGE_QUADFORM_BOUNDS of pc_mfd_embmetric, which this file does not     *)
(* load and which asks for smoothness on the whole space.)                   *)
(* ------------------------------------------------------------------------- *)

let WAN_QF_LOWER_COMPACT = prove
 (`!(G:real^M->real^N^N) k.
     compact k /\ (\z. vectorize(G z)) continuous_on k /\
     (!z v. z IN k /\ ~(v = vec 0) ==> &0 < v dot (G z ** v))
     ==> ?lam. &0 < lam /\
               !z v. z IN k ==> lam * norm v pow 2 <= v dot (G z ** v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd"))) THEN
  ASM_CASES_TAC `k:real^M->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  ABBREV_TAC `qf = \p:real^(M,N)finite_sum.
                     sndcart p dot ((G:real^M->real^N^N)(fstcart p) ** sndcart p)` THEN
  SUBGOAL_THEN `(lift o (qf:real^(M,N)finite_sum->real)) continuous_on
                ((k:real^M->bool) PCROSS sphere(vec 0:real^N,&1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qf" THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    SUBGOAL_THEN
     `(vectorize o (\p:real^(M,N)finite_sum. (G:real^M->real^N^N)(fstcart p))) =
      (\z. vectorize(G z)) o fstcart`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`qf:real^(M,N)finite_sum->real`;
                 `(k:real^M->bool) PCROSS sphere(vec 0:real^N,&1)`]
                CONTINUOUS_ATTAINS_INF) THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY;
               REAL_ARITH `~(&1 < &0)`; EXISTS_IN_PCROSS; FORALL_IN_PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^M` (X_CHOOSE_THEN `v0:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inf"))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0]) THEN
  SUBGOAL_THEN
   `!z u. z IN k /\ norm(u:real^N) = &1
          ==> v0 dot ((G:real^M->real^N^N) z0 ** v0) <= u dot (G z ** u)`
  (LABEL_TAC "unit") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "inf" (MP_TAC o SPECL [`z:real^M`; `u:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
    EXPAND_TAC "qf" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  EXISTS_TAC `v0 dot ((G:real^M->real^N^N) z0 ** v0)` THEN CONJ_TAC THENL
   [USE_THEN "pd" (MP_TAC o SPECL [`z0:real^M`; `v0:real^N`]) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_MESON_TAC[REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^M` THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "unit" (MP_TAC o SPECL [`z:real^M`; `inv(norm v) % v:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = v dot ((G:real^M->real^N^N) z ** v)` THEN
  ABBREV_TAC `n = norm(v:real^N)` THEN
  ABBREV_TAC `m = v0 dot ((G:real^M->real^N^N) z0 ** v0)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `m * n pow 2 <= (inv n * inv n * q) * n pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = q ==> x <= y ==> x <= q`) THEN
  UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD);;

let WAN_CONVEX_ELL_ARITH = prove
 (`!t m mu n q.
     &0 <= t /\ t <= &1 /\ &0 <= n /\ m <= mu /\ m <= &1 /\ t * mu * n <= t * q
     ==> m * n <= t * q + (&1 - t) * n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t * (mu - m) * n /\ &0 <= (&1 - t) * (&1 - m) * n` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let WAN_PREG_COEFF = prove
 (`!(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) k.
     open om /\ smooth_map_on om (\z. lift(rho z)) /\ (!z. z IN om ==> &0 < rho z) /\
     smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o A) /\
     (!z v. z IN om /\ ~(v = vec 0) ==> &0 < v dot (A z ** v)) /\
     compact k /\ k SUBSET om
     ==> ?a lam. &0 < lam /\
                 (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                        ==> wan_cc (\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j)) /\
                 (!z xi. lam * norm xi pow 2 <= xi dot (a z ** xi)) /\
                 (!z i j. z IN k /\ 1 <= i /\ i <= dimindex(:N) /\
                          1 <= j /\ j <= dimindex(:N)
                          ==> a z$i$j = A z$i$j * inv(rho z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `k:real^(N,1)finite_sum->bool`]
                WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:real^(N,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT) THEN
  DISCH_THEN(X_CHOOSE_THEN `kt:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `smooth_map_on om (\z. lift(inv((rho:real^(N,1)finite_sum->real) z)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z. lift((rho:real^(N,1)finite_sum->real) z)`]
                  SMOOTH_MAP_ON_LIFT_INV) THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_LT_IMP_NZ; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on om (\z. lift((A:real^(N,1)finite_sum->real^N^N) z$i$j))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`]
                  LRG_SMOOTH_VECTORIZE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. inv((rho:real^(N,1)finite_sum->real) z) %%
                      (A:real^(N,1)finite_sum->real^N^N) z`;
                 `kt:real^(N,1)finite_sum->bool`] WAN_QF_LOWER_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; VECTORIZE_CMUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_REWRITE_TAC[];
        MP_TAC(MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON (ASSUME
         `smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o
                            (A:real^(N,1)finite_sum->real^N^N))`)) THEN
        REWRITE_TAC[o_DEF]];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^(N,1)finite_sum) IN om` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mu"))) THEN
  EXISTS_TAC `\z. (theta:real^(N,1)finite_sum->real) z %%
                  (inv((rho:real^(N,1)finite_sum->real) z) %%
                   (A:real^(N,1)finite_sum->real^N^N) z) +
                  (&1 - theta z) %% mat 1` THEN
  EXISTS_TAC `min mu (&1)` THEN
  ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT;
               REAL_LT_MIN; REAL_LT_01] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_CC_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_TEST_CC THEN MATCH_MP_TAC WAN_TEST_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `theta:real^(N,1)finite_sum->real`;
                     `\z. inv((rho:real^(N,1)finite_sum->real) z) *
                          (A:real^(N,1)finite_sum->real^N^N) z$i$j`] WAN_TEST_SMUL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\z. lift(inv((rho:real^(N,1)finite_sum->real) z))`;
                     `\z. lift((A:real^(N,1)finite_sum->real^N^N) z$i$j)`]
                    SMOOTH_MAP_ON_LIFT_MUL) THEN
      ASM_SIMP_TAC[LIFT_DROP];
      MATCH_MP_TAC WAN_CC_MUL THEN REWRITE_TAC[WAN_CC_CONST] THEN
      MATCH_MP_TAC WAN_CC_SUB THEN REWRITE_TAC[WAN_CC_CONST; ETA_AX] THEN
      MATCH_MP_TAC WAN_TEST_CC THEN MATCH_MP_TAC WAN_TEST_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    MAP_EVERY X_GEN_TAC [`z:real^(N,1)finite_sum`; `xi:real^N`] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_LID; DOT_RADD; DOT_RMUL; GSYM NORM_POW_2] THEN
    MATCH_MP_TAC WAN_CONVEX_ELL_ARITH THEN EXISTS_TAC `mu:real` THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN kt` THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "mu" (MP_TAC o SPECL [`z:real^(N,1)finite_sum`; `xi:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL];
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LE_REFL]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The localised data.  For a cutoff chi (a test function                    *)
(* on om) and eta = chi / rho, W = chi U solves wan_gweak with a, b = 0,   *)
(* c = 0, forcing wan_locf (all lower-order terms, including -eta Fs) and  *)
(* divergence data wan_locg.  This section: definitions, the pointwise       *)
(* identity between the two integrands, L^2 memberships and supports.      *)
(* ========================================================================= *)

let wan_loce = new_definition
 `wan_loce (rho:real^(N,1)finite_sum->real) (chi:real^(N,1)finite_sum->real) =
    \z. chi z * inv(rho z)`;;

let wan_locf = new_definition
 `wan_locf (rho:real^(N,1)finite_sum->real) (A:real^(N,1)finite_sum->real^N^N)
           (B:real^(N,1)finite_sum->real^N) (C:real^(N,1)finite_sum->real)
           (Fs:real^(N,1)finite_sum->real) (U:real^(N,1)finite_sum->real)
           (K:num->real^(N,1)finite_sum->real) (chi:real^(N,1)finite_sum->real) =
    \z. (wan_dpart (dimindex(:N) + 1) (wan_loce rho chi) z * rho z) % lift(U z) +
        (wan_loce rho chi z * C z) % lift(U z) +
        vsum(1..dimindex(:N)) (\j. (wan_loce rho chi z * B z$j) % lift(K j z)) -
        vsum(1..dimindex(:N))
          (\i. vsum(1..dimindex(:N))
                 (\j. (wan_dpart i (wan_loce rho chi) z * A z$i$j) % lift(K j z))) -
        lift(wan_loce rho chi z * Fs z)`;;

let wan_locg = new_definition
 `wan_locg (a:real^(N,1)finite_sum->real^N^N) (chi:real^(N,1)finite_sum->real)
           (U:real^(N,1)finite_sum->real) =
    \i z. --(vsum(1..dimindex(:N)) (\j. (wan_dpart j chi z * a z$i$j) % lift(U z)))`;;

(* ------------------------------------------------------------------------- *)
(* The pointwise identity: the wan_gweak integrand for chi U (with the     *)
(* simplifications b = 0, c = 0 already made) is the wan_pweak integrand    *)
(* at phi = psi eta minus Fs phi.                                            *)
(* ------------------------------------------------------------------------- *)

let WAN_PREG_INTEGRAND = prove
 (`!(psi:real^(N,1)finite_sum->real) eta chi rho U (K:num->real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N) C Fs
    (a:real^(N,1)finite_sum->real^N^N) z.
     chi z = rho z * eta z /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> a z$i$j * chi z = eta z * A z$i$j)
     ==> wan_dpart (dimindex(:N) + 1) psi z % (chi z % lift(U z)) -
         vsum(1..dimindex(:N))
           (\i. wan_dpart i psi z %
                (vsum(1..dimindex(:N))
                   (\j. a z$i$j % (wan_dpart j chi z % lift(U z) + chi z % lift(K j z))) +
                 --(vsum(1..dimindex(:N)) (\j. (wan_dpart j chi z * a z$i$j) % lift(U z))))) +
         psi z % ((wan_dpart (dimindex(:N) + 1) eta z * rho z) % lift(U z) +
                  (eta z * C z) % lift(U z) +
                  vsum(1..dimindex(:N)) (\j. (eta z * B z$j) % lift(K j z)) -
                  vsum(1..dimindex(:N))
                    (\i. vsum(1..dimindex(:N))
                           (\j. (wan_dpart i eta z * A z$i$j) % lift(K j z))) -
                  lift(eta z * Fs z)) =
         lift(rho z * U z *
                (wan_dpart (dimindex(:N) + 1) psi z * eta z +
                 psi z * wan_dpart (dimindex(:N) + 1) eta z) -
              sum(1..dimindex(:N))
                (\i. sum(1..dimindex(:N))
                       (\j. A z$i$j * K j z *
                            (wan_dpart i psi z * eta z + psi z * wan_dpart i eta z))) +
              (sum(1..dimindex(:N)) (\i. B z$i * K i z) + C z * U z) * (psi z * eta z)) -
         lift(Fs z * (psi z * eta z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_ADD; DROP_CMUL; DROP_VSUM; DROP_NEG;
              LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. wan_dpart i (psi:real^(N,1)finite_sum->real) z *
           (sum(1..dimindex(:N))
              (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j *
                   (wan_dpart j chi z * (U:real^(N,1)finite_sum->real) z +
                    chi z * (K:num->real^(N,1)finite_sum->real) j z)) +
            --sum(1..dimindex(:N)) (\j. (wan_dpart j chi z * a z$i$j) * U z))) =
    sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
             (\j. (A:real^(N,1)finite_sum->real^N^N) z$i$j * K j z *
                  wan_dpart i psi z * (eta:real^(N,1)finite_sum->real) z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
             (\j. (A:real^(N,1)finite_sum->real^N^N) z$i$j *
                  (K:num->real^(N,1)finite_sum->real) j z *
                  (wan_dpart i (psi:real^(N,1)finite_sum->real) z *
                   (eta:real^(N,1)finite_sum->real) z +
                   psi z * wan_dpart i eta z))) =
    sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N)) (\j. A z$i$j * K j z * wan_dpart i psi z * eta z)) +
    psi z * sum(1..dimindex(:N))
              (\i. sum(1..dimindex(:N)) (\j. (wan_dpart i eta z * A z$i$j) * K j z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\j. ((eta:real^(N,1)finite_sum->real) z *
            (B:real^(N,1)finite_sum->real^N) z$j) *
           (K:num->real^(N,1)finite_sum->real) j z) =
    eta z * sum(1..dimindex(:N)) (\i. B z$i * K i z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ABBREV_TAC `S1 = sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N)) (\j. (A:real^(N,1)finite_sum->real^N^N) z$i$j *
           (K:num->real^(N,1)finite_sum->real) j z *
           wan_dpart i (psi:real^(N,1)finite_sum->real) z *
           (eta:real^(N,1)finite_sum->real) z))` THEN
  ABBREV_TAC `S2 = sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
             (\j. (wan_dpart i (eta:real^(N,1)finite_sum->real) z *
                   (A:real^(N,1)finite_sum->real^N^N) z$i$j) *
                  (K:num->real^(N,1)finite_sum->real) j z))` THEN
  ABBREV_TAC `SB = sum(1..dimindex(:N))
      (\i. (B:real^(N,1)finite_sum->real^N) z$i *
           (K:num->real^(N,1)finite_sum->real) i z)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* eta = chi / rho.                                                          *)
(* ------------------------------------------------------------------------- *)

let WAN_LOCE_FACTS = prove
 (`!(om:real^(N,1)finite_sum->bool) rho chi k.
     open om /\ smooth_map_on om (\z. lift(rho z)) /\ (!z. z IN om ==> &0 < rho z) /\
     wan_test om chi /\ compact k /\ k SUBSET om /\ (!z. ~(z IN k) ==> chi z = &0)
     ==> wan_test om (wan_loce rho chi) /\
         (!z. chi z = rho z * wan_loce rho chi z) /\
         (!z. ~(z IN k) ==> wan_loce rho chi z = &0) /\
         (!i z. ~(z IN k) ==> wan_dpart i (wan_loce rho chi) z = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_test om (wan_loce (rho:real^(N,1)finite_sum->real) chi)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wan_loce] THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `chi:real^(N,1)finite_sum->real`;
                   `\z. inv((rho:real^(N,1)finite_sum->real) z)`] WAN_TEST_SMUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z. lift((rho:real^(N,1)finite_sum->real) z)`]
                  SMOOTH_MAP_ON_LIFT_INV) THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_LT_IMP_NZ; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z IN k) ==> wan_loce (rho:real^(N,1)finite_sum->real) chi z = &0`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[wan_loce; REAL_MUL_LZERO]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN REWRITE_TAC[wan_loce] THEN
    ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN om` THENL
     [SUBGOAL_THEN `&0 < (rho:real^(N,1)finite_sum->real) z` MP_TAC THENL
       [ASM_SIMP_TAC[]; CONV_TAC REAL_FIELD];
      SUBGOAL_THEN `~((z:real^(N,1)finite_sum) IN k)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `wan_test om (wan_loce (rho:real^(N,1)finite_sum->real) chi)` THEN
    SIMP_TAC[wan_test]]);;

let WAN_SMUL_CUTOFF_L2 = prove
 (`!(s:real^M->bool) m g (u:real^M->real^K).
     open s /\ wan_test s m /\ smooth_map_on s (\x. lift(g x)) /\ wan_l2loc s u
     ==> (\x. (m x * g x) % u x) IN lspace (:real^M) (&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `m:real^M->real`; `g:real^M->real`] WAN_TEST_SMUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `u:real^M->real^K`; `\x. (m:real^M->real) x * g x`]
                WAN_L2LOC_CUTOFF) THEN
  ASM_REWRITE_TAC[]);;

let WAN_L2_SUMS_TAC =
  REPEAT((MATCH_MP_TAC LSPACE_ADD ORELSE MATCH_MP_TAC LSPACE_SUB) THEN
         REWRITE_TAC[REAL_ARITH `&0 <= &2`] THEN CONJ_TAC);;

let WAN_PREG_L2 = prove
 (`!(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
    (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
    (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real)
    (chi:real^(N,1)finite_sum->real) (a:real^(N,1)finite_sum->real^N^N) k.
     wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
     wan_l2loc om (\z. lift(U z)) /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_l2loc om (\z. lift(K j z))) /\
     wan_test om chi /\ compact k /\ k SUBSET om /\ (!z. ~(z IN k) ==> chi z = &0) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j))
     ==> (\z. chi z % lift(U z)) IN lspace (:real^(N,1)finite_sum) (&2) /\
         (!z. ~(z IN k) ==> chi z % lift(U z) = vec 0) /\
         (!j. 1 <= j /\ j <= dimindex(:N)
              ==> (\z. wan_dpart j chi z % lift(U z) + chi z % lift(K j z)) IN
                  lspace (:real^(N,1)finite_sum) (&2)) /\
         (!j z. ~(z IN k)
                ==> wan_dpart j chi z % lift(U z) + chi z % lift(K j z) = vec 0) /\
         wan_locf rho A B C Fs U K chi IN lspace (:real^(N,1)finite_sum) (&2) /\
         (!z. ~(z IN k) ==> wan_locf rho A B C Fs U K chi z = vec 0) /\
         (!i. 1 <= i /\ i <= dimindex(:N)
              ==> wan_locg a chi U i IN lspace (:real^(N,1)finite_sum) (&2)) /\
         (!i z. ~(z IN k) ==> wan_locg a chi U i z = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `chi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                WAN_LOCE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[wan_locf; wan_locg] THEN
  ABBREV_TAC `eta = wan_loce (rho:real^(N,1)finite_sum->real) chi` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!j z. ~(z IN k) ==> wan_dpart j (chi:real^(N,1)finite_sum->real) z = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `wan_test om (chi:real^(N,1)finite_sum->real)` THEN
    SIMP_TAC[wan_test];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!j. 1 <= j /\ j <= dimindex(:N)
         ==> smooth_map_on om (\z. lift((B:real^(N,1)finite_sum->real^N) z$j))) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> smooth_map_on om (\z. lift((A:real^(N,1)finite_sum->real^N^N) z$i$j))) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> smooth_map_on om (\z. lift((a:real^(N,1)finite_sum->real^N^N) z$i$j)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`]
                    LRG_SMOOTH_VECTORIZE) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^(N,1)finite_sum)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC WAN_CC_SMOOTH THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!m (g:real^(N,1)finite_sum->real).
       wan_test om m /\ smooth_map_on om (\z. lift(g z))
       ==> (\z. (m z * g z) % lift((U:real^(N,1)finite_sum->real) z)) IN
           lspace (:real^(N,1)finite_sum) (&2)) /\
    (!m (g:real^(N,1)finite_sum->real) j.
       wan_test om m /\ smooth_map_on om (\z. lift(g z)) /\ 1 <= j /\ j <= dimindex(:N)
       ==> (\z. (m z * g z) % lift((K:num->real^(N,1)finite_sum->real) j z)) IN
           lspace (:real^(N,1)finite_sum) (&2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_SMUL_CUTOFF_L2 THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. wan_test om m
        ==> (\z. m z % lift((U:real^(N,1)finite_sum->real) z)) IN
            lspace (:real^(N,1)finite_sum) (&2) /\
            (!j. 1 <= j /\ j <= dimindex(:N)
                 ==> (\z. m z % lift((K:num->real^(N,1)finite_sum->real) j z)) IN
                     lspace (:real^(N,1)finite_sum) (&2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_L2LOC_CUTOFF THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_test om (wan_dpart (dimindex(:N) + 1) (eta:real^(N,1)finite_sum->real)) /\
    (!i. wan_test om (wan_dpart i (eta:real^(N,1)finite_sum->real))) /\
    (!j. wan_test om (wan_dpart j (chi:real^(N,1)finite_sum->real)))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_TEST_DPART_OPEN]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[ETA_AX];
    ASM_SIMP_TAC[VECTOR_MUL_LZERO];
    REPEAT STRIP_TAC THEN WAN_L2_SUMS_TAC THEN ASM_SIMP_TAC[ETA_AX];
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    REWRITE_TAC[] THEN WAN_L2_SUMS_TAC THENL
     [ASM_SIMP_TAC[ETA_AX];
      ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC LSPACE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ARITH `&0 < &2`] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC LSPACE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ARITH `&0 < &2`] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LSPACE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ARITH `&0 < &2`] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC WAN_TEST_LSPACE2 THEN MATCH_MP_TAC WAN_TEST_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `eta:real^(N,1)finite_sum->real`;
                     `Fs:real^(N,1)finite_sum->real`] WAN_TEST_SMUL) THEN
      ASM_SIMP_TAC[ETA_AX]];
    ASM_SIMP_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO; VSUM_0; LIFT_NUM; VECTOR_ADD_LID;
                 VECTOR_SUB_REFL];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC LSPACE_NEG THEN
    MATCH_MP_TAC LSPACE_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ARITH `&0 < &2`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ETA_AX];
    ASM_SIMP_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO; VSUM_0; VECTOR_NEG_0]]);;

(* ========================================================================= *)
(* The localisation.  chi U solves the whole-space weak                    *)
(* form wan_gweak with coefficients a (equal to A / rho where chi lives),  *)
(* b = 0, c = 0, forcing wan_locf and divergence data wan_locg.             *)
(* ========================================================================= *)

let WAN_GWEAK_INTEGRAND_INTEGRABLE = prove
 (`!(psi:real^M->real) (W:real^M->real^K) H R t n.
     wan_test (:real^M) psi /\ wan_lloc (:real^M) W /\ wan_lloc (:real^M) R /\
     (!i. 1 <= i /\ i <= n ==> wan_lloc (:real^M) (H i))
     ==> (\z. wan_dpart t psi z % W z - vsum(1..n) (\i. wan_dpart i psi z % H i z) +
              psi z % R z) integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^M)`; `psi:real^M->real`; `W:real^M->real^K`]
                    WAN_TEST_PAIRING) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(:real^M)`; `psi:real^M->real`; `(H:num->real^M->real^K) i`]
                    WAN_TEST_PAIRING) THEN
      ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`(:real^M)`; `psi:real^M->real`; `R:real^M->real^K`]
                  WAN_TEST_PAIRING) THEN
    ASM_SIMP_TAC[]]);;

let WAN_PREG_FINISH = prove
 (`!(p:real^M->real) q om k.
     k SUBSET om /\ (!z. ~(z IN k) ==> p z = &0 /\ q z = &0) /\
     (\z. lift(p z) - lift(q z)) integrable_on (:real^M) /\
     (\z. lift(q z)) integrable_on (:real^M) /\
     integral om (\z. lift(p z)) = integral om (\z. lift(q z))
     ==> integral (:real^M) (\z. lift(p z) - lift(q z)) = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((p:real^M->real) z)) integrable_on (:real^M)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. lift((p:real^M->real) z) - lift(q z)`;
                   `\z. lift((q:real^M->real) z)`; `(:real^M)`] INTEGRABLE_ADD) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_ADD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB] THEN
  SUBGOAL_THEN
   `integral (:real^M) (\z. lift((p:real^M->real) z)) = integral om (\z. lift(p z)) /\
    integral (:real^M) (\z. lift((q:real^M->real) z)) = integral om (\z. lift(q z))`
  (fun th -> ASM_REWRITE_TAC[th; VECTOR_SUB_REFL]) THEN
  CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[SUBSET_UNIV; LIFT_NUM]);;

let WAN_PREG_GWEAK = prove
 (`!(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
    (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
    (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real)
    (chi:real^(N,1)finite_sum->real) (a:real^(N,1)finite_sum->real^N^N) k.
     wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
     wan_l2loc om (\z. lift(U z)) /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_l2loc om (\z. lift(K j z))) /\
     wan_pweak om rho A B C Fs U K /\
     wan_test om chi /\ compact k /\ k SUBSET om /\ (!z. ~(z IN k) ==> chi z = &0) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!z i j. z IN k /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> a z$i$j = A z$i$j * inv(rho z))
     ==> wan_gweak a (\z. vec 0) (\z. &0) (wan_locf rho A B C Fs U K chi)
           (wan_locg a chi U) (\z. chi z % lift(U z))
           (\j z. wan_dpart j chi z % lift(U z) + chi z % lift(K j z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL WAN_PREG_L2) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  REWRITE_TAC[wan_gweak] THEN
  X_GEN_TAC `psi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  REWRITE_TAC[VEC_COMPONENT; VECTOR_MUL_LZERO; VSUM_0; VECTOR_ADD_LID] THEN
  MP_TAC(ISPECL
   [`psi:real^(N,1)finite_sum->real`;
    `\z. (chi:real^(N,1)finite_sum->real) z % lift((U:real^(N,1)finite_sum->real) z)`;
    `\i z. vsum(1..dimindex(:N))
             (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                  (wan_dpart j (chi:real^(N,1)finite_sum->real) z %
                   lift((U:real^(N,1)finite_sum->real) z) +
                   chi z % lift((K:num->real^(N,1)finite_sum->real) j z))) +
           wan_locg a chi U i z`;
    `wan_locf (rho:real^(N,1)finite_sum->real) A B C Fs U K chi`;
    `dimindex(:N) + 1`; `dimindex(:N)`] WAN_GWEAK_INTEGRAND_INTEGRABLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_L2_LLOC] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_LLOC_ADD THEN ASM_SIMP_TAC[WAN_L2_LLOC; ETA_AX] THEN
    MATCH_MP_TAC WAN_LLOC_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_SIMP_TAC[WAN_L2_LLOC] THEN
    MP_TAC(ISPEC `\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j` WAN_CC_CONTINUOUS) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `chi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                WAN_LOCE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[wan_locf; wan_locg] THEN
  ABBREV_TAC `eta = wan_loce (rho:real^(N,1)finite_sum->real) chi` THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `!z. (chi:real^(N,1)finite_sum->real) z = rho z * eta z /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> (a:real^(N,1)finite_sum->real^N^N) z$i$j * chi z =
                   eta z * (A:real^(N,1)finite_sum->real^N^N) z$i$j)`
  (LABEL_TAC "rel") THENL
   [GEN_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN k` THENL
     [SUBGOAL_THEN `&0 < (rho:real^(N,1)finite_sum->real) z` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  USE_THEN "rel" (fun th -> REWRITE_TAC[GEN `z:real^(N,1)finite_sum`
    (MATCH_MP (ISPECL [`psi:real^(N,1)finite_sum->real`; `eta:real^(N,1)finite_sum->real`;
                       `chi:real^(N,1)finite_sum->real`; `rho:real^(N,1)finite_sum->real`;
                       `U:real^(N,1)finite_sum->real`; `K:num->real^(N,1)finite_sum->real`;
                       `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
                       `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
                       `a:real^(N,1)finite_sum->real^N^N`; `z:real^(N,1)finite_sum`]
                      WAN_PREG_INTEGRAND) (SPEC `z:real^(N,1)finite_sum` th))]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real`;
                 `eta:real^(N,1)finite_sum->real`] WAN_TEST_PRODUCT_UNIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "prod")) THEN
  UNDISCH_TAC `wan_pweak om (rho:real^(N,1)finite_sum->real) A B C Fs U K` THEN
  REWRITE_TAC[wan_pweak] THEN
  DISCH_THEN(MP_TAC o SPEC `\x. (psi:real^(N,1)finite_sum->real) x * eta x`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. wan_tder (\x. (psi:real^(N,1)finite_sum->real) x * eta x) z =
        wan_dpart (dimindex(:N) + 1) psi z * eta z +
        psi z * wan_dpart (dimindex(:N) + 1) eta z`
  (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "prod" (fun th -> REWRITE_TAC[WAN_TDER_DPART; th]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. sum(1..dimindex(:N))
          (\i. sum(1..dimindex(:N))
                 (\j. (A:real^(N,1)finite_sum->real^N^N) z$i$j *
                      (K:num->real^(N,1)finite_sum->real) j z *
                      wan_xder i (\x. (psi:real^(N,1)finite_sum->real) x * eta x) z)) =
        sum(1..dimindex(:N))
          (\i. sum(1..dimindex(:N))
                 (\j. A z$i$j * K j z *
                      (wan_dpart i psi z * eta z + psi z * wan_dpart i eta z)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[WAN_XDER_DPART] THEN USE_THEN "prod" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC WAN_PREG_FINISH THEN
  MAP_EVERY EXISTS_TAC [`om:real^(N,1)finite_sum->bool`; `k:real^(N,1)finite_sum->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID; SUM_0; REAL_SUB_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_PEN_CCS_INTEGRABLE THEN EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN
  ASM_SIMP_TAC[REAL_MUL_RZERO] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                 `\x. (psi:real^(N,1)finite_sum->real) x * eta x`;
                 `Fs:real^(N,1)finite_sum->real`] WAN_TEST_SMUL) THEN
  ASM_REWRITE_TAC[wan_test] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    fst(strip_comb(concl th)) = `smooth_map_on:(real^(N,1)finite_sum->bool)->
       (real^(N,1)finite_sum->real^1)->bool` &&
    can (find_term ((=) `Fs:real^(N,1)finite_sum->real`)) (concl th) &&
    can (find_term ((=) `psi:real^(N,1)finite_sum->real`)) (concl th))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The bootstrap.  Regularity classes of the localised                     *)
(* data (generic in the class), the spatial bootstrap over all cutoffs     *)
(* (WAN_PSTEP_BOOT), the time bootstrap (WAN_TIME_BOOT), local smooth       *)
(* representatives and WAN_PAR_REG_W.                                        *)
(* ========================================================================= *)

let WAN_WPD_CUTOFF = prove
 (`!(s:real^M->bool) i (u:real^M->real^K) v zeta.
     open s /\ wan_wpd s i u v /\ wan_test s zeta
     ==> wan_wpd (:real^M) i (\x. zeta x % u x)
                 (\x. wan_dpart i zeta x % u x + zeta x % v x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `i:num`; `u:real^M->real^K`; `v:real^M->real^K`;
                 `zeta:real^M->real`] WAN_WPD_ZERO_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\x. if x IN s then (zeta:real^M->real) x % (u:real^M->real^K) x else vec 0) =
    (\x. zeta x % u x) /\
    (\x. if x IN s then wan_dpart i zeta x % u x + zeta x % (v:real^M->real^K) x
         else vec 0) =
    (\x. wan_dpart i zeta x % u x + zeta x % v x)`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  (SUBGOAL_THEN `~((x:real^M) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;

let WAN_LOCF_CLASS = prove
 (`!(cls:(real^(N,1)finite_sum->real^1)->bool) om rho A B C Fs
    (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real) chi.
     (!u v. cls u /\ cls v ==> cls (\x. u x + v x)) /\
     (!u v. cls u /\ cls v ==> cls (\x. u x - v x)) /\
     (!u:num->real^(N,1)finite_sum->real^1 t.
         FINITE t /\ (!i. i IN t ==> cls (u i)) ==> cls (\x. vsum t (\i. u i x))) /\
     (!phi. wan_test (:real^(N,1)finite_sum) phi ==> cls (\x. lift(phi x))) /\
     (!m. wan_test om m ==> cls (\z. m z % lift(U z))) /\
     (!m j. wan_test om m /\ 1 <= j /\ j <= dimindex(:N)
            ==> cls (\z. m z % lift(K j z))) /\
     wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\ wan_test om chi
     ==> cls (wan_locf rho A B C Fs U K chi)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "add") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
   (CONJUNCTS_THEN2 (LABEL_TAC "vsum") (CONJUNCTS_THEN2 (LABEL_TAC "test")
   (CONJUNCTS_THEN2 (LABEL_TAC "uterm") (CONJUNCTS_THEN2 (LABEL_TAC "kterm")
    STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT o
    check (fun th -> concl th = `wan_test om (chi:real^(N,1)finite_sum->real)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `chi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                WAN_LOCE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[wan_locf] THEN
  ABBREV_TAC `eta = wan_loce (rho:real^(N,1)finite_sum->real) chi` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `(!j. 1 <= j /\ j <= dimindex(:N)
         ==> smooth_map_on om (\z. lift((B:real^(N,1)finite_sum->real^N) z$j))) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> smooth_map_on om (\z. lift((A:real^(N,1)finite_sum->real^N^N) z$i$j)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`]
                    LRG_SMOOTH_VECTORIZE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m (g:real^(N,1)finite_sum->real).
      wan_test om m /\ smooth_map_on om (\z. lift(g z))
      ==> wan_test om (\z. m z * g z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `m:real^(N,1)finite_sum->real`;
                   `g:real^(N,1)finite_sum->real`] WAN_TEST_SMUL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. wan_test om (wan_dpart i (eta:real^(N,1)finite_sum->real))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_TEST_DPART_OPEN]; ALL_TAC] THEN
  USE_THEN "add" MATCH_MP_TAC THEN CONJ_TAC THENL
   [USE_THEN "uterm" MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  USE_THEN "add" MATCH_MP_TAC THEN CONJ_TAC THENL
   [USE_THEN "uterm" MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  USE_THEN "sub" MATCH_MP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "test" MATCH_MP_TAC THEN MATCH_MP_TAC WAN_TEST_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX]] THEN
  USE_THEN "sub" MATCH_MP_TAC THEN CONJ_TAC THEN
  USE_THEN "vsum" MATCH_MP_TAC THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "kterm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "vsum" MATCH_MP_TAC THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "kterm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]]);;

let WAN_LOCG_CLASS = prove
 (`!(cls:(real^(N,1)finite_sum->real^1)->bool) om (a:real^(N,1)finite_sum->real^N^N) chi
    (U:real^(N,1)finite_sum->real) i.
     (!u:num->real^(N,1)finite_sum->real^1 t.
         FINITE t /\ (!i. i IN t ==> cls (u i)) ==> cls (\x. vsum t (\i. u i x))) /\
     (!u. cls u ==> cls (\x. --(u x))) /\
     (!m. wan_test om m ==> cls (\z. m z % lift(U z))) /\
     open om /\ wan_test om chi /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_cc (\z. a z$i$j))
     ==> cls (wan_locg a chi U i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vsum") (CONJUNCTS_THEN2 (LABEL_TAC "neg")
    (CONJUNCTS_THEN2 (LABEL_TAC "uterm") STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[wan_locg] THEN
  USE_THEN "neg" MATCH_MP_TAC THEN USE_THEN "vsum" MATCH_MP_TAC THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN USE_THEN "uterm" MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                 `wan_dpart j (chi:real^(N,1)finite_sum->real)`;
                 `\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j`] WAN_TEST_SMUL) THEN
  ASM_SIMP_TAC[WAN_TEST_DPART_OPEN] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  MP_TAC(ISPEC `\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j` WAN_CC_SMOOTH) THEN
  ASM_SIMP_TAC[]);;

let WAN_PREG_K_HD = prove
 (`!(om:real^(N,1)finite_sum->bool) (U:real^(N,1)finite_sum->real)
    (K:num->real^(N,1)finite_sum->real) s m j.
     open om /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> wan_wpd om j (\z. lift(U z)) (\z. lift(K j z))) /\
     (!m. wan_test om m ==> wan_hd (1..dimindex(:N)) (SUC s) (\z. m z % lift(U z))) /\
     wan_test om m /\ 1 <= j /\ j <= dimindex(:N)
     ==> wan_hd (1..dimindex(:N)) s (\z. m z % lift(K j z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `j:num`;
                 `\z. lift((U:real^(N,1)finite_sum->real) z)`;
                 `\z. lift((K:num->real^(N,1)finite_sum->real) j z)`;
                 `m:real^(N,1)finite_sum->real`] WAN_WPD_CUTOFF) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `wan_hd (1..dimindex(:N)) s
      (\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
           lift((U:real^(N,1)finite_sum->real) x) +
           m x % lift((K:num->real^(N,1)finite_sum->real) j x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_HD_WPD THEN
    MAP_EVERY EXISTS_TAC
     [`\z. (m:real^(N,1)finite_sum->real) z % lift((U:real^(N,1)finite_sum->real) z)`;
      `j:num`] THEN
    ASM_SIMP_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_hd (1..dimindex(:N)) s
      (\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
           lift((U:real^(N,1)finite_sum->real) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_HD_MONO THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `wan_dpart j (m:real^(N,1)finite_sum->real)` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `SUC s`)) (concl th))) THEN
    ASM_SIMP_TAC[WAN_TEST_DPART_OPEN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1..dimindex(:N)`; `s:num`;
                 `\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
                      lift((U:real^(N,1)finite_sum->real) x) +
                      m x % lift((K:num->real^(N,1)finite_sum->real) j x)`;
                 `\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
                      lift((U:real^(N,1)finite_sum->real) x)`] WAN_HD_SUB) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`]);;

let WAN_PREG_K_HT = prove
 (`!(om:real^(N,1)finite_sum->bool) (U:real^(N,1)finite_sum->real)
    (K:num->real^(N,1)finite_sum->real) n m j.
     open om /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> wan_wpd om j (\z. lift(U z)) (\z. lift(K j z))) /\
     (!m. wan_test om m ==> wan_ht n (\z. m z % lift(U z))) /\
     wan_test om m /\ 1 <= j /\ j <= dimindex(:N)
     ==> wan_ht n (\z. m z % lift(K j z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `j:num`;
                 `\z. lift((U:real^(N,1)finite_sum->real) z)`;
                 `\z. lift((K:num->real^(N,1)finite_sum->real) j z)`;
                 `m:real^(N,1)finite_sum->real`] WAN_WPD_CUTOFF) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `wan_ht n
      (\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
           lift((U:real^(N,1)finite_sum->real) x) +
           m x % lift((K:num->real^(N,1)finite_sum->real) j x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_HT_DERIV_X THEN
    MAP_EVERY EXISTS_TAC
     [`\z. (m:real^(N,1)finite_sum->real) z % lift((U:real^(N,1)finite_sum->real) z)`;
      `j:num`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_ht n
      (\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
           lift((U:real^(N,1)finite_sum->real) x))`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `wan_dpart j (m:real^(N,1)finite_sum->real)` (ASSUME
     `!m. wan_test om m
          ==> wan_ht n (\z. m z % lift((U:real^(N,1)finite_sum->real) z))`)) THEN
    ASM_SIMP_TAC[WAN_TEST_DPART_OPEN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`;
                 `\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
                      lift((U:real^(N,1)finite_sum->real) x) +
                      m x % lift((K:num->real^(N,1)finite_sum->real) j x)`;
                 `\x. wan_dpart j (m:real^(N,1)finite_sum->real) x %
                      lift((U:real^(N,1)finite_sum->real) x)`] WAN_HT_SUB) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`]);;

let WAN_PREG_SETUP = prove
 (`!(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
    (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
    (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real) chi.
     wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
     wan_l2loc om (\z. lift(U z)) /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> wan_wpd om j (\z. lift(U z)) (\z. lift(K j z)) /\
              wan_l2loc om (\z. lift(K j z))) /\
     wan_pweak om rho A B C Fs U K /\ wan_test om chi
     ==> ?a lam k.
           &0 < lam /\ compact k /\
           (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                  ==> wan_cc (\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j)) /\
           (!z xi. lam * norm xi pow 2 <= xi dot (a z ** xi)) /\
           (\z. chi z % lift(U z)) IN lspace (:real^(N,1)finite_sum) (&2) /\
           (!z. ~(z IN k) ==> chi z % lift(U z) = vec 0) /\
           (!j. 1 <= j /\ j <= dimindex(:N)
                ==> (\z. wan_dpart j chi z % lift(U z) + chi z % lift(K j z)) IN
                    lspace (:real^(N,1)finite_sum) (&2) /\
                    wan_wpd (:real^(N,1)finite_sum) j (\z. chi z % lift(U z))
                      (\z. wan_dpart j chi z % lift(U z) + chi z % lift(K j z))) /\
           (!j z. ~(z IN k)
                  ==> wan_dpart j chi z % lift(U z) + chi z % lift(K j z) = vec 0) /\
           (!z. ~(z IN k) ==> wan_locf rho A B C Fs U K chi z = vec 0) /\
           (!i z. ~(z IN k) ==> wan_locg a chi U i z = vec 0) /\
           wan_gweak a (\z. vec 0) (\z. &0) (wan_locf rho A B C Fs U K chi)
             (wan_locg a chi U) (\z. chi z % lift(U z))
             (\j z. wan_dpart j chi z % lift(U z) + chi z % lift(K j z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT o
    check (fun th -> concl th = `wan_test om (chi:real^(N,1)finite_sum->real)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `A:real^(N,1)finite_sum->real^N^N`; `k:real^(N,1)finite_sum->bool`]
                WAN_PREG_COEFF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^(N,1)finite_sum->real^N^N`
    (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:real^(N,1)finite_sum->real^N^N`; `lam:real`;
                        `k:real^(N,1)finite_sum->bool`] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
                 `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
                 `U:real^(N,1)finite_sum->real`; `K:num->real^(N,1)finite_sum->real`;
                 `chi:real^(N,1)finite_sum->real`; `a:real^(N,1)finite_sum->real^N^N`;
                 `k:real^(N,1)finite_sum->bool`] WAN_PREG_L2) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
                 `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
                 `U:real^(N,1)finite_sum->real`; `K:num->real^(N,1)finite_sum->real`;
                 `chi:real^(N,1)finite_sum->real`; `a:real^(N,1)finite_sum->real^N^N`;
                 `k:real^(N,1)finite_sum->bool`] WAN_PREG_GWEAK) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_CUTOFF THEN
  EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[]);;

let WAN_PREG_HXA = prove
 (`!(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
    (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
    (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real).
     wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
     wan_l2loc om (\z. lift(U z)) /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> wan_wpd om j (\z. lift(U z)) (\z. lift(K j z)) /\
              wan_l2loc om (\z. lift(K j z))) /\
     wan_pweak om rho A B C Fs U K
     ==> !s chi. wan_test om chi
                 ==> wan_hd (1..dimindex(:N)) s (\z. chi z % lift(U z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  SUBGOAL_THEN
   `!s chi. wan_test om chi
            ==> wan_hd (1..dimindex(:N)) (SUC s)
                  (\z. chi z % lift((U:real^(N,1)finite_sum->real) z))`
  ASSUME_TAC THENL
   [ALL_TAC; REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HD_MONO THEN ASM_SIMP_TAC[]] THEN
  INDUCT_TAC THEN X_GEN_TAC `chi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
                 `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
                 `U:real^(N,1)finite_sum->real`; `K:num->real^(N,1)finite_sum->real`;
                 `chi:real^(N,1)finite_sum->real`] WAN_PREG_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^(N,1)finite_sum->real^N^N`
    (X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool`
      STRIP_ASSUME_TAC))) THENL
   [REWRITE_TAC[wan_hd; IN_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    EXISTS_TAC `\z. wan_dpart j (chi:real^(N,1)finite_sum->real) z %
                    lift((U:real^(N,1)finite_sum->real) z) +
                    chi z % lift((K:num->real^(N,1)finite_sum->real) j z)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `a:real^(N,1)finite_sum->real^N^N`;
                 `\z:real^(N,1)finite_sum. vec 0:real^N`;
                 `\z:real^(N,1)finite_sum. &0`] WAN_PSTEP_BOOT) THEN
  ASM_REWRITE_TAC[VEC_COMPONENT; WAN_CC_CONST] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`s:num`; `wan_locf (rho:real^(N,1)finite_sum->real) A B C Fs U K chi`;
    `wan_locg (a:real^(N,1)finite_sum->real^N^N) chi U`;
    `\z. (chi:real^(N,1)finite_sum->real) z % lift((U:real^(N,1)finite_sum->real) z)`;
    `\j z. wan_dpart j (chi:real^(N,1)finite_sum->real) z %
           lift((U:real^(N,1)finite_sum->real) z) +
           chi z % lift((K:num->real^(N,1)finite_sum->real) j z)`;
    `k:real^(N,1)finite_sum->bool`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LOCF_CLASS THEN EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[WAN_HD_ADD];
      SIMP_TAC[WAN_HD_SUB];
      SIMP_TAC[WAN_HD_VSUM];
      SIMP_TAC[WAN_HD_TEST];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HD_MONO THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_PREG_K_HD THEN
      MAP_EVERY EXISTS_TAC [`om:real^(N,1)finite_sum->bool`;
                            `U:real^(N,1)finite_sum->real`] THEN
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LOCG_CLASS THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[WAN_HD_VSUM; WAN_HD_NEG]]);;

let WAN_PREG_HT = prove
 (`!(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
    (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
    (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real).
     wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
     wan_l2loc om (\z. lift(U z)) /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> wan_wpd om j (\z. lift(U z)) (\z. lift(K j z)) /\
              wan_l2loc om (\z. lift(K j z))) /\
     wan_pweak om rho A B C Fs U K
     ==> !n chi. wan_test om chi ==> wan_ht n (\z. chi z % lift(U z))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WAN_PREG_HXA) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  SUBGOAL_THEN `!n (u:real^(N,1)finite_sum->real^1). wan_ht n u ==> wan_ht n (\x. --(u x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `u:real^(N,1)finite_sum->real^1`; `--(&1)`] WAN_HT_CMUL) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[wan_ht; wan_hxa] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `chi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
                 `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
                 `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
                 `U:real^(N,1)finite_sum->real`; `K:num->real^(N,1)finite_sum->real`;
                 `chi:real^(N,1)finite_sum->real`] WAN_PREG_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^(N,1)finite_sum->real^N^N`
    (X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool`
      STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`a:real^(N,1)finite_sum->real^N^N`;
                 `\z:real^(N,1)finite_sum. vec 0:real^N`;
                 `\z:real^(N,1)finite_sum. &0`] WAN_TIME_BOOT) THEN
  ASM_REWRITE_TAC[VEC_COMPONENT; WAN_CC_CONST] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`n:num`; `wan_locf (rho:real^(N,1)finite_sum->real) A B C Fs U K chi`;
    `wan_locg (a:real^(N,1)finite_sum->real^N^N) chi U`;
    `\z. (chi:real^(N,1)finite_sum->real) z % lift((U:real^(N,1)finite_sum->real) z)`;
    `\j z. wan_dpart j (chi:real^(N,1)finite_sum->real) z %
           lift((U:real^(N,1)finite_sum->real) z) +
           chi z % lift((K:num->real^(N,1)finite_sum->real) j z)`]) THEN
  ASM_SIMP_TAC[wan_hxa] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LOCF_CLASS THEN EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[WAN_HT_ADD];
      SIMP_TAC[WAN_HT_SUB];
      SIMP_TAC[WAN_HT_VSUM];
      SIMP_TAC[WAN_HT_TEST];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_PREG_K_HT THEN
      MAP_EVERY EXISTS_TAC [`om:real^(N,1)finite_sum->bool`;
                            `U:real^(N,1)finite_sum->real`] THEN
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LOCG_CLASS THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[WAN_HT_VSUM]]);;

let WAN_PREG_LOCAL = prove
 (`!(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
    (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
    (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
    (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real).
     wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
     wan_l2loc om (\z. lift(U z)) /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> wan_wpd om j (\z. lift(U z)) (\z. lift(K j z)) /\
              wan_l2loc om (\z. lift(K j z))) /\
     wan_pweak om rho A B C Fs U K
     ==> !chi. wan_test om chi
               ==> ?w. smooth_map_on (:real^(N,1)finite_sum) w /\
                       negligible {z | ~(chi z % lift(U z) = w z)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WAN_PREG_HT) THEN
  X_GEN_TAC `chi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT o
    check (fun th -> concl th = `wan_test om (chi:real^(N,1)finite_sum->real)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC WAN_HD_ALL_SMOOTH THEN EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO] THEN GEN_TAC THEN MATCH_MP_TAC WAN_HT_ALL_HD THEN
  ASM_SIMP_TAC[]);;

let WAN_PAR_REG_W = prove
 (`!n:N->bool. WAN_PAR_REG_W_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[WAN_PAR_REG_W_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
    `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
    `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
    `U:real^(N,1)finite_sum->real`; `K:num->real^(N,1)finite_sum->real`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "loc" o MATCH_MP WAN_PREG_LOCAL) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                 `\z. lift((U:real^(N,1)finite_sum->real) z)`] WAN_LOCAL_SMOOTH_AE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z0:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(SPEC `z0:real^(N,1)finite_sum` (REWRITE_RULE[OPEN_CONTAINS_BALL]
      (ASSUME `open(om:real^(N,1)finite_sum->bool)`))) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `cball(z0:real^(N,1)finite_sum,e / &2)`] WAN_SMOOTH_URYSOHN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^(N,1)finite_sum,e)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `chi:real^(N,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `wan_test om (chi:real^(N,1)finite_sum->real)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`ball(z0:real^(N,1)finite_sum,e / &2)`;
                          `w:real^(N,1)finite_sum->real^1`] THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^(N,1)finite_sum,e)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{z | ~((chi:real^(N,1)finite_sum->real) z %
                         lift((U:real^(N,1)finite_sum->real) z) =
                         (w:real^(N,1)finite_sum->real^1) z)}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(chi:real^(N,1)finite_sum->real) z = &1`
        (fun th -> ASM_REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`z0:real^(N,1)finite_sum`; `e / &2`] BALL_SUBSET_CBALL) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z. drop((w:real^(N,1)finite_sum->real^1) z)` THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP]);;

(* ========================================================================= *)
(* WAN_PAR_REG (locally Lipschitz U with its a.e. spatial                  *)
(* gradient) from WAN_PAR_REG_W and WAN_LIP_W12; continuity upgrades the   *)
(* a.e. equality to equality.                                                *)
(* ========================================================================= *)

let WAN_L2LOC_SPIKE = prove
 (`!(s:real^M->bool) (v:real^M->real^K) v'.
     wan_l2loc s v /\ negligible {x | x IN s /\ ~(v x = v' x)}
     ==> wan_l2loc s v'`,
  REWRITE_TAC[wan_l2loc] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^M->real^K) IN lspace k (&2)` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`v:real^M->real^K`; `v':real^M->real^K`;
                   `{x | x IN s /\ ~((v:real^M->real^K) x = v' x)}`; `k:real^M->bool`]
                  MEASURABLE_ON_SPIKE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`\x. lift(norm((v:real^M->real^K) x) rpow &2)`;
                   `\x. lift(norm((v':real^M->real^K) x) rpow &2)`;
                   `{x | x IN s /\ ~((v:real^M->real^K) x = v' x)}`; `k:real^M->bool`]
                  INTEGRABLE_SPIKE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^M->real^K) x = v' x` (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[]]);;

let WAN_PAR_REG = prove
 (`!n:N->bool. WAN_PAR_REG_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[WAN_PAR_REG_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
    `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
    `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
    `U:real^(N,1)finite_sum->real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_pcoeff]) THEN
  SUBGOAL_THEN `(\z. lift((U:real^(N,1)finite_sum->real) z)) continuous_on om`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(ISPEC `(:(N,1)finite_sum)` WAN_LIP_W12) THEN
  REWRITE_TAC[WAN_LIP_W12_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`om:real^(N,1)finite_sum->bool`;
                             `U:real^(N,1)finite_sum->real`]) THEN
  ASM_REWRITE_TAC[num_CONV `1`; wan_hk] THEN REWRITE_TAC[GSYM ONE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hk"))
    (LABEL_TAC "wpd")) THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> wan_wpd om j (\z. lift((U:real^(N,1)finite_sum->real) z))
                         (\z. lift(wan_xder j U z)) /\
            wan_l2loc om (\z. lift(wan_xder j U z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(\z. lift(wan_xder j (U:real^(N,1)finite_sum->real) z)) =
                  (\z. lift(wan_dpart j U z))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[FUN_EQ_THM; WAN_XDER_DPART]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= j /\ j <= dimindex(:(N,1)finite_sum)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[WAN_SPACE_INDEX]; ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_wpd om j (\z. lift((U:real^(N,1)finite_sum->real) z))
                   (\z. lift(wan_dpart j U z))`
    ASSUME_TAC THENL
     [USE_THEN "wpd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "hk" (fun th -> MP_TAC(MATCH_MP (SPEC `j:num` th)
      (ASSUME `1 <= j /\ j <= dimindex(:(N,1)finite_sum)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC WAN_L2LOC_SPIKE THEN EXISTS_TAC `v:real^(N,1)finite_sum->real^1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_WPD_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `\z. lift((U:real^(N,1)finite_sum->real) z)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `n:N->bool` WAN_PAR_REG_W) THEN REWRITE_TAC[WAN_PAR_REG_W_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`om:real^(N,1)finite_sum->bool`; `rho:real^(N,1)finite_sum->real`;
    `A:real^(N,1)finite_sum->real^N^N`; `B:real^(N,1)finite_sum->real^N`;
    `C:real^(N,1)finite_sum->real`; `Fs:real^(N,1)finite_sum->real`;
    `U:real^(N,1)finite_sum->real`; `\j z. wan_xder j (U:real^(N,1)finite_sum->real) z`]) THEN
  ASM_SIMP_TAC[WAN_CONTINUOUS_ON_L2LOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(N,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. lift((W:real^(N,1)finite_sum->real) z)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WAN_CONT_AE_EQ_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `negligible:(real^(N,1)finite_sum->bool)->bool`)) (concl th))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; LIFT_EQ] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* WAN_CONJ_HEAT_REG.  In a chart with time coordinate tau                 *)
(* and metrics G(x,tau), the weak conjugate heat equation (weights          *)
(* sqrt(det G)) is wan_pweak with rho = sqrt(det G), A = rho G^-1, B = 0,  *)
(* C = d_tau rho - R rho, Fs = 0, after integration by parts in tau        *)
(* (WAN_LIP_IBP); WAN_PAR_REG then gives smoothness.                        *)
(* ========================================================================= *)

let WAN_LIP_TDER_IBP = prove
 (`!(om:real^(N,1)finite_sum->bool) U m.
     open om /\ wan_loclip om U /\ wan_test om m
     ==> (\x. lift(wan_tder U x * m x)) absolutely_integrable_on om /\
         integral om (\x. lift(U x * wan_tder m x)) =
         --(integral om (\x. lift(wan_tder U x * m x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:(N,1)finite_sum)` WAN_LIP_IBP) THEN
  REWRITE_TAC[WAN_LIP_IBP_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`om:real^(N,1)finite_sum->bool`;
    `U:real^(N,1)finite_sum->real`; `m:real^(N,1)finite_sum->real`;
    `pastecart (vec 0:real^N) (lift(&1))`]) THEN
  ASM_REWRITE_TAC[wan_tder] THEN SIMP_TAC[]);;

let WAN_LIP_XDER_PAIRING = prove
 (`!(om:real^(N,1)finite_sum->bool) U m i.
     open om /\ wan_loclip om U /\ wan_test om m
     ==> (\x. lift(wan_xder i U x * m x)) absolutely_integrable_on om`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:(N,1)finite_sum)` WAN_LIP_IBP) THEN
  REWRITE_TAC[WAN_LIP_IBP_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`om:real^(N,1)finite_sum->bool`;
    `U:real^(N,1)finite_sum->real`; `m:real^(N,1)finite_sum->real`;
    `pastecart (basis i:real^N) (vec 0:real^1)`]) THEN
  ASM_SIMP_TAC[wan_xder]);;

let WAN_SUM_SWAP_SYM = prove
 (`!n (g:num->num->real) (a:num->real) b.
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> g i j = g j i)
     ==> sum(1..n) (\i. sum(1..n) (\j. g i j * a j * b i)) =
         sum(1..n) (\i. sum(1..n) (\j. g i j * a i * b j))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let WAN_CONJ_PWEAK_GEN = prove
 (`!(om:real^(N,1)finite_sum->bool) rho (Gi:real^(N,1)finite_sum->real^N^N) R U.
     open om /\ smooth_map_on om (\z. lift(rho z)) /\ smooth_map_on om (\z. lift(R z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on om (\z. lift(Gi z$i$j))) /\
     (!z i j. z IN om /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> Gi z$i$j = Gi z$j$i) /\
     wan_loclip om U /\
     (!phi. wan_test om phi
            ==> integral om
                  (\z. lift((phi z * wan_tder U z + R z * phi z * U z +
                             sum(1..dimindex(:N))
                                (\i. sum(1..dimindex(:N))
                                       (\j. Gi z$i$j * wan_xder i U z *
                                            wan_xder j phi z))) * rho z)) = vec 0)
     ==> wan_pweak om rho (\z. rho z %% Gi z) (\z. vec 0)
           (\z. wan_tder rho z - R z * rho z) (\z. &0) U (\j z. wan_xder j U z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))))))) THEN
  REWRITE_TAC[wan_pweak] THEN X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN
  DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; LIFT_NUM; INTEGRAL_0; VEC_COMPONENT;
              MATRIX_CMUL_COMPONENT; SUM_0; REAL_ADD_LID] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                 `rho:real^(N,1)finite_sum->real`] WAN_TEST_SMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "prod")) THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `U:real^(N,1)finite_sum->real`;
                 `\x. (phi:real^(N,1)finite_sum->real) x * rho x`] WAN_LIP_TDER_IBP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ibp")) THEN
  USE_THEN "H" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `wan_test om (phi:real^(N,1)finite_sum->real)`))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `wan_lloc om (\x. lift((U:real^(N,1)finite_sum->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_ON_LLOC THEN ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((U:real^(N,1)finite_sum->real) z *
              wan_tder (\x. (phi:real^(N,1)finite_sum->real) x * rho x) z))
    integrable_on om`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\x. (phi:real^(N,1)finite_sum->real) x * rho x`;
                   `\x. lift((U:real^(N,1)finite_sum->real) x)`] WAN_TEST_PAIRING) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `dimindex(:N) + 1` o CONJUNCT2) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; WAN_TDER_DPART; GSYM LIFT_CMUL] THEN GEN_TAC THEN
    AP_TERM_TAC THEN USE_THEN "prod" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((phi z * wan_tder (U:real^(N,1)finite_sum->real) z +
               (R:real^(N,1)finite_sum->real) z * phi z * U z +
               sum(1..dimindex(:N))
                  (\i. sum(1..dimindex(:N))
                         (\j. (Gi:real^(N,1)finite_sum->real^N^N) z$i$j *
                              wan_xder i U z * wan_xder j phi z))) * rho z))
    integrable_on om`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    SUBGOAL_THEN
     `(\z. lift((phi z * wan_tder (U:real^(N,1)finite_sum->real) z +
                 (R:real^(N,1)finite_sum->real) z * phi z * U z +
                 sum(1..dimindex(:N))
                    (\i. sum(1..dimindex(:N))
                           (\j. (Gi:real^(N,1)finite_sum->real^N^N) z$i$j *
                                wan_xder i U z * wan_xder j phi z))) * rho z)) =
      (\z. lift(wan_tder U z * (phi z * rho z)) +
           ((phi z * (R z * rho z)) % lift(U z) +
            vsum(1..dimindex(:N))
              (\i. vsum(1..dimindex(:N))
                     (\j. lift(wan_xder i U z *
                               (wan_dpart j phi z * (Gi z$i$j * rho z)))))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_VSUM; LIFT_DROP; o_DEF] THEN
      SUBGOAL_THEN
       `sum(1..dimindex(:N))
          (\i. sum(1..dimindex(:N))
                 (\j. (Gi:real^(N,1)finite_sum->real^N^N) z$i$j *
                      wan_xder i (U:real^(N,1)finite_sum->real) z *
                      wan_xder j (phi:real^(N,1)finite_sum->real) z)) * rho z =
        sum(1..dimindex(:N))
          (\i. sum(1..dimindex(:N))
                 (\j. wan_xder i U z * (wan_dpart j phi z * (Gi z$i$j * rho z))))`
      (fun th -> REWRITE_TAC[REAL_ADD_RDISTRIB; th]) THENL
       [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[WAN_XDER_DPART] THEN REAL_ARITH_TAC;
        ABBREV_TAC
         `S = sum(1..dimindex(:N))
                (\i. sum(1..dimindex(:N))
                       (\j. wan_xder i (U:real^(N,1)finite_sum->real) z *
                            (wan_dpart j (phi:real^(N,1)finite_sum->real) z *
                             ((Gi:real^(N,1)finite_sum->real^N^N) z$i$j * rho z))))` THEN
        CONV_TAC REAL_RING];
      ALL_TAC] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `\z. (R:real^(N,1)finite_sum->real) z * rho z`] WAN_TEST_SMUL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                       `\z. lift((R:real^(N,1)finite_sum->real) z)`;
                       `\z. lift((rho:real^(N,1)finite_sum->real) z)`]
                      SMOOTH_MAP_ON_LIFT_MUL) THEN
        ASM_SIMP_TAC[LIFT_DROP; ETA_AX];
        DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\x. (phi:real^(N,1)finite_sum->real) x *
                          (R:real^(N,1)finite_sum->real) x * rho x`;
                     `\x. lift((U:real^(N,1)finite_sum->real) x)`] WAN_TEST_PAIRING) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `U:real^(N,1)finite_sum->real`;
                     `\x. wan_dpart j (phi:real^(N,1)finite_sum->real) x *
                          (Gi:real^(N,1)finite_sum->real^N^N) x$i$j * rho x`;
                     `i:num`] WAN_LIP_XDER_PAIRING) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `wan_dpart j (phi:real^(N,1)finite_sum->real)`;
                     `\x. (Gi:real^(N,1)finite_sum->real^N^N) x$i$j * rho x`]
                    WAN_TEST_SMUL) THEN
      ASM_SIMP_TAC[WAN_TEST_DPART_OPEN] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\z. lift((Gi:real^(N,1)finite_sum->real^N^N) z$i$j)`;
                     `\z. lift((rho:real^(N,1)finite_sum->real) z)`]
                    SMOOTH_MAP_ON_LIFT_MUL) THEN
      ASM_SIMP_TAC[LIFT_DROP; ETA_AX]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `integral om
      (\z. (lift((U:real^(N,1)finite_sum->real) z *
                 wan_tder (\x. (phi:real^(N,1)finite_sum->real) x * rho x) z) +
            lift(wan_tder U z * (phi z * rho z))) -
           lift((phi z * wan_tder U z +
                 (R:real^(N,1)finite_sum->real) z * phi z * U z +
                 sum(1..dimindex(:N))
                    (\i. sum(1..dimindex(:N))
                           (\j. (Gi:real^(N,1)finite_sum->real^N^N) z$i$j *
                                wan_xder i U z * wan_xder j phi z))) * rho z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_SUB; LIFT_EQ] THEN
    USE_THEN "prod" (fun th -> REWRITE_TAC[WAN_TDER_DPART; th]) THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\i. sum(1..dimindex(:N))
               (\j. (rho z * (Gi:real^(N,1)finite_sum->real^N^N) z$i$j) *
                    wan_xder j (U:real^(N,1)finite_sum->real) z *
                    wan_xder i (phi:real^(N,1)finite_sum->real) z)) =
      rho z * sum(1..dimindex(:N))
                (\i. sum(1..dimindex(:N))
                       (\j. Gi z$i$j * wan_xder i U z * wan_xder j phi z))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`dimindex(:N)`;
                     `\i j. (Gi:real^(N,1)finite_sum->real^N^N) z$i$j`;
                     `\j. wan_xder j (U:real^(N,1)finite_sum->real) z`;
                     `\i. wan_xder i (phi:real^(N,1)finite_sum->real) z`]
                    WAN_SUM_SWAP_SYM) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `S = sum(1..dimindex(:N))
            (\i. sum(1..dimindex(:N))
                   (\j. (Gi:real^(N,1)finite_sum->real^N^N) z$i$j *
                        wan_xder i (U:real^(N,1)finite_sum->real) z *
                        wan_xder j (phi:real^(N,1)finite_sum->real) z))` THEN
    REWRITE_TAC[GSYM WAN_TDER_DPART] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRAL_ADD; INTEGRABLE_ADD;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  USE_THEN "ibp" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VECTOR_ADD_LINV; VECTOR_SUB_RZERO]);;

let WAN_CONJ_COEFF = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) R.
     open om /\
     smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\
                      !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
     smooth_map_on om (\z. lift(R z))
     ==> wan_pcoeff om (\z. sqrt(det(G z))) (\z. sqrt(det(G z)) %% matrix_inv(G z))
           (\z. vec 0) (\z. wan_tder (\z. sqrt(det(G z))) z - R z * sqrt(det(G z))) /\
         smooth_map_on om (\z. lift(sqrt(det(G z)))) /\
         (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                ==> smooth_map_on om (\z. lift(matrix_inv(G z)$i$j))) /\
         (!z i j. z IN om /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                  ==> matrix_inv(G z)$i$j = matrix_inv(G z)$j$i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN om ==> positive_definite((G:real^(N,1)finite_sum->real^N^N) z)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[positive_definite; symmetric_matrix]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN om ==> &0 < det((G:real^(N,1)finite_sum->real^N^N) z)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[DET_POSITIVE_DEFINITE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on om (\z. lift((G:real^(N,1)finite_sum->real^N^N) z$i$j))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`]
                  LRG_SMOOTH_VECTORIZE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on om (\z. lift(det((G:real^(N,1)finite_sum->real^N^N) z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[smooth_map_on]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on om (\z. lift(sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z. lift(det((G:real^(N,1)finite_sum->real^N^N) z))`]
                  SMOOTH_MAP_ON_LIFT_SQRT) THEN
    ASM_SIMP_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on om
                (\z. lift(matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `G:real^(N,1)finite_sum->real^N^N`] LRG_SMOOTH_MATRIX_INV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)`]
                  LRG_SMOOTH_VECTORIZE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z i j. z IN om /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j =
                matrix_inv(G z)$j$i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `transp(matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)) =
                  matrix_inv(G z)` MP_TAC THENL
     [REWRITE_TAC[GSYM MATRIX_INV_TRANSP] THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)`; `i:num`; `j:num`]
                    TRANSP_COMPONENT) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_pcoeff] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT];
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) %%
                        matrix_inv(G z)`] LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN DISCH_THEN SUBST1_TAC THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z. lift(sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)))`;
                   `\z. lift(matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j)`]
                  SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_SIMP_TAC[LIFT_DROP];
    X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `positive_definite(sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) %%
                        matrix_inv(G z))`
    MP_TAC THENL
     [MATCH_MP_TAC POSITIVE_DEFINITE_CMUL THEN
      ASM_SIMP_TAC[POSITIVE_DEFINITE_INV; SQRT_POS_LT];
      SIMP_TAC[positive_definite; symmetric_matrix]];
    REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    SUBGOAL_THEN
     `(\z. lift(wan_tder (\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))) z -
                (R:real^(N,1)finite_sum->real) z * sqrt(det(G z)))) =
      (\z. lift(drop(partial_derivative (dimindex(:N) + 1)
                       (\z. lift(sqrt(det(G z)))) z) -
                drop(lift(R z)) * drop(lift(sqrt(det(G z))))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; WAN_TDER_DPART; wan_dpart; partial_derivative;
                  LIFT_DROP];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `partial_derivative (dimindex(:N) + 1)
                      (\z. lift(sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))))`;
                   `\z. lift(lift((R:real^(N,1)finite_sum->real) z)$1 *
                             sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)))`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP] THEN
    ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
                    REWRITE_TAC[FUN_EQ_THM; GSYM drop; LIFT_DROP]] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z. lift((R:real^(N,1)finite_sum->real) z)`;
                   `\z. lift(sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)))`]
                  SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_SIMP_TAC[LIFT_DROP; GSYM drop]]);;

let WAN_CONJ_HEAT_REG = prove
 (`!n:N->bool. WAN_CONJ_HEAT_REG_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[WAN_CONJ_HEAT_REG_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
    `R:real^(N,1)finite_sum->real`; `U:real^(N,1)finite_sum->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `R:real^(N,1)finite_sum->real`] WAN_CONJ_COEFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `n:N->bool` WAN_PAR_REG) THEN REWRITE_TAC[WAN_PAR_REG_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))`;
    `\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) %% matrix_inv(G z)`;
    `\z:real^(N,1)finite_sum. vec 0:real^N`;
    `\z. wan_tder (\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))) z -
         (R:real^(N,1)finite_sum->real) z * sqrt(det(G z))`;
    `\z:real^(N,1)finite_sum. &0`] THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; LIFT_NUM] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`om:real^(N,1)finite_sum->bool`;
    `\z. sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))`;
    `\z. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)`;
    `R:real^(N,1)finite_sum->real`; `U:real^(N,1)finite_sum->real`]
   WAN_CONJ_PWEAK_GEN)) THEN
  ASM_REWRITE_TAC[]);;

let WAN_CONJ_HEAT_REG_3 = prove
 (`!n:3->bool. WAN_CONJ_HEAT_REG_STATEMENT n`,
  REWRITE_TAC[INST_TYPE [`:3`,`:N`] WAN_CONJ_HEAT_REG]);;

let WAN_CONJ_HEAT_REG_2 = prove
 (`!n:2->bool. WAN_CONJ_HEAT_REG_STATEMENT n`,
  REWRITE_TAC[INST_TYPE [`:2`,`:N`] WAN_CONJ_HEAT_REG]);;

