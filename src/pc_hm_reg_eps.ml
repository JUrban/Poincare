(* ========================================================================= *)
(* Unit pc_hm_reg_eps (a unit of the harmonic map regularity chain of        *)
(* pc_hm_regularity): the epsilon-regularity theorem CM_EPS_REG for smooth   *)
(* harmonic maps of small energy into a cm_target.  The first derivatives    *)
(* are bounded by HMR_EPS_E (Schoen's maximum-point argument) on every ball  *)
(* centred in ball(x,r/2); the weighted maximum argument HMR_ABSORB raises   *)
(* the order of the weighted jet bound one step at a time, linearly in the   *)
(* first-order bound, which is proportional to the square root of the        *)
(* energy.                                                                   *)
(* ========================================================================= *)

needs "src/pc_hm_reg_boot.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The order-zero weighted jet, the induction over the order, and            *)
(* CM_EPS_REG.                                                               *)
(* ========================================================================= *)

let HMR_INDEX_LISTS_0 = prove
 (`pde_index_lists 0 (:2) = {[]}`,
  REWRITE_TAC[EXTENSION; pde_index_lists; IN_ELIM_THM; IN_SING; LE; LENGTH_EQ_NIL] THEN
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[ALL]);;

let HMR_DJ0 = prove
 (`!r (u:real^2->real^K) z.
     hmr_dj 0 r u z = r * norm(partial_derivative 1 u z) + r * norm(partial_derivative 2 u z)`,
  REWRITE_TAC[hmr_dj; HMR_INDEX_LISTS_0; SUM_SING; LENGTH; iterated_partial; SUM_2] THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_POW_1]);;

(* The weighted jets of every order, linearly in the order-zero bound. *)

let HMR_DJ_ALL = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !n. ?K. &0 <= K /\
                 !s (u:real^2->real^K) x0 R A.
                    open s /\ smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
                    (!x. x IN s ==> hmr_vlap u x = hmr_fq S G u x) /\
                    &0 < R /\ cball(x0,R) SUBSET s /\ &0 <= A /\ A <= &1 /\
                    (!y. y IN ball(x0,R) ==> hmr_dj 0 (R - norm(y - x0)) u y <= A)
                    ==> !y. y IN ball(x0,R) ==> hmr_dj n (R - norm(y - x0)) u y <= K * A`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS; REAL_MUL_LID] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `K:real`] o MATCH_MP HMR_ABSORB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ab"))) THEN
  EXISTS_TAC `K2 * K` THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "ab" (MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `x0:real^2`; `R:real`;
                                 `K * A`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[];
      USE_THEN "ih" (fun th -> MATCH_MP_TAC(SPECL [`s:real^2->bool`; `u:real^2->real^K`;
                                                   `x0:real^2`; `R:real`; `A:real`] th)) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[ADD1; REAL_MUL_ASSOC]]);;

(* The order-zero bound on the half ball from the first-derivative estimate. *)

let HMR_EPS_BASE = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?e C. &0 < e /\ &0 < C /\
               !a r (u:real^2->real^K) x.
                  &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
                  wan_gdir (ball(a,r)) G u <= e /\ x IN ball(a,r / &2)
                  ==> &0 <= wan_gdir (ball(a,r)) G u /\
                      !y. y IN ball(x,r / &2)
                          ==> hmr_dj 0 (r / &2 - norm(y - x)) u y <=
                              &2 * sqrt(C * wan_gdir (ball(a,r)) G u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMR_EPS_E) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`; `x:real^2`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  ABBREV_TAC `E = wan_gdir (ball(a,r)) (G:real^K->real^K^K) (u:real^2->real^K)` THEN
  (* the energy is nonnegative *)
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real^K`] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "hmr_e"))
                           (concl th) && is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`] HMR_E_POS) THEN
    SUBGOAL_THEN `&0 < r pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= C * E` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r pow 2 * hmr_e (u:real^2->real^K) a` THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_MUL_EQ]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  ABBREV_TAC `dl = r / &2 - norm(y - x:real^2)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN UNDISCH_TAC `(y:real^2) IN ball(x,r / &2)` THEN
    REWRITE_TAC[IN_BALL; dist] THEN MP_TAC(ISPECL [`x:real^2`; `y:real^2`] NORM_SUB) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^2,dl) SUBSET ball(a,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; dist] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^2) IN ball(a,r / &2)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`a - z:real^2`; `a - x:real^2`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x - z:real^2`; `x - y:real^2`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x:real^2`; `y:real^2`] NORM_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `(a - z) - (a - x):real^2 = x - z`;
                VECTOR_ARITH `(x - z) - (x - y):real^2 = y - z`] THEN
    UNDISCH_TAC `norm(y - z:real^2) < dl` THEN
    UNDISCH_TAC `r / &2 - norm(y - x:real^2) = dl` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the energy of the small ball *)
  SUBGOAL_THEN `wan_gdir (ball(y,dl)) (G:real^K->real^K^K) (u:real^2->real^K) <= E`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC HMC_GDIR_MONO THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `dl:real`; `u:real^2->real^K`] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "hmr_e"))
                         (concl th) && is_forall (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `dl pow 2 * hmr_e (u:real^2->real^K) y <= C * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * wan_gdir (ball(y,dl)) (G:real^K->real^K^K) (u:real^2->real^K)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> dl * norm(partial_derivative i (u:real^2->real^K) y) <= sqrt(C * E)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl pow 2 * hmr_e (u:real^2->real^K) y` THEN
    ASM_REWRITE_TAC[REAL_POW_MUL; NORM_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2; hmr_e] THEN
    MP_TAC(ISPEC `partial_derivative 1 (u:real^2->real^K) y` DOT_POS_LE) THEN
    MP_TAC(ISPEC `partial_derivative 2 (u:real^2->real^K) y` DOT_POS_LE) THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HMR_DJ0] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The epsilon-regularity theorem. *)

let CM_EPS_REG = prove
 (`!kk:K->bool. CM_EPS_REG_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_EPS_REG_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `C1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base")))) o
    MATCH_MP HMR_EPS_BASE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMR_DJ_ALL) THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `KK:num->real` (LABEL_TAC "kk")) THEN
  SUBGOAL_THEN `!n. &0 <= (KK:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "kk" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min e1 (inv(&4 * C1))` THEN
  EXISTS_TAC `\k. &2 pow k * (KK:num->real)(k - 1) * &2 * sqrt C1 + &1` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`; `l:num list`; `x:real^2`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  ABBREV_TAC `E = wan_gdir (ball(a,r)) (G:real^K->real^K^K) (u:real^2->real^K)` THEN
  SUBGOAL_THEN `E <= e1 /\ C1 * E <= &1 / &4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `E <= min e1 (inv(&4 * C1))` THEN REWRITE_TAC[REAL_LE_MIN] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * inv(&4 * C1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `C1 * inv(&4 * C1) = &1 / &4` (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      UNDISCH_TAC `&0 < C1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  USE_THEN "base" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real^K`; `x:real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A1 = &2 * sqrt(C1 * E)` THEN
  SUBGOAL_THEN `&0 <= A1 /\ A1 <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `s <= &1 / &2 ==> &2 * s <= &1`) THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the harmonic map equation on the ball *)
  SUBGOAL_THEN `!z. z IN ball(a,r) ==> hmr_vlap (u:real^2->real^K) z = hmr_fq S G u z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_fq] THEN MATCH_MP_TAC HMR_PDE THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `ball(a:real^2,r)`] THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(x:real^2,r / &2) SUBSET ball(a,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL; dist] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^2) IN ball(a,r / &2)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`a - z:real^2`; `a - x:real^2`] NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `(a - z) - (a - x):real^2 = x - z`] THEN
    UNDISCH_TAC `norm(x - z:real^2) <= r / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the weighted jet at the centre *)
  ABBREV_TAC `k = LENGTH(l:num list)` THEN
  USE_THEN "kk" (MP_TAC o SPEC `k - 1`) THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`; `u:real^2->real^K`; `x:real^2`; `r / &2`;
                             `A1:real`] o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  REWRITE_TAC[CENTRE_IN_BALL; VECTOR_SUB_REFL; NORM_0; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  (* the list as a derivative of a first partial *)
  MP_TAC(ISPEC `l:num list` APPEND_BUTLAST_LAST) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `l' = BUTLAST(l:num list)` THEN ABBREV_TAC `i = LAST(l:num list)` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `ALL (\j. 1 <= j /\ j <= 2) (l':num list) /\ 1 <= i /\ i <= 2 /\
                LENGTH l' = k - 1 /\ 1 <= k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= 2) (l:num list)` THEN
    UNDISCH_TAC `LENGTH(l:num list) = k` THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL; LENGTH_APPEND; LENGTH] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX] THEN
  MP_TAC(ISPECL [`k - 1`; `r / &2`; `u:real^2->real^K`; `x:real^2`; `i:num`; `l':num list`]
    HMR_DJ_TERM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r pow k = &2 pow k * (r / &2) pow k` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow k * (KK:num->real)(k - 1) * A1` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  EXPAND_TAC "A1" THEN REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `&0 <= sqrt E` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

