(* ========================================================================= *)
(* pc_pde_rdt_iter: the Ricci-DeTurck existence, part 5.  The frozen         *)
(* coefficient iteration of the Ricci-DeTurck flow: the ball pde_rdt_ball is *)
(* invariant under the step and the step contracts in                        *)
(* sup_t L^2 + int H^1 (PDE_RDT_ITERATION).                                  *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_energy.ml";;
needs "src/pc_lrg_stab.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basic facts for the step.  Constant families, tr_k Hess_h h = 0, the step *)
(* minus the background solves the problem with initial value 0, and facts   *)
(* about pde_mnorm2: congruence on the space, chart form, monotonicity in    *)
(* the level, continuity in time, the bound from pde_cbound.                 *)
(* ------------------------------------------------------------------------- *)

(* The same statement as PDE_MX_TFAM_CONST of pc_pde_mexist (which this unit *)
(* does not load).                                                           *)

let RDT_TFAM_CONST = prove
 (`!top atlas a b (v0:A->real^N^N).
     smooth_manifold_atlas top atlas /\ mfd_tensor2_smooth atlas v0
     ==> pde_tfam_from atlas a b (\t:real. v0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDE_MT_UPTO_TIME_CONST THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C];
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_tensor2_smooth]) THEN
    ASM_SIMP_TAC[GSYM o_DEF; ETA_AX]]);;

let RDT_TRHESS_SELF = prove
 (`!top atlas (k:A->real^N^N) h x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ x IN topspace top
     ==> pde_trhess atlas k h h x = mat 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at atlas (x:A))) (FST(chart_at atlas x)))
                  (metric_local atlas (chart_at atlas x) (h:A->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. lnabla_iter 2 2 (metric_local atlas (chart_at atlas (x:A)) (h:A->real^N^N))
          (lmetric2 (metric_local atlas (chart_at atlas x) h)) (SND(chart_at atlas x) x) u = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`1`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                                `u:num->real^N`] o
      MATCH_MP LRG_LNABLA_ITER_METRIC) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUC_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_trhess; pde_ltrhess; REAL_MUL_RZERO; SUM_0] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; MAT_COMPONENT; COND_ID]);;

let RDT_STEP_SHIFT = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     pde_mlin_sol (top,atlas) a b k h f h v
     ==> pde_mlin_sol (top,atlas) a b k h f (\x. mat 0) (\t x. v t x - h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mlin_sol] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas (h:A->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `h:A->real^N^N`] RDT_TFAM_CONST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `v:real->A->real^N^N`; `\t:real. (h:A->real^N^N)`] PDE_ME_TFAM_SUB) THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MATRIX_SUB_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_trhess atlas ((k:real->A->real^N^N) t) h (\x. (v:real->A->real^N^N) t x - h x) x =
    pde_trhess atlas (k t) h (v t) x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(k:real->A->real^N^N) t`; `h:A->real^N^N`; `(v:real->A->real^N^N) t`;
                   `h:A->real^N^N`; `x:A`] PDE_ME_TRHESS_SUB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(k:real->A->real^N^N) t`; `h:A->real^N^N`; `x:A`] RDT_TRHESS_SELF) THEN
    ASM_SIMP_TAC[MATRIX_SUB_RZERO];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s. (v:real->A->real^N^N) s x$i$j`;
                 `(pde_trhess atlas ((k:real->A->real^N^N) t) h ((v:real->A->real^N^N) t) x +
                   (f:real->A->real^N^N) t x)$i$j`;
                 `\s:real. (h:A->real^N^N) x$i$j`; `&0`; `atreal t`] HAS_REAL_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO; MATRIX_SUB_COMPONENT]);;

(* pde_mnorm2 only depends on the values on the space.                     *)

let RDT_MNORM2_CONG = prove
 (`!top atlas n0 cs (psi:num->A->real) s (v:A->real^N^N) v'.
     smooth_manifold_atlas top atlas /\ (!i. i < n0 ==> cs i IN atlas) /\
     (!x. x IN topspace top ==> v x = v' x)
     ==> pde_mnorm2 atlas n0 cs psi s v = pde_mnorm2 atlas n0 cs psi s v'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mnorm2] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `v:A->real^N^N`; `v':A->real^N^N`]
    PDE_METRIC_LOCAL_CONG) THEN
  ASM_SIMP_TAC[]);;

let RDT_MNORM2_HS = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) n0 cs psi s v.
     pde_mnorm2 atlas n0 cs psi s v =
     sum {i | i < n0}
       (\i. rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) s
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (psi i (chart_inv (cs i) z) %% metric_local atlas (cs i) v z)))`,
  REWRITE_TAC[pde_mnorm2; rdt_hs; rdt_int]);;

let RDT_MNORM2_MONO = prove
 (`!top atlas n0 cs ks psi (v:A->real^N^N) s s'.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tensor_smooth atlas v /\ s <= s'
     ==> pde_mnorm2 atlas n0 cs psi s v <= pde_mnorm2 atlas n0 cs psi s' v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `v:A->real^N^N`; `s':num`] PDM_MNORM2_TERMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[pde_mnorm2] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; PDE_INDEX_LISTS_MONO]);;

let RDT_MNORM2_CONT = prove
 (`!top atlas n0 cs ks psi a b b' (v:real->A->real^N^N) s.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tfam_from atlas a b v /\ b' < b
     ==> (\r. pde_mnorm2 atlas n0 cs psi s (v r)) real_continuous_on real_interval[a,b']`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[PDE_ME_MNORM2_CNORM] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_ME_CNORM_CONT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) i`; `b:real`] THEN
  ASM_SIMP_TAC[]);;

(* The bound of |h|_s^2 from pde_cbound m B h, m >= s.                      *)

let RDT_MNORM2_CBOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s m B.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     s <= m /\ &0 <= B
     ==> ?MH. &0 <= MH /\
              !h. riemannian_metric atlas h /\ pde_cbound atlas n0 cs ks m B h
                  ==> pde_mnorm2 atlas n0 cs psi s h <= MH`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `s:num`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> &0 <= (AP:num->real) i /\
                   &0 <= drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_ONE] THEN MATCH_MP_TAC RDT_INTK_ONE_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `APS = sum {i | i < n0} (AP:num->real)` THEN
  ABBREV_TAC `IS = sum {i | i < n0}
                     (\i. drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2))))` THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> (AP:num->real) i <= APS /\
                   drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2))) <= IS`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["APS"; "IS"] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`AP:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM);
      MP_TAC(ISPECL [`\i. drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))`;
                     `n0:num`; `i:num`] RDT_TERM_LE_SUM)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= APS /\ &0 <= IS` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["APS"; "IS"] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `c1 = &(CARD(pde_index_lists s (:N))) * (&2 pow s * &1 * &(s + 1) * APS) *
                   (&(CARD(pde_index_lists m (:N))) * B)` THEN
  SUBGOAL_THEN `&0 <= c1` ASSUME_TAC THENL [EXPAND_TAC "c1" THEN RDT_NN_TAC; ALL_TAC] THEN
  ABBREV_TAC `FC = &(CARD(pde_index_lists s (:N))) *
                   (&2 * c1 pow 2 * (&0 pow 2 * &(CARD(pde_index_lists s (:N))) * &0 +
                                     &1 pow 2 * IS))` THEN
  SUBGOAL_THEN `&0 <= FC` ASSUME_TAC THENL
   [EXPAND_TAC "FC" THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `&n0 * FC` THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
                                         ALL_TAC] THEN
  X_GEN_TAC `h:A->real^N^N` THEN STRIP_TAC THEN
  REWRITE_TAC[RDT_MNORM2_HS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {i | i < n0} (\i:num. FC)` THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `U = IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                  (h:A->real^N^N))`
  ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`; `h:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                   (h:A->real^N^N))` THEN
    SIMP_TAC[metric_field];
    STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&(CARD(pde_index_lists s (:N))) *
    (&2 * c1 pow 2 *
     (&0 pow 2 * &(CARD(pde_index_lists s (:N))) * rdt_hs U s (\z:real^N. vec 0:real^1) +
      &1 pow 2 * drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "FC" THEN REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_LZERO; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC RDT_HS_FROM_POINTWISE THEN
  MAP_EVERY EXISTS_TAC [`(ks:num->real^N->bool) i`; `(ks:num->real^N->bool) i`;
                        `\y:real^N. &1`] THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; REAL_LE_REFL; REAL_POS; SMOOTH_MAP_ON_CONST] THEN
  MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn s
                (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                        metric_local atlas (cs i) (h:A->real^N^N) z)) y` THEN
  CONJ_TAC THENL [MATCH_MP_TAC PDE_ME_TERM_LE_JETN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(x:real^1) (v:real^(N,N)finite_prod). drop x % v`; `&1`; `s:num`;
                 `U:real^N->bool`;
                 `\z. lift((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z))`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N) z)`;
                 `y:real^N`; `(AP:num->real) i`] RDT_JETN_BILINEAR_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INST_TYPE [`:N`,`:Q`] RDT_BB_E2; REAL_POS] THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                   (h:A->real^N^N))` THEN
    SIMP_TAC[metric_field; o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; GSYM VECTORIZE_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `m:num`; `B:real`;
                 `h:A->real^N^N`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_jetn s (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N) z)) y
    <= &(CARD(pde_index_lists m (:N))) * B`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn m (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N) z)) y` THEN
    ASM_SIMP_TAC[PDE_JETN_MONO] THEN
    UNDISCH_TAC `pde_jetn m ((vectorize:real^N^N->real^(N,N)finite_prod) o
                metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)) y
                <= &(CARD(pde_index_lists m (:N))) * B` THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(AP:num->real) i <= APS /\ &0 <= AP i` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "c1" THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PDE_JETN_POS]);;

(* ------------------------------------------------------------------------- *)
(* Symmetry.  tr_k Hess_h commutes with the transpose (the iterated          *)
(* covariant derivative is natural under the swap of the first two           *)
(* arguments), the Ricci-DeTurck operator of a metric is symmetric, and      *)
(* solutions of the linear problem with symmetric data are symmetric         *)
(* (PDE_MLIN_UNIQUE applied to the transposed solution).                     *)
(* ------------------------------------------------------------------------- *)

let rdt_sw = new_definition
 `rdt_sw (u:num->real^N) = \j. if j = 1 then u 2 else if j = 2 then u 1 else u j`;;

let RDT_LNABLA_SWAP = prove
 (`!k (G:real^N->real^N^N) tf tf'.
     2 <= k /\ (!z u. tf' z u = tf z (rdt_sw u))
     ==> !y u. lnabla k G tf' y u = lnabla k G tf y (rdt_sw u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN X_GEN_TAC `u:num->real^N` THEN
  SUBGOAL_THEN `rdt_sw (u:num->real^N) (k + 1) = u (k + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[rdt_sw] THEN
    SUBGOAL_THEN `~(k + 1 = 1) /\ ~(k + 1 = 2)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lnabla] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\i. (tf:real^N->(num->real^N)->real) y
                       (\j. if j = i then christoffel G y (u(k + 1)) (rdt_sw u i)
                            else rdt_sw (u:num->real^N) j)`;
                 `swap(1,2)`; `1..k`] SUM_PERMUTE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM; swap] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; rdt_sw] THEN
  X_GEN_TAC `j:num` THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_ARITH_TAC);;

let RDT_LNABLA_ITER_SWAP = prove
 (`!k (G:real^N->real^N^N) tf tf'.
     2 <= k /\ (!z u. tf' z u = tf z (rdt_sw u))
     ==> !l y u. lnabla_iter k l G tf' y u = lnabla_iter k l G tf y (rdt_sw u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[lnabla_iter] THEN
  MATCH_MP_TAC RDT_LNABLA_SWAP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RDT_LTRHESS_TRANSP = prove
 (`!(K:real^N->real^N^N) H V y.
     pde_ltrhess K H (\z. transp(V z)) y = transp(pde_ltrhess K H V y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!z u. lmetric2 (\z. transp((V:real^N->real^N^N) z)) z u =
                      lmetric2 V z (rdt_sw u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[lmetric2; rdt_sw; ARITH_EQ; DOT_MATRIX_TRANSP_RMUL] THEN MESON_TAC[DOT_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `H:real^N->real^N^N`; `lmetric2 (V:real^N->real^N^N)`;
                 `lmetric2 (\z. transp((V:real^N->real^N^N) z))`] RDT_LNABLA_ITER_SWAP) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  SIMP_TAC[CART_EQ; pde_ltrhess; LAMBDA_BETA; TRANSP_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; rdt_sw] THEN
  X_GEN_TAC `m:num` THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_ARITH_TAC);;

let RDT_METRIC_LOCAL_TRANSP = prove
 (`!atlas (c:(A->bool)#(A->real^N)) (v:A->real^N^N).
     metric_local atlas c (\x. transp(v x)) = (\y. transp(metric_local atlas c v y))`,
  REWRITE_TAC[metric_local; FUN_EQ_THM; MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC]);;

let RDT_TRHESS_TRANSP = prove
 (`!atlas (k:A->real^N^N) h v x.
     pde_trhess atlas k h (\x. transp(v x)) x = transp(pde_trhess atlas k h v x)`,
  REWRITE_TAC[pde_trhess; RDT_METRIC_LOCAL_TRANSP; RDT_LTRHESS_TRANSP; ETA_AX]);;

let RDT_TRHESS_CONG = prove
 (`!top atlas (k:A->real^N^N) h (v:A->real^N^N) w x.
     smooth_manifold_atlas top atlas /\ x IN topspace top /\
     (!y. y IN topspace top ==> v y = w y)
     ==> pde_trhess atlas k h v x = pde_trhess atlas k h w x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_trhess] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_ML_LTRHESS_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C];
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                   `v:A->real^N^N`; `w:A->real^N^N`] PDE_METRIC_LOCAL_CONG) THEN
    ASM_SIMP_TAC[]]);;

let RDT_MDERIV_TRANSP = prove
 (`!U (G:real^N->real^N^N) y w.
     metric_field U G /\ y IN U ==> transp(mderiv G y w) = mderiv G y w`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CART_EQ; TRANSP_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `basis i:real^N`; `basis j:real^N`] LRG_MDERIV_SYM) THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let RDT_LRDT_SYM = prove
 (`!U (H:real^N->real^N^N) G y.
     metric_field U G /\ y IN U ==> transp(pde_lrdt H G y) = pde_lrdt H G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `transp(pde_lricci_matrix (G:real^N->real^N^N) y) = pde_lricci_matrix G y`
  ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; TRANSP_COMPONENT; pde_lricci_matrix; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. transp(mderiv (G:real^N->real^N^N) y w) = mderiv G y w` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RDT_MDERIV_TRANSP THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_lrdt; llie; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; MATRIX_TRANSP_MUL;
                  TRANSP_TRANSP] THEN
  MATRIX_ARITH_TAC);;

let RDT_METRIC_SYM = prove
 (`!top atlas (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> transp(g x) = g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^N^N))`
  MP_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  REWRITE_TAC[metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x` o
             CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let RDT_RDT_RHS_SYM = prove
 (`!top atlas (h:A->real^N^N) g x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> transp(pde_rdt_rhs atlas h g x) = pde_rdt_rhs atlas h g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_rdt_rhs] THEN MATCH_MP_TAC RDT_LRDT_SYM THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  ASM_MESON_TAC[riemannian_metric]);;

let RDT_FORCING_SYM = prove
 (`!top atlas (h:A->real^N^N) g x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> transp(pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x) =
         pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TRANSP_MATRIX_SUB] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `h:A->real^N^N`;
                 `g:A->real^N^N`; `x:A`] RDT_RDT_RHS_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM RDT_TRHESS_TRANSP] THEN MATCH_MP_TAC RDT_TRHESS_CONG THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_METRIC_SYM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

let RDT_TFAM_TRANSP = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a b (v:real->A->real^N^N).
     (!c. c IN atlas ==> open(IMAGE (SND c) (FST c))) /\ pde_tfam_from atlas a b v
     ==> pde_tfam_from atlas a b (\t x. transp(v t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tfam_from] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `Fv:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `(\w:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
                (transp((matrify:real^(N,N)finite_prod->real^N^N) w))) o
              (Fv:real^(1,N)finite_sum->real^(N,N)finite_prod)` THEN
  ASM_SIMP_TAC[o_THM; RDT_METRIC_LOCAL_TRANSP; MATRIFY_VECTORIZE; ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_SIMP_TAC[OPEN_INTERVAL];
    REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL;
                VECTORIZE_ADD; VECTORIZE_CMUL]]);;

let RDT_MLIN_SOL_SYM = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v0 v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> transp(f t x) = f t x) /\
     (!x. x IN topspace top ==> transp(v0 x) = v0 x) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v
     ==> !t x. a <= t /\ t < b /\ x IN topspace top ==> transp(v t x) = v t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_mlin_sol (top,atlas) a b k h f v0 (\t x. transp((v:real->A->real^N^N) t x))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pde_mlin_sol (top,atlas) a b k h f v0 (v:real->A->real^N^N)` THEN
    REWRITE_TAC[pde_mlin_sol] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_TFAM_TRANSP THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[PDM_CHART_OPEN_C];
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((f:real->A->real^N^N) t x)$i$j = (f t x)$j$i` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(f:real->A->real^N^N) t x`; `i:num`; `j:num`] TRANSP_COMPONENT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[TRANSP_COMPONENT; RDT_TRHESS_TRANSP; MATRIX_ADD_COMPONENT] THEN
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `j:num`; `i:num`] o check (fun th ->
      can (find_term (fun tm -> try fst(dest_const tm) = "has_real_derivative"
                                with Failure _ -> false)) (concl th) && is_forall(concl th))) THEN
    ASM_SIMP_TAC[MATRIX_ADD_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                 `v0:A->real^N^N`; `v:real->A->real^N^N`;
                 `\t x. transp((v:real->A->real^N^N) t x)`] PDE_MLIN_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* A smooth symmetric tensor field whose chart representatives               *)
(* are positive definite on the pieces of a cover is a Riemannian metric.    *)
(* ------------------------------------------------------------------------- *)

let RDT_CHART_JAC_INV = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' x.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
     x IN FST c /\ x IN FST c'
     ==> matrix(chart_jac c' c x) ** matrix(chart_jac c c' x) = mat 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_JAC_CHAIN_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
    CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_ID]);;

let RDT_METRIC_LOCAL_DOT = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) z w.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ z IN IMAGE (SND c) (FST c)
     ==> w dot (metric_local atlas c g z ** w) =
         (matrix(chart_jac c (chart_at atlas (chart_inv c z)) (chart_inv c z)) ** w) dot
         (g(chart_inv c z) **
          (matrix(chart_jac c (chart_at atlas (chart_inv c z)) (chart_inv c z)) ** w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_local; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL]);;

let RDT_PREF_POS = prove
 (`!top atlas n0 cs ks (g:A->real^N^N) x u.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     (!i y w. i < n0 /\ y IN ks i /\ ~(w = vec 0)
              ==> &0 < w dot (metric_local atlas (cs i) g y ** w)) /\
     x IN topspace top /\ ~(u = vec 0)
     ==> &0 < u dot (g x ** u)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
  REWRITE_TAC[pde_cover] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?i z. i < n0 /\ z IN (ks:num->real^N->bool) i /\
                      chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN topspace top` THEN ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `z:real^N`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\
                (z:real^N) IN IMAGE (SND(cs i)) (FST(cs i))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) i)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_INV_C]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = matrix(chart_jac ((cs:num->(A->bool)#(A->real^N)) i)
                                   (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x)` THEN
  ABBREV_TAC `J' = matrix(chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                                    ((cs:num->(A->bool)#(A->real^N)) i) x)` THEN
  SUBGOAL_THEN `(J:real^N^N) ** (J' ** u) = u` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN MAP_EVERY EXPAND_TAC ["J"; "J'"] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `(cs:num->(A->bool)#(A->real^N)) i`; `x:A`]
      RDT_CHART_JAC_INV) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `z:real^N`; `(J':real^N^N) ** u`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `(<):real->real->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(J:real^N^N) ** (J' ** u) = u` THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `g:A->real^N^N`; `z:real^N`;
                 `(J':real^N^N) ** u`] RDT_METRIC_LOCAL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

let RDT_RIEM_FROM_LOCAL = prove
 (`!top atlas n0 cs ks (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     mfd_tensor2_smooth atlas g /\
     (!x. x IN topspace top ==> transp(g x) = g x) /\
     (!i y w. i < n0 /\ y IN ks i /\ ~(w = vec 0)
              ==> &0 < w dot (metric_local atlas (cs i) g y ** w))
     ==> riemannian_metric atlas g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric; metric_field] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C];
    ASM_MESON_TAC[mfd_tensor2_smooth];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN FST c /\
                chart_inv c z IN topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PDM_CHART_INV_C; PDM_CHART_OPEN_C; SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM(REWRITE_RULE[FUN_EQ_THM] RDT_METRIC_LOCAL_TRANSP)] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `\x. transp((g:A->real^N^N) x)`; `g:A->real^N^N`]
      PDE_METRIC_LOCAL_CONG) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `g:A->real^N^N`; `z:real^N`; `w:real^N`]
    RDT_METRIC_LOCAL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RDT_PREF_POS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                        `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_inv (c:(A->bool)#(A->real^N)) z`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (chart_inv (c:(A->bool)#(A->real^N)) z)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) z`] RDT_CHART_JAC_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(w:real^N = vec 0)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
   `\v:real^N. matrix(chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                 (chart_inv (c:(A->bool)#(A->real^N)) z)) c (chart_inv c z)) ** v` o
   check (fun th -> is_eq(concl th) && can (find_term ((=) `w:real^N`)) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the invariance of the ball: monotonicity of pde_cbound, the     *)
(* pointwise C^0 bound by |w|_s, a perturbation of the lower bound, and the  *)
(* Gronwall bound of |u(t)|_s^2 for solutions of the frozen problem with     *)
(* coefficient and forcing bounds on (a,b).                                  *)
(* ------------------------------------------------------------------------- *)

(* A theorem test: does the conclusion contain the named constant?          *)

let rdt_has_const nm th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = nm)) (concl th);;

let RDT_METRIC_FIELD_PSD = prove
 (`!U (G:real^N->real^N^N) y w.
     metric_field U G /\ y IN U ==> &0 <= w dot (G y ** w)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `w:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[metric_field]);;

let RDT_CBOUND_MONO = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) n0 cs ks m m' B B' g.
     pde_cbound atlas n0 cs ks m B g /\ m' <= m /\ B <= B' /\
     (!i. i < n0 ==> cs i IN atlas /\ ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))) /\
     riemannian_metric atlas g
     ==> pde_cbound atlas n0 cs ks m' B' g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_cbound] THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall(concl th) && rdt_has_const "iterated_partial" th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PDE_INDEX_LISTS_MONO; SUBSET];
    MAP_EVERY X_GEN_TAC [`y:real^N`; `w:real^N`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B * (w dot (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                            (g:A->real^N^N) y ** w))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RDT_METRIC_FIELD_PSD THEN
    EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ASM SET_TAC[]]]);;

let RDT_SOB0 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     dimindex(:N) <= s
     ==> ?C0. &0 <= C0 /\
              !(w:A->real^N^N) i y.
                pde_tensor_smooth atlas w /\ i < n0 /\ y IN ks i
                ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas (cs i) w y)) pow 2
                    <= C0 * pde_mnorm2 atlas n0 cs psi s w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `0`] PDE_MNORM_SOBOLEV) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "sob")) THEN
  EXISTS_TAC `max C (&0)` THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  USE_THEN "sob" (MP_TAC o SPECL [`w:A->real^N^N`; `i:num`; `[]:num list`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PDE_INDEX_LISTS_NIL]; REWRITE_TAC[iterated_partial; o_THM]] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  SUBGOAL_THEN `&0 <= pde_mnorm2 atlas n0 cs psi (dimindex(:N)) (w:A->real^N^N) /\
                pde_mnorm2 atlas n0 cs psi (dimindex(:N)) w <= pde_mnorm2 atlas n0 cs psi s w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RDT_MNORM2_MONO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `max C (&0) * pde_mnorm2 atlas n0 cs psi (dimindex(:N)) (w:A->real^N^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let RDT_LOWER_PERTURB = prove
 (`!(V:real^N^N) G B B1 e.
     norm(vectorize(V - G)) <= e /\ norm(vectorize G) <= B /\ &0 < B1 /\
     (!u. norm u pow 2 <= B1 * (u dot (G ** u))) /\ &2 * B1 * e <= &1
     ==> norm(vectorize V) <= B + e /\
         (!u. norm u pow 2 <= (&2 * B1) * (u dot (V ** u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`vectorize(V - G:real^N^N)`; `vectorize(G:real^N^N)`] NORM_TRIANGLE) THEN
    REWRITE_TAC[GSYM VECTORIZE_ADD; MATRIX_SUB_ADD] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `u:real^N` THEN
  SUBGOAL_THEN `u dot ((V:real^N^N) ** u) = u dot (G ** u) + u dot ((V - G) ** u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(u dot ((V - G:real^N^N) ** u)) <= e * norm(u:real^N) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(u:real^N) * norm((V - G:real^N^N) ** u)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `e * (n * n) = n * (e * n)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(V - G:real^N^N)) * norm(u:real^N)` THEN
    REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (is_forall o concl)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= B1 * e * norm(u:real^N) pow 2 /\
                B1 * abs(u dot ((V - G:real^N^N) ** u)) <= B1 * (e * norm u pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      MP_TAC(ISPEC `vectorize(V - G:real^N^N)` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * B1 * e) * norm(u:real^N) pow 2 <= &1 * norm u pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MP_TAC(SPEC `u dot ((V - G:real^N^N) ** u)` REAL_ABS_BOUNDS) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `--(B1 * (e * norm(u:real^N) pow 2)) <= B1 * (u dot ((V - G:real^N^N) ** u))`
  MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> --y <= x`) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> abs B = B`];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The Gronwall bound for solutions of the frozen problem.                  *)

let RDT_STEP_GRONWALL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s lam M Qb.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ &0 < lam /\ &0 <= M /\ &0 <= Qb
     ==> ?C. &0 <= C /\
             !a b k h f u0 u CF Y0.
               riemannian_metric atlas h /\
               (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
               pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b f /\
               pde_mlin_sol (top,atlas) a b k h f u0 u /\
               (!t. a < t /\ t < b
                    ==> (!i y w. i < n0 /\ y IN ks i
                                 ==> lam * norm w pow 2 <=
                                     w dot (pde_mlaa atlas (cs i) k t y ** w)) /\
                        (!i y. i < n0 /\ y IN ks i
                               ==> rdt_cjet (s DIV 2 + 1) (pde_mlaa atlas (cs i) k t)
                                     (pde_mlbt atlas (cs i) k h t)
                                     (pde_mlct atlas (cs i) k h t) y <= M) /\
                        (!i. i < n0
                             ==> drop(integral (ks i)
                                   (\y. lift(rdt_cjet s (pde_mlaa atlas (cs i) k t)
                                                   (pde_mlbt atlas (cs i) k h t)
                                                   (pde_mlct atlas (cs i) k h t) y pow 2)))
                                 <= Qb) /\
                        pde_mnorm2 atlas n0 cs psi (s - 1) (f t) <= CF) /\
               pde_mnorm2 atlas n0 cs psi s (u a) <= Y0 /\ &0 <= CF
               ==> !t. a <= t /\ t < b
                       ==> pde_mnorm2 atlas n0 cs psi s (u t) <=
                           Y0 + (t - a) * (C * (Y0 + CF)) * exp(C * (t - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `lam:real`; `M:real`; `Qb:real`] RDT_MENERGY_S) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "me"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (u:real->A->real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pde_mlin_sol]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pde_mnorm2 atlas n0 cs psi s ((u:real->A->real^N^N) a)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Y0 + CF /\ &0 <= C * (Y0 + CF)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `t = a:real` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `a < t:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?D. !r. a < r /\ r < b
            ==> ((\r. pde_mnorm2 atlas n0 cs psi s ((u:real->A->real^N^N) r))
                 has_real_derivative D r) (atreal r) /\
                D r <= C * (pde_mnorm2 atlas n0 cs psi s (u r) +
                            pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) r))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN USE_THEN "me" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                          `u0:A->real^N^N`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
      is_forall(concl th) && rdt_has_const "rdt_cjet" th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. pde_mnorm2 atlas n0 cs psi s ((u:real->A->real^N^N) r)`;
                 `D:real->real`; `a:real`; `t:real`; `C:real`; `CF:real`] RDT_GRONWALL_CONST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_MNORM2_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`; `b:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < r /\ r < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * (pde_mnorm2 atlas n0 cs psi s ((u:real->A->real^N^N) r) +
                     pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) r))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= x + z`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
      is_forall(concl th) && rdt_has_const "rdt_cjet" th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `x' <= y /\ d <= e ==> x <= x' + d ==> x <= y + e`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= t - a /\ &0 <= exp(C * (t - a))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The ball is invariant under the step (RDT_BALL_INV): K from               *)
(* the background bound, tau from the Gronwall bounds of |v|_s^2 and of      *)
(* |v - g0|_s^2; C^0 closeness by Sobolev gives pde_cbound 0 K and           *)
(* positivity, symmetry from RDT_MLIN_SOL_SYM.                               *)
(* ------------------------------------------------------------------------- *)

let RDT_SMALL_TIME = prove
 (`!C X eps.
     &0 <= C /\ &0 <= X /\ &0 < eps
     ==> ?tau1. &0 < tau1 /\ tau1 <= &1 /\
                !d. &0 <= d /\ d <= tau1 ==> d * (C * X) * exp(C * d) <= eps`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = C * X * exp C` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1) (eps * inv(A + &1))` THEN
  SUBGOAL_THEN `&0 < eps * inv(A + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `d <= &1 /\ d <= eps * inv(A + &1)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d * A` THEN CONJ_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps * inv(A + &1)) * A` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let RDT_POS_FROM_LOWER = prove
 (`!c x d. &0 < c /\ x <= c * d ==> (&0 <= x ==> &0 <= d) /\ (&0 < x ==> &0 < d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`c:real`; `d:real`] (CONJUNCT1 REAL_LE_MUL_EQ));
    MP_TAC(SPECL [`c:real`; `d:real`] (CONJUNCT1 REAL_LT_MUL_EQ))] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC);;

(* pde_cbound 0 K and positivity for a field C^0-close to the background.   *)

let RDT_CBOUND_FROM_CLOSE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) n0 cs ks m B g0 (v:A->real^N^N) K e0.
     pde_cbound atlas n0 cs ks m B g0 /\ riemannian_metric atlas g0 /\
     (!i. i < n0 ==> cs i IN atlas /\ ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))) /\
     &0 <= B /\ &0 <= e0 /\ &2 * (B + &1) * e0 <= &1 /\ e0 <= &1 /\
     &2 * (B + &1) <= K /\ B + &1 <= K /\
     (!i y. i < n0 /\ y IN ks i
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                       (metric_local atlas (cs i) v y - metric_local atlas (cs i) g0 y)) <= e0)
     ==> pde_cbound atlas n0 cs ks 0 K v /\
         (!i y u. i < n0 /\ y IN ks i /\ ~(u = vec 0)
                  ==> &0 < u dot (metric_local atlas (cs i) v y ** u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i y. i < n0 /\ y IN ks i
          ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                     (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (v:A->real^N^N) y))
              <= K /\
              (!u. norm u pow 2 <= (&2 * (B + &1)) *
                                   (u dot (metric_local atlas (cs i) v y ** u)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `m:num`; `B:real`;
                   `g0:A->real^N^N`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (v:A->real^N^N) y`;
                   `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g0:A->real^N^N) y`;
                   `B:real`; `B + &1`; `e0:real`] RDT_LOWER_PERTURB) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real^N` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B * (u dot (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                (g0:A->real^N^N) y ** u))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RDT_METRIC_FIELD_PSD THEN
      EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ASM SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pde_cbound; PDE_INDEX_LISTS_0; IN_SING] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[iterated_partial; o_THM] THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`y:real^N`; `u:real^N`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N` o CONJUNCT2) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`&2 * (B + &1)`; `norm(u:real^N) pow 2`;
                     `u dot (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                (v:A->real^N^N) y ** u)`] RDT_POS_FROM_LOWER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[REAL_LE_POW_2] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * (B + &1)) *
                  (u dot (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                            (v:A->real^N^N) y ** u))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`; `u:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^N` o CONJUNCT2) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&2 * (B + &1)`; `norm(u:real^N) pow 2`;
                 `u dot (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                            (v:A->real^N^N) y ** u)`] RDT_POS_FROM_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]);;

(* ------------------------------------------------------------------------- *)
(* RDT_BALL_INV.  For s >= 2N+4, m >= s+3 and the background                 *)
(* bound B there are K and tau1 > 0 such that for every tau <= tau1 the      *)
(* constant family is in the ball and the step maps the ball into itself.    *)
(* ------------------------------------------------------------------------- *)

let RDT_BALL_INV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s m B.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ s + 3 <= m /\ &0 <= B
     ==> ?K tau1. &0 < K /\ &0 < tau1 /\
           !tau g0 a. &0 < tau /\ tau <= tau1 /\
                      riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks m B g0
             ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (\t. g0) /\
                 (!g v. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
                        pde_rdt_step (top,atlas) a (a + tau) g0 g v
                        ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  SUBGOAL_THEN `!i. i < n0 ==> (cs:num->(A->bool)#(A->real^N)) i IN atlas /\
                               (ks:num->real^N->bool) i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `m:num`; `B:real`] RDT_MNORM2_CBOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `MH:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mh"))) THEN
  ABBREV_TAC `K = &2 * (B + &1) + MH + &1` THEN
  SUBGOAL_THEN `&0 < K /\ &2 * (B + &1) <= K /\ B + &1 <= K /\ MH + &1 <= K /\ &0 <= K /\
                B <= K`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "K" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `m:num`; `B:real`; `K:real`] RDT_BALL_COEF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `Qb:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bc"))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `m:num`; `B:real`; `K:real`] RDT_BALL_FORCING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bf"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `lam:real`; `M:real`; `Qb:real`] RDT_STEP_GRONWALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gr"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`] RDT_SOB0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s0"))) THEN
  SUBGOAL_THEN `&0 < &2 * (B + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `e0 = inv(&2 * (B + &1))` THEN
  SUBGOAL_THEN `&0 < e0 /\ &0 <= e0 /\ &2 * (B + &1) * e0 <= &1 /\ e0 <= &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN
    SIMP_TAC[REAL_LT_INV_EQ; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_MUL_ASSOC;
             REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL; ASSUME `&0 < &2 * (B + &1)`] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `MH + CF`; `&1`] RDT_SMALL_TIME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ta")))) THEN
  MP_TAC(SPECL [`C:real`; `&0 + CF`; `e0 pow 2 * inv(C0 + &1)`] RDT_SMALL_TIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tb")))) THEN
  EXISTS_TAC `K:real` THEN EXISTS_TAC `min ta tb` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `g0:A->real^N^N`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas (g0:A->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_mnorm2 atlas n0 cs psi s (g0:A->real^N^N) <= MH` ASSUME_TAC THENL
   [USE_THEN "mh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pde_rdt_ball] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_TFAM_CONST THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RDT_CBOUND_MONO THEN MAP_EVERY EXISTS_TAC [`m:num`; `B:real`] THEN
        ASM_REWRITE_TAC[LE_0];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real->A->real^N^N`; `v:real->A->real^N^N`] THEN
  REWRITE_TAC[pde_rdt_ball; pde_rdt_step] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_tfam_from atlas a (a + tau) (v:real->A->real^N^N) /\
    (!x. x IN topspace top ==> v a x = (g0:A->real^N^N) x)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pde_mlin_sol]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `pde_tfam_from atlas a (a + tau)
      (\t x. pde_rdt_rhs atlas (g0:A->real^N^N) ((g:real->A->real^N^N) t) x -
             pde_trhess atlas (g t) g0 (g t) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RDT_REMAINDER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. a < r /\ r < a + tau
        ==> (!i y w. i < n0 /\ y IN ks i
                     ==> lam * norm w pow 2 <=
                         w dot (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                  (g:real->A->real^N^N) r y ** w)) /\
            (!i y. i < n0 /\ y IN ks i
                   ==> rdt_cjet (s DIV 2 + 1) (pde_mlaa atlas (cs i) g r)
                         (pde_mlbt atlas (cs i) g (g0:A->real^N^N) r)
                         (pde_mlct atlas (cs i) g g0 r) y <= M) /\
            (!i. i < n0
                 ==> drop(integral (ks i)
                       (\y. lift(rdt_cjet s (pde_mlaa atlas (cs i) g r)
                                       (pde_mlbt atlas (cs i) g g0 r)
                                       (pde_mlct atlas (cs i) g g0 r) y pow 2))) <= Qb) /\
            pde_mnorm2 atlas n0 cs psi (s - 1)
              ((\t x. pde_rdt_rhs atlas g0 (g t) x - pde_trhess atlas (g t) g0 (g t) x) r)
            <= CF`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_cbound" th && rdt_has_const "pde_mnorm2" th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "bc" (MP_TAC o SPECL [`g0:A->real^N^N`; `(g:real->A->real^N^N) r`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "bf" (MP_TAC o SPECL [`g0:A->real^N^N`; `(g:real->A->real^N^N) r`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[PDE_ML_COEFF_FUN];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) a) <= MH` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_mnorm2 atlas n0 cs psi s (g0:A->real^N^N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_MNORM2_CONG THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < a + tau
        ==> pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t) <=
            MH + (t - a) * (C * (MH + CF)) * exp(C * (t - a))`
  ASSUME_TAC THENL
   [USE_THEN "gr" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`g:real->A->real^N^N`; `g0:A->real^N^N`;
      `\t x. pde_rdt_rhs atlas (g0:A->real^N^N) ((g:real->A->real^N^N) t) x -
             pde_trhess atlas (g t) g0 (g t) x`;
      `g0:A->real^N^N`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mlin_sol (top,atlas) a (a + tau) g g0
      (\t x. pde_rdt_rhs atlas (g0:A->real^N^N) ((g:real->A->real^N^N) t) x -
             pde_trhess atlas (g t) g0 (g t) x)
      (\x. mat 0) (\t x. (v:real->A->real^N^N) t x - g0 x)`
  ASSUME_TAC THENL [MATCH_MP_TAC RDT_STEP_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mnorm2 atlas n0 cs psi s (\x. (v:real->A->real^N^N) a x - (g0:A->real^N^N) x) <= &0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `pde_mnorm2 atlas n0 cs psi s (\x. (v:real->A->real^N^N) a x - (g0:A->real^N^N) x) =
      pde_mnorm2 atlas n0 cs psi s (\x:A. mat 0:real^N^N)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RDT_MNORM2_CONG THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[MATRIX_SUB_REFL];
      REWRITE_TAC[PDE_ME_MNORM2_ZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < a + tau
        ==> pde_mnorm2 atlas n0 cs psi s
              (\x. (v:real->A->real^N^N) t x - (g0:A->real^N^N) x) <=
            &0 + (t - a) * (C * (&0 + CF)) * exp(C * (t - a))`
  ASSUME_TAC THENL
   [USE_THEN "gr" (MP_TAC o SPECL
     [`a:real`; `a + tau`; `g:real->A->real^N^N`; `g0:A->real^N^N`;
      `\t x. pde_rdt_rhs atlas (g0:A->real^N^N) ((g:real->A->real^N^N) t) x -
             pde_trhess atlas (g t) g0 (g t) x`;
      `\x:A. mat 0:real^N^N`; `\t x. (v:real->A->real^N^N) t x - (g0:A->real^N^N) x`;
      `CF:real`; `&0`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t - a /\ t - a <= ta /\ t - a <= tb` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t - a) * (C * (MH + CF)) * exp(C * (t - a)) <= &1 /\
                (t - a) * (C * (&0 + CF)) * exp(C * (t - a)) <= e0 pow 2 * inv(C0 + &1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "ta" MATCH_MP_TAC; USE_THEN "tb" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `a + tau`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i y. i < n0 /\ y IN ks i
          ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                     (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                   ((v:real->A->real^N^N) t) y -
                      metric_local atlas (cs i) (g0:A->real^N^N) y)) <= e0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN
    USE_THEN "s0" (MP_TAC o SPECL
     [`\x. (v:real->A->real^N^N) t x - (g0:A->real^N^N) x`; `i:num`; `y:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[METRIC_LOCAL_SUB; ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * (e0 pow 2 * inv(C0 + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&0 + (t - a) * (C * (&0 + CF)) * exp(C * (t - a))` THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `C0 * (e0 pow 2 * inv(C0 + &1)) = e0 pow 2 * (C0 * inv(C0 + &1))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ;
                   REAL_ARITH `&0 <= C0 ==> &0 < C0 + &1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `m:num`; `B:real`;
                 `g0:A->real^N^N`; `(v:real->A->real^N^N) t`; `K:real`; `e0:real`]
    RDT_CBOUND_FROM_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_RIEM_FROM_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `n0:num`; `cs:num->(A->bool)#(A->real^N)`;
                          `ks:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `a + tau`; `g:real->A->real^N^N`; `g0:A->real^N^N`;
                   `\t x. pde_rdt_rhs atlas (g0:A->real^N^N) ((g:real->A->real^N^N) t) x -
                          pde_trhess atlas (g t) g0 (g t) x`;
                   `g0:A->real^N^N`; `v:real->A->real^N^N`] RDT_MLIN_SOL_SYM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC RDT_FORCING_SYM THEN
        EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_METRIC_SYM THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `MH + (t - a) * (C * (MH + CF)) * exp(C * (t - a))` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

