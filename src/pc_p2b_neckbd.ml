(* ========================================================================= *)
(* Unit pc_p2b_neckbd: general bounds at the centres of eps-necks and        *)
(* evolving eps-necks, for the hypotheses of local compactness theorems      *)
(* (pc_p2b_lcreqg: curvature bounds on backward neighbourhoods and volume    *)
(* lower bounds of small balls).  A separate low unit, shared with the view  *)
(* routes of MT Thms 11.1, 11.8.  Statements read the slices of a view       *)
(* through explicit hypotheses, not through p2c_regular_view.                *)
(*                                                                           *)
(* Contents:                                                                 *)
(* - balls about points of a neck at bounded level stay in the neck at       *)
(*   bounded levels, with compact closure (P2BN_BALL_LEVELS);                *)
(* - |Rm| <= c R(x) at the centre of an evolving neck along its window       *)
(*   (P2BN_EVNECK_RM), via the shrinking-cylinder bound (copied from         *)
(*   pc_p3_c172d / pc_p3_c172c / pc_rfa_shiscale);                           *)
(* - persistence of an open set covered by persisting open sets;             *)
(* - neck centres are noncollapsed (P2BN_NECK_NONCOLL, P2BN_NECK_BALL_IN);   *)
(* - general forms of the backward (R1) and volume (R2) hypotheses;          *)
(* - R along evolving necks (copies from pc_p3_c172d).                       *)
(* ========================================================================= *)

needs "src/pc_p3_defs.ml";;   (* view vocabulary rfs_vtop etc. only *)
needs "src/pc_apx_chain.ml";;
needs "src/pc_lrg_base.ml";;
needs "src/pc_rfa_doubling.ml";;
needs "src/pc_rfa_sec.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_lim_close.ml";;   (* LIM_PB_BALL_IMAGE, for P2BN_NECK_NONCOLL *)
needs "src/pc_lim_vol.ml";;     (* LIM_OPEN_VOLUME, LIM_VOL_IMAGE_LOWER, for P2BN_NECK_NONCOLL *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Balls in necks.  In an eps-neck e centred at x with scale                 *)
(* h = R(x)^(-1/2), the ball of radius r about a point e y with             *)
(* |s(y)| <= lam stays in the image of the closed slab |s| <= lam + r/(h')  *)
(* (h' = 99/100 h) when that level is below 1/eps; the image of a closed    *)
(* slab is compact, so the closure of the ball is compact.                  *)
(* ========================================================================= *)

let P2BN_SVAL_NORM = prove
 (`!y:real^3 a.
     ~(y = vec 0)
     ==> (abs(apx_sval y) <= a <=>
          exp(--a / sqrt(&2)) <= norm y /\ norm y <= exp(a / sqrt(&2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LT; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  MP_TAC(SPECL [`--a / sqrt(&2)`; `log(norm(y:real^3))`] REAL_EXP_MONO_LE) THEN
  MP_TAC(SPECL [`log(norm(y:real^3))`; `a / sqrt(&2)`] REAL_EXP_MONO_LE) THEN
  ASM_SIMP_TAC[EXP_LOG] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let P2BN_CLOSED_SLAB = prove
 (`!Lam. &0 <= Lam
         ==> compact {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= Lam} /\
             (!eps. Lam < inv eps
                    ==> {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= Lam} SUBSET
                        rfs_neck_dom eps)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `{z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= Lam} =
                {z | exp(--Lam / sqrt(&2)) <= norm z /\ norm z <= exp(Lam / sqrt(&2))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_SIMP_TAC[P2BN_SVAL_NORM] THEN
    REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `--Lam / sqrt(&2)` REAL_EXP_POS_LT) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{z:real^3 | exp(--Lam / sqrt(&2)) <= norm z /\ norm z <= exp(Lam / sqrt(&2))} =
                  cball(vec 0,exp(Lam / sqrt(&2))) DIFF ball(vec 0,exp(--Lam / sqrt(&2)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
    X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Lam / sqrt(&2) < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; rfs_neck_dom; annulus] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) < exp(--Lam / sqrt(&2)) /\
                  exp(Lam / sqrt(&2)) < exp(inv(sqrt(&2) * eps))` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LT; real_div; REAL_MUL_LNEG; REAL_LT_NEG2] THEN
      ASM_REWRITE_TAC[GSYM real_div];
      ASM_REAL_ARITH_TAC]]);;

(* The ball about a neck point at bounded level. *)

let P2BN_BALL_LEVELS = prove
 (`!top atlas (g:A->real^3^3) eps x e y lam r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < eps /\ apx_eng_n2 top atlas g eps (&1 / &100) /\
     rfs_neck (top,atlas) g eps x e /\
     y IN rfs_neck_dom eps /\ abs(apx_sval y) <= lam /\ &0 < r /\
     lam + r / (&99 / &100 * inv(sqrt(mfd_scalar atlas g x))) < inv eps
     ==> mfd_ball (top,atlas) g (e y) r SUBSET
           IMAGE e {z | ~(z = vec 0) /\
                        abs(apx_sval z) <= lam + r / (&99 / &100 * inv(sqrt(mfd_scalar atlas g x)))} /\
         compact_in top
           (IMAGE e {z | ~(z = vec 0) /\
                        abs(apx_sval z) <= lam + r / (&99 / &100 * inv(sqrt(mfd_scalar atlas g x)))}) /\
         top closure_of mfd_ball (top,atlas) g (e y) r SUBSET
           IMAGE e {z | ~(z = vec 0) /\
                        abs(apx_sval z) <= lam + r / (&99 / &100 * inv(sqrt(mfd_scalar atlas g x)))} /\
         compact_in top (top closure_of mfd_ball (top,atlas) g (e y) r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h = &99 / &100 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = lam + r / h` THEN
  SUBGOAL_THEN `&0 <= lam /\ &0 <= Lam /\ lam < Lam` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r / h` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `apx_sval y` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `Lam:real` P2BN_CLOSED_SLAB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `eps:real`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN
   `compact_in top (IMAGE (e:real^3->A) {z | ~(z = vec 0) /\ abs(apx_sval z) <= Lam})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) (g:A->real^3^3) ((e:real^3->A) y) r SUBSET
    IMAGE e {z | ~(z = vec 0) /\ abs(apx_sval z) <= Lam}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(q:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
     [MATCH_MP_TAC APX_NECK_EXIT_BALL THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `x:A`; `y:real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `r <= h * (inv eps - abs(apx_sval y))` MP_TAC THENL
       [SUBGOAL_THEN `r = h * (r / h)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) y) q < r` THEN
        EXPAND_TAC "h" THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN rfs_neck_dom eps` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `apx_eng_n2 top atlas (g:A->real^3^3) eps (&1 / &100)` THEN
    REWRITE_TAC[apx_eng_n2] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `y:real^3`; `z:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) y) q < r` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `(e:real^3->A) z`)) THEN
    SUBGOAL_THEN `abs(apx_sval z) < inv eps` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN rfs_neck_dom eps` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r / h < min (abs(apx_sval y - apx_sval z))
                              (&2 * inv eps - abs(apx_sval y) - abs(apx_sval z))`
    MP_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN EXPAND_TAC "h" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `IMAGE (e:real^3->A) {z | ~(z = vec 0) /\ abs(apx_sval z) <= Lam}` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]]);;

(* ========================================================================= *)
(* The curvature of the shrinking cylinders and |Rm| along evolving necks.   *)
(* The first five lemmas are renamed copies, with the same proofs, of        *)
(* RFA_LTNORM2_METRIC_SCALE and RFA_LRM_DERIV_NORM2_SCALE (pc_rfa_shiscale), *)
(* RFA_RMD_POS (pc_rfa_slcalc), P3H_PW_CYL (pc_p3_c172c) and                 *)
(* P3H_CYL_RM_BOUND (pc_p3_c172d), so that this unit stays off the Shi and   *)
(* Seeley closure and the Part 3 units.                                      *)
(* ========================================================================= *)

let P2BN_LTNORM2_METRIC_SCALE = prove
 (`!k (G:real^N->real^N^N) c tf y.
     ltnorm2 k (\z. c %% G z) tf y = inv c pow k * ltnorm2 k G tf y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltnorm2; MATRIX_INV_CMUL; MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[PRODUCT_MUL_NUMSEG; PRODUCT_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC);;

let P2BN_LRM_DERIV_NORM2_SCALE = prove
 (`!U (G:real^N->real^N^N) c l y.
     metric_field U G /\ y IN U /\ &0 < c
     ==> lrm_deriv_norm2 l (\z. c %% G z) y = inv c pow (l + 2) * lrm_deriv_norm2 l G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRM4_TENSOR_FIELD) THEN
  SUBGOAL_THEN
   `!z u. z IN U ==> lrm4 (\z. c %% (G:real^N->real^N^N) z) z u = c * lrm4 G z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRIEMANN_SCALE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z u. z IN U
          ==> lnabla_iter 4 l (\z. c %% (G:real^N->real^N^N) z) (lrm4 (\z. c %% G z)) z u =
              c * lnabla_iter 4 l G (lrm4 G) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `lnabla_iter 4 l (G:real^N->real^N^N) (lrm4 (\z. c %% G z)) z u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `\z. c %% (G:real^N->real^N^N) z`; `G:real^N->real^N^N`;
                     `lrm4 (\z. c %% (G:real^N->real^N^N) z)`; `U:real^N->bool`]
             LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SCALE THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `lnabla_iter 4 l (G:real^N->real^N^N) (\x u. c * lrm4 G x u) z u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `G:real^N->real^N^N`; `G:real^N->real^N^N`;
                     `lrm4 (\z. c %% (G:real^N->real^N^N) z)`;
                     `\x:real^N u. c * lrm4 (G:real^N->real^N^N) x u`; `U:real^N->bool`]
             LRG_LNABLA_ITER_LOCAL) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                   `lrm4 (G:real^N->real^N^N)`; `c:real`; `&0`] LRG_LNABLA_ITER_LINCOMB) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    DISCH_THEN(MP_TAC o SPECL [`l:num`; `z:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lrm_deriv_norm2; P2BN_LTNORM2_METRIC_SCALE] THEN
  SUBGOAL_THEN
   `ltnorm2 (4 + l) (G:real^N->real^N^N)
      (lnabla_iter 4 l (\z. c %% G z) (lrm4 (\z. c %% G z))) y =
    ltnorm2 (4 + l) G (\x u. c * lnabla_iter 4 l G (lrm4 G) x u) y`
  SUBST1_TAC THENL [REWRITE_TAC[ltnorm2] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LRG_LTNORM2_CMUL; REAL_MUL_ASSOC; ETA_AX] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_INV] THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

let P2BN_RMD_POS = prove
 (`!j U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> &0 <= lrm_deriv_norm2 j G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
  MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD]);;

let P2BN_PW_CYL = prove
 (`!e t (y:real^3).
     ~(y = vec 0) /\ ~(&2 * e + &1 = &0)
     ==> mpullback (\z. ((norm z pow 2) rpow e) % z) (cylinder_flow t) y =
         ((&2 * e + &1) pow 2) %%
         cylinder_flow (&1 - (&1 - t) / (&2 * e + &1) pow 2) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_FRECHET) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  MP_TAC(ISPECL [`frechet_derivative (\z:real^3. (norm z pow 2) rpow e % z) (at y)`;
                 `cylinder_flow t (((norm(y:real^3) pow 2) rpow e) % y)`;
                 `u:real^3`; `v:real^3`] RFB_CONGRUENCE_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL] THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_NORM2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `N = norm(y:real^3) pow 2` THEN
  SUBGOAL_THEN `N rpow (&2 * e + &1) = (N rpow e) pow 2 * N /\
                N rpow (e - &1) = N rpow e / N` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[RPOW_ADD; RPOW_SUB] THEN REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN
    SUBGOAL_THEN `&2 * e = e + e` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < N rpow e` ASSUME_TAC THENL [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = N rpow e` THEN
  SUBGOAL_THEN `(y:real^3) dot y = N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[DOT_RADD; DOT_LADD; DOT_RMUL; DOT_LMUL; MATRIX_VECTOR_LMUL] THEN
  ASM_REWRITE_TAC[DOT_SYM] THEN
  UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&0 < N` THEN
  UNDISCH_TAC `~(&2 * e + &1 = &0)` THEN CONV_TAC REAL_FIELD);;

let P2BN_CYL_RM_BOUND = prove
 (`?K0. !s (y:real^3). s <= &0 /\ ~(y = vec 0)
                       ==> lrm_deriv_norm2 0 (cylinder_flow s) y <= K0 pow 2`,
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN EXISTS_TAC `K0:real` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - s /\ &1 <= &1 - s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `p = inv(sqrt(&1 - s))` THEN
  SUBGOAL_THEN `&0 < p /\ p pow 2 = inv(&1 - s)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `ee = (p - &1) / &2` THEN
  SUBGOAL_THEN `&2 * ee + &1 = p` ASSUME_TAC THENL [EXPAND_TAC "ee" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `pw = \z:real^3. ((norm z pow 2) rpow ee) % z` THEN
  SUBGOAL_THEN
   `!z:real^3. z IN (:real^3) DELETE vec 0
               ==> cylinder_flow s z = (&1 - s) %% mpullback pw (cylinder_flow (&0)) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE; IN_UNIV] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXPAND_TAC "pw" THEN
    MP_TAC(SPECL [`ee:real`; `&0`; `z:real^3`] P2BN_PW_CYL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_CMUL_ASSOC; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&1 - &1 / inv(&1 - s) = s /\ (&1 - s) * inv(&1 - s) = &1`
    (fun th -> REWRITE_TAC[th; MATRIX_CMUL_LID]) THEN
    UNDISCH_TAC `&0 < &1 - s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                  (pw:real^3->real^3) (\y. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "pw" THEN MATCH_MP_TAC RFB_PW_DIFFEO THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field ((:real^3) DELETE vec 0) (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field ((:real^3) DELETE vec 0) (mpullback pw (cylinder_flow (&0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`(:real^3) DELETE vec 0`;
                          `\y:real^3. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `cylinder_flow s`;
                 `\z. (&1 - s) %% mpullback (pw:real^3->real^3) (cylinder_flow (&0)) z`;
                 `(:real^3) DELETE vec 0`; `y:real^3`] LRM_DERIV_NORM2_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `mpullback (pw:real^3->real^3) (cylinder_flow (&0))`;
                 `&1 - s`; `0`; `y:real^3`] P2BN_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`0`; `(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`;
                 `pw:real^3->real^3`;
                 `\y:real^3. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y`;
                 `cylinder_flow (&0)`; `y:real^3`] LRM_DERIV_NORM2_PULLBACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~((pw:real^3->real^3) y = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                  (pw:real^3->real^3) (\y. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y)` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (pw:real^3->real^3) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `(pw:real^3->real^3) y`) THEN
    MATCH_MP_TAC(TAUT `p ==> (p <=> q) ==> q`) THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * K0 pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BN_RMD_POS THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_UNIV];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;


(* The general-view reading of rfs_evolving_neck (as P2B9_EVOLVING_NECK_ALT *)
(* of pc_p2b_979, re-proved here to keep this unit's closure small).       *)

let P2BN_EVOLVING_NECK_ALT = prove
 (`!V eps (x:A) t len e.
     rfs_evolving_neck V eps x t len e <=>
     rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps x e /\ &0 < len /\
     (!s. t - len / rfs_vscalar V t x < s /\ s <= t
          ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
              open_in (rfs_vtop V s) (IMAGE e (rfs_neck_dom eps))) /\
     rfs_close_fam (rfs_kreg eps) eps {s | --len < s /\ s <= &0}
                   (rfs_neck_dom eps) cylinder_flow
                   (\s y. rfs_vscalar V t x %%
                          rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                                       (rfs_vmetric V (t + s / rfs_vscalar V t x)) y)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_evolving_neck; rfs_persists; rfs_vtop; rfs_vatlas;
              rfs_vmetric; rfs_vscalar]);;

let P2BN_RFS_VSCALAR = prove
 (`!V t (x:A). rfs_vscalar V t x = mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) x`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric]);;

(* |Rm| at the centre of an evolving eps-neck along its window: at every    *)
(* time t + s/R(x), -len < s <= 0, at which the slice is a smooth          *)
(* Riemannian manifold carrying the parametrization, |Rm|(x) <= K1 R(x).    *)
(* The rescaled pullback is C^2-close to the shrinking cylinder at s, whose *)
(* curvature is uniformly bounded (P2BN_CYL_RM_BOUND); LRG_RM_NEAR_BOUND    *)
(* bounds its curvature, and sectional curvatures transfer through the      *)
(* chart representation of e (APX_PULLBACK_SECTIONAL_GEN).                  *)

let P2BN_EVNECK_RM = prove
 (`?K1. &0 < K1 /\
     !V eps (x:A) t len e s.
        &0 < eps /\ eps <= &1 / &4 /\ rfs_evolving_neck V eps x t len e /\
        --len < s /\ s <= &0 /\
        smooth_manifold_atlas (rfs_vtop V (t + s / rfs_vscalar V t x))
                              (rfs_vatlas V (t + s / rfs_vscalar V t x)) /\
        riemannian_metric (rfs_vatlas V (t + s / rfs_vscalar V t x))
                          (rfs_vmetric V (t + s / rfs_vscalar V t x)) /\
        mfd_param (rfs_vtop V (t + s / rfs_vscalar V t x))
                  (rfs_vatlas V (t + s / rfs_vscalar V t x)) (rfs_neck_dom eps) e
        ==> mfd_rm_norm (rfs_vatlas V (t + s / rfs_vscalar V t x))
                        (rfs_vmetric V (t + s / rfs_vscalar V t x)) x
            <= K1 * rfs_vscalar V t x`,
  X_CHOOSE_TAC `K0:real` P2BN_CYL_RM_BOUND THEN
  X_CHOOSE_TAC `K:real` (SPEC `K0 pow 2` LRG_RM_NEAR_BOUND) THEN
  EXISTS_TAC `sqrt(abs K) + &1` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `abs K` SQRT_POS_LE) THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_fam")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ ~(y0 = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPECL [`s:real`; `y0:real^3`]))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                    (rfs_vmetric V t) x` THEN
  ABBREV_TAC `u = t + s / R` THEN
  ABBREV_TAC `top' = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) u` THEN
  ABBREV_TAC `atl = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) u` THEN
  ABBREV_TAC `g' = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) u` THEN
  ABBREV_TAC `G = \z. R %% rfs_pullback atl (e:real^3->A) (g':A->real^3^3) z` THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (rfs_pullback atl (e:real^3->A) (g':A->real^3^3)) /\
                metric_field (rfs_neck_dom eps) (G:real^3->real^3^3) /\
                metric_field (rfs_neck_dom eps) (cylinder_flow s)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ r ==> p /\ q /\ r`) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top':A topology` THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXPAND_TAC "G" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 0 (G:real^3->real^3^3) y0 <= K` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    EXISTS_TAC `cylinder_flow s` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0 pow 2` THEN REWRITE_TAC[REAL_LE_REFL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow s) (G:real^3->real^3^3) y0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &4) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lrm_deriv_norm2 0 (G:real^3->real^3^3) y0) <= sqrt(abs K)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':A topology`; `atl:((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `y0:real^3`] APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
    (X_CHOOSE_THEN `h':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`N':real^3->bool`; `N:real^3->bool`;
                 `SND(chart_at (atl:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y0)) o e`;
                 `h':real^3->real^3`; `y0:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative
                    (SND(chart_at (atl:((A->bool)#(A->real^3))->bool) (x:A)) o (e:real^3->A))
                    (at y0)` THEN
  SUBGOAL_THEN
   `!p q. ~collinear {vec 0,p,q}
          ==> abs(mfd_sectional atl (g':A->real^3^3) x ((D:real^3->real^3) p) (D q))
              <= sqrt(abs K) * R`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atl (e:real^3->A) (g':A->real^3^3)`;
                   `R:real`; `y0:real^3`; `p:real^3`; `q:real^3`] APX_LSECTIONAL_SCALE) THEN
    MP_TAC(ISPECL [`top':A topology`; `atl:((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                   `rfs_neck_dom eps`; `e:real^3->A`; `y0:real^3`; `p:real^3`; `q:real^3`]
      APX_PULLBACK_SECTIONAL_GEN) THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `G:real^3->real^3^3`; `y0:real^3`; `p:real^3`;
                   `q:real^3`] RFA_LSECTIONAL_LRM_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    SUBGOAL_THEN `lsectional (rfs_pullback atl (e:real^3->A) (g':A->real^3^3)) y0 p q =
                  R * lsectional (G:real^3->real^3^3) y0 p q`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`; ASSUME `&0 < R`] THEN
    SUBGOAL_THEN `R * abs(lsectional (G:real^3->real^3^3) y0 p q) <= R * sqrt(abs K)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(abs K) * R` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH_RULE `2 <= 3`] THEN
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN DISCH_TAC THEN
    ABBREV_TAC `D' = frechet_derivative (h':real^3->real^3)
                       (at ((SND(chart_at (atl:((A->bool)#(A->real^3))->bool)
                                (x:A)) o (e:real^3->A)) y0))` THEN
    SUBGOAL_THEN `(D:real^3->real^3) (D' a) = a /\ D (D' b) = b` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(D':real^3->real^3) a`; `(D':real^3->real^3) b`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~collinear {vec 0,a:real^3,b}` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `{vec 0,a:real^3,b} = IMAGE (D:real^3->real^3) {vec 0,D' a,D' b}`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
      MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (D:real^3->real^3)`)) THEN SIMP_TAC[];
      MATCH_MP_TAC COLLINEAR_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Persistence of an open set covered by persisting sets.  If                *)
(* on every persisting set the identity is a homeomorphism between the     *)
(* slices at s and at b (the diffeomorphism clause of regular views), a     *)
(* nonempty open set of the slice at b each of whose points lies in a set  *)
(* persisting over (a,b] persists over (a,b].                               *)
(* ========================================================================= *)

let P2BN_OPEN_IN_IDENTITY = prove
 (`!top top' (N:A->bool) W.
     homeomorphic_maps (subtopology top N,subtopology top' N) ((\y. y),(\y. y)) /\
     open_in top N /\ open_in top' N /\ open_in top' W
     ==> open_in top (W INTER N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology top' N) ((W:A->bool) INTER N)` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology top N) ((W:A->bool) INTER N)` MP_TAC THENL
   [MP_TAC(ISPECL [`\y:A. y`; `subtopology top (N:A->bool)`; `subtopology top' (N:A->bool)`;
                   `(W:A->bool) INTER N`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [homeomorphic_maps]);
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> concl th = `open_in (top:A topology) N`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]);;

let P2BN_PERSISTS_ALT = prove
 (`!V (W:A->bool) a b.
     rfs_persists V W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\ open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas]);;

let P2BN_PERSISTS_COVER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     a < b /\
     (!N s. a < s /\ s <= b /\ rfs_persists V N a b
            ==> homeomorphic_maps (subtopology (rfs_vtop V s) N,subtopology (rfs_vtop V b) N)
                                  ((\y. y),(\y. y))) /\
     ~(W = {}) /\ open_in (rfs_vtop V b) W /\
     (!w. w IN W ==> ?N. w IN N /\ rfs_persists V N a b)
     ==> rfs_persists V W a b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "id")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cov"))))) THEN
  REWRITE_TAC[P2BN_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `w0:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    USE_THEN "cov" (MP_TAC o C MATCH_MP (ASSUME `(w0:A) IN W`)) THEN
    REWRITE_TAC[P2BN_PERSISTS_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (MP_TAC o SPEC `s:real` o CONJUNCT2)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  USE_THEN "cov" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN W`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(W:A->bool) INTER N` THEN ASM_REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN
  MATCH_MP_TAC P2BN_OPEN_IN_IDENTITY THEN
  EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) b` THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) N a b` THEN
  REWRITE_TAC[P2BN_PERSISTS_ALT] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Centres of eps-necks are kappa0-noncollapsed, kappa0 =                    *)
(* pi/750, at every scale r with |Rm| <= r^-2 at the centre                  *)
(* (P2BN_NECK_NONCOLL), and the ball B(x,r) with r sqrt(R(x)) <= 2 lies in  *)
(* the image of a compact core of the neck (P2BN_NECK_BALL_IN).              *)
(*                                                                           *)
(* Proof idea: the centre has a plane of sectional curvature about R/2       *)
(* (APX_NECK_PLANES), so r <= 2 R^(-1/2); the ball B(x,r) lies in the image  *)
(* of a compact part of the neck (exit and distance bounds of MT Lemma A.2)  *)
(* and contains the image of the flat ball of radius r sqrt(R)/10 about the  *)
(* preimage of x; then LIM_VOL_IMAGE_LOWER with the C^0 bounds of the neck.  *)
(* ========================================================================= *)

(* Copies of three small lemmas of pc_p2c_horns and of                       *)
(* P2BN_PULLBACK_OPEN_UNIV of pc_p3_c17vol, so that this unit loads no       *)
(* Part 3 proof unit.                                                        *)

let P2BN_NECK_DOM_SVAL = prove
 (`!eps y:real^3. &0 < eps /\ y IN rfs_neck_dom eps ==> abs(apx_sval y) < inv eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; apx_sval] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `exp(--(inv(sqrt(&2) * eps)))` THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(norm(y:real^3))) < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x k. --k < x /\ x < k ==> abs x < k`) THEN CONJ_TAC THENL
     [SUBGOAL_THEN `--(inv(sqrt(&2) * eps)) < log(norm(y:real^3)) <=>
                    exp(--(inv(sqrt(&2) * eps))) < exp(log(norm(y:real^3)))`
        SUBST1_TAC THENL [REWRITE_TAC[REAL_EXP_MONO_LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[EXP_LOG];
      SUBGOAL_THEN `log(norm(y:real^3)) < inv(sqrt(&2) * eps) <=>
                    exp(log(norm(y:real^3))) < exp(inv(sqrt(&2) * eps))`
        SUBST1_TAC THENL [REWRITE_TAC[REAL_EXP_MONO_LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[EXP_LOG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  SUBGOAL_THEN `inv eps = sqrt(&2) * inv(sqrt(&2) * eps)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]);;

let P2BN_SPHERE_SVAL = prove
 (`!y:real^3. y IN sphere(vec 0,&1) ==> apx_sval y = &0`,
  GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0; apx_sval] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LOG_1; REAL_MUL_RZERO]);;

let P2BN_SPHERE_IN_NECK_DOM = prove
 (`!eps y:real^3. &0 < eps /\ y IN sphere(vec 0,&1) ==> y IN rfs_neck_dom eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0; rfs_neck_dom; annulus; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BN_PULLBACK_OPEN_UNIV = prove
 (`!atlas (e:real^N->A) (g:A->real^N^N) y.
     mfd_pullback_metric (open_set_atlas (:real^N)) atlas e g y = rfs_pullback atlas e g y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_pullback_metric; rfs_pullback; GEOL_EUCLID_FACTS] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]);;


(* The flat model: balls and their volumes (the same facts as FLT_EUCLID_BALL *)
(* and FLT_EUCLID_VOLUME of pc_p2b_flatknc, whose closure is about 9.7K      *)
(* lines larger than this unit's).                                           *)

let P2BN_FLAT_BALL = prove
 (`!(x:real^3) r.
     mfd_ball (euclidean,open_set_atlas (:real^3)) (\x. mat 1) x r = ball(x,r)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(:real^3)` MFD_DIST_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; CONVEX_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[mfd_ball; EXTENSION; IN_ELIM_THM; IN_BALL]);;

let P2BN_FLAT_BALL_VOLUME = prove
 (`!(p:real^3) r.
     &0 <= r
     ==> mfd_has_volume (euclidean,open_set_atlas (:real^3)) (\x. mat 1) (ball(p,r))
           (&4 / &3 * pi * r pow 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `ball(p:real^3,r)`; `&4 / &3 * pi * r pow 3`]
    MFD_HAS_VOLUME_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_BALL; VOLUME_BALL]);;

let P2BN_MFD_BALL_MONO = prove
 (`!top atlas (g:A->real^N^N) x r r'.
     r <= r' ==> mfd_ball (top,atlas) g x r SUBSET mfd_ball (top,atlas) g x r'`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Small arithmetic.                                                          *)

let P2BN_SQRT_1_EPS = prove
 (`!eps. eps <= &1 / &10 ==> &1 / &2 <= sqrt(&1 - eps)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC);;

let P2BN_INV_SQRT2_EPS = prove
 (`!eps. &0 < eps /\ eps <= &1 / &10 ==> &3 < inv(sqrt(&2) * eps)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&2) < &3 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * eps < &1 / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(&3 / &2) * eps` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt(&2) * eps`; `&1 / &3`] REAL_LT_INV2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let P2BN_EXP3_BOUNDS = prove
 (`&5 / &4 < exp(&3) /\ exp(--(&3)) < &3 / &4`,
  SUBGOAL_THEN `&4 <= exp(&3)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&3` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&4)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* The compact core of the neck domain used below; it contains the flat     *)
(* balls of radius 1/4 about the points of the unit sphere.                   *)

let P2BN_NECK_CORE_DOM = prove
 (`!eps. &0 < eps /\ eps <= &1 / &10
         ==> compact (cball(vec 0:real^3,exp(&3)) DIFF ball(vec 0,exp(--(&3)))) /\
             cball(vec 0:real^3,exp(&3)) DIFF ball(vec 0,exp(--(&3))) SUBSET
             rfs_neck_dom eps /\
             (!z:real^3. norm z = &1
                         ==> ball(z,&1 / &4) SUBSET
                             cball(vec 0,exp(&3)) DIFF ball(vec 0,exp(--(&3))))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2BN_INV_SQRT2_EPS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC P2BN_EXP3_BOUNDS THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; rfs_neck_dom; annulus;
                IN_ELIM_THM; REAL_NOT_LT] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--(&3))` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(&3)` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&3 / &4 < norm(y:real^3) /\ norm y < &5 / &4` MP_TAC THENL
     [UNDISCH_TAC `dist(z:real^3,y) < &1 / &4` THEN
      UNDISCH_TAC `norm(z:real^3) = &1` THEN CONV_TAC NORM_ARITH;
      ASM_REAL_ARITH_TAC]]);;

(* At the centre of a neck the curvature scale bounds r: r sqrt(R) <= 2.      *)

let P2BN_NECK_RM_SCALE = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x (e:real^3->A) r.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ &0 < r /\ mfd_rm_norm atlas g x <= inv(r pow 2)
        ==> r * sqrt(mfd_scalar atlas g x) <= &2`,
  MP_TAC(SPEC `&1 / &4` (INST_TYPE [`:A`,`:A`] APX_NECK_PLANES)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pl"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `r:real`] THEN
  STRIP_TAC THEN
  USE_THEN "pl" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3`
    (X_CHOOSE_THEN `u2:real^3` (X_CHOOSE_THEN `v2:real^3` STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` (MP_TAC o CONJUNCT1 o CONJUNCT2)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    MP_TAC(SPECL [`eps:real`] P2BN_SPHERE_IN_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `u2:real^3`; `v2:real^3`] RFA_MFD_SECTIONAL_LE_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `R <= &4 * inv(r pow 2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 * R <= &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r pow 2 * (&4 * inv(r pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> a * (&4 * inv a) = &4`; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ; REAL_POS; REAL_POW_MUL] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

(* Arithmetic for the exit and distance bounds.                              *)

let P2BN_ARITH_ABK = prove
 (`!a b k. &1 / &2 <= a /\ &10 <= b /\ &0 <= k ==> &5 * k <= a * k * b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&5 <= a * b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) * &10` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&5 * k <= (a * b) * k` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let P2BN_ARITH_MIN = prove
 (`!a k s b d r. &1 / &2 <= a /\ &0 < k /\ abs s < b /\ &10 <= b /\
                 a * k * min (abs s) (&2 * b - abs s) <= d /\ d < r /\ r <= &2 * k
                 ==> abs s < &4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `min (abs s) (&2 * b - abs s) = abs s` ASSUME_TAC THENL
   [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MATCH_MP_TAC(REAL_ARITH `~(&4 <= x) ==> x < &4`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 <= a * abs s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) * &4` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * k <= (a * abs s) * k` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2BN_SVAL_SMALL = prove
 (`!y:real^3. &0 < norm y /\ abs(apx_sval y) < &4
              ==> y IN cball(vec 0,exp(&3)) DIFF ball(vec 0,exp(--(&3)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&4 / &3 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(norm(y:real^3))) < &3` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(&3 <= x) ==> x < &3`) THEN DISCH_TAC THEN
    UNDISCH_TAC `abs(apx_sval (y:real^3)) < &4` THEN
    REWRITE_TAC[apx_sval; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(sqrt(&2)) = sqrt(&2)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&4 <= x ==> ~(x < &4)`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 / &3) * &3` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
  MP_TAC(SPEC `norm(y:real^3)` EXP_LOG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC);;

(* The ball of radius r <= 2 R^(-1/2) about a neck centre lies in the image  *)
(* of the compact core of the neck domain.                                   *)

let P2BN_NECK_BALL_IN = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) r.
     &0 < eps /\ eps <= &1 / &10 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ &0 < r /\ r * sqrt(mfd_scalar atlas g x) <= &2
     ==> mfd_ball (top,atlas) g x r SUBSET
         IMAGE e (cball(vec 0,exp(&3)) DIFF ball(vec 0,exp(--(&3))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z0:real^3) IN rfs_neck_dom eps /\ apx_sval z0 = &0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BN_SPHERE_IN_NECK_DOM; P2BN_SPHERE_SVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) z0))`
  ASSUME_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `k = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) z0)))` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &2 * k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` P2BN_SQRT_1_EPS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&10 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`eps:real`; `&1 / &10`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `(e:real^3->A) z0`; `q:A`;
                   `sqrt(&1 - eps) * k * inv eps`] APX_DIST_GE_CURVES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `(e:real^3->A) z0`; `e:real^3->A`;
                     `z0:real^3`; `gamma:real->A`] APX_NECK_EXIT01) THEN
      ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`sqrt(&1 - eps)`; `inv eps`; `k:real`] P2BN_ARITH_ABK) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `y:real^3` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BN_SVAL_SMALL THEN CONJ_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    MP_TAC(SPEC `--(inv(sqrt(&2) * eps))` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `(e:real^3->A) z0`; `e:real^3->A`;
                 `z0:real^3`; `y:real^3`] APX_NECK_DIST_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  DISCH_TAC THEN MATCH_MP_TAC P2BN_ARITH_MIN THEN
  MAP_EVERY EXISTS_TAC [`sqrt(&1 - eps)`; `k:real`; `inv eps`;
                        `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) z0) (e y)`;
                        `r:real`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BN_NECK_DOM_SVAL THEN ASM_REWRITE_TAC[]);;

(* Bounds of the cylinder quadratic form near the unit sphere.               *)

let P2BN_CYL_QF_BOUNDS = prove
 (`!y:real^3 w:real^3. &3 / &4 < norm y /\ norm y < &5 / &4
                ==> &32 / &25 * (w dot w) <= &2 / norm y pow 2 * (w dot w) /\
                    &2 / norm y pow 2 * (w dot w) <= &32 / &9 * (w dot w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= w dot (w:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &16 < norm(y:real^3) pow 2 /\ norm y pow 2 < &25 / &16`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `&9 / &16 = (&3 / &4) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&25 / &16 = (&5 / &4) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&32 / &25 <= &2 / norm(y:real^3) pow 2 /\
                &2 / norm y pow 2 <= &32 / &9` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

let P2BN_ARITH_QF_UP = prove
 (`!e X Y W. &0 <= e /\ e <= &1 / &10 /\ &0 <= X /\ &0 <= W /\ X <= &32 / &9 * W /\
             Y <= (&1 + e) * X
             ==> Y / &4 <= W`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&1 + e) * X <= (&11 / &10) * X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BN_ARITH_QF_LOW = prove
 (`!e X Y W. &0 <= e /\ e <= &1 / &10 /\ &0 <= W /\ &32 / &25 * W <= X /\
             (&1 - e) * X <= Y
             ==> W <= Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&9 / &10) * X <= (&1 - e) * X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Centres of eps-necks are noncollapsed at every curvature scale.            *)

let P2BN_NECK_NONCOLL = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x (e:real^3->A) r.
        &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ &0 < r /\ mfd_rm_norm atlas g x <= inv(r pow 2)
        ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\
                pi / &750 * r pow 3 <= v`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_RM_SCALE) THEN
  EXISTS_TAC `min eps1 (&1 / &10)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `r:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r * sqrt(mfd_scalar atlas (g:A->real^3^3) x) <= &2` ASSUME_TAC THENL
   [USE_THEN "sc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `r:real`]
                P2BN_NECK_BALL_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) z0)` THEN
  ABBREV_TAC `K = cball(vec 0:real^3,exp(&3)) DIFF ball(vec 0,exp(--(&3)))` THEN
  MP_TAC(SPEC `eps:real` P2BN_NECK_CORE_DOM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "core"))) THEN
  SUBGOAL_THEN `norm(z0:real^3) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `compact_in (top:A topology) (IMAGE (e:real^3->A) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  (* the ball has a volume *)
  SUBGOAL_THEN
   `mfd_has_volume (top,atlas) (g:A->real^3^3)
      (mfd_ball (top,atlas) g ((e:real^3->A) z0) r)
      (mfd_volume (top,atlas) g (mfd_ball (top,atlas) g (e z0) r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN EXISTS_TAC `IMAGE (e:real^3->A) K` THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_volume (top,atlas) (g:A->real^3^3)
                (mfd_ball (top,atlas) g ((e:real^3->A) z0) r)` THEN
  ASM_REWRITE_TAC[] THEN
  (* the flat ball and its image *)
  ABBREV_TAC `rho = r * sqrt R / &10` THEN
  SUBGOAL_THEN `&0 < sqrt R` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &10`];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `U = ball(z0:real^3,&1 / &4)` THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET K /\ open U /\ (z0:real^3) IN U /\
                ball(z0,rho) SUBSET U`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    CONJ_TAC THENL [USE_THEN "core" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN U ==> &3 / &4 < norm y /\ norm y < &5 / &4`
  ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_BALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `dist(z0:real^3,y) < &1 / &4` THEN
    UNDISCH_TAC `norm(z0:real^3) = &1` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `?e''. mfd_diffeo euclidean (open_set_atlas (:real^3)) U (top:A topology)
                                 (atlas:((A->bool)#(A->real^3))->bool)
                                 (IMAGE (e:real^3->A) U) e e''`
  (X_CHOOSE_TAC `e'':A->real^3`) THENL
   [REWRITE_TAC[GSYM mfd_param] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* quadratic form bounds of the pullback on U *)
  SUBGOAL_THEN
   `!y w:real^3. y IN U
          ==> &32 / &25 * (w dot w) <=
              &2 / norm(y:real^3) pow 2 * (w dot w) /\
              &2 / norm y pow 2 * (w dot w) <= &32 / &9 * (w dot w) /\
              (&1 - eps) * (&2 / norm y pow 2 * (w dot w)) <=
              R * (w dot (mfd_pullback_metric (open_set_atlas (:real^3)) atlas
                            (e:real^3->A) (g:A->real^3^3) y ** w)) /\
              R * (w dot (mfd_pullback_metric (open_set_atlas (:real^3)) atlas e g y ** w))
              <= (&1 + eps) * (&2 / norm y pow 2 * (w dot w))`
  (LABEL_TAC "qf") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2BN_CYL_QF_BOUNDS]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2BN_CYL_QF_BOUNDS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `(e:real^3->A) z0`; `e:real^3->A`;
                   `y:real^3`; `w:real^3`] APX_NECK_C0_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[P2BN_PULLBACK_OPEN_UNIV; APX_CYL0_QUAD; MATRIX_VECTOR_LMUL; DOT_RMUL];
    ALL_TAC] THEN
  (* the image of the flat ball lies in B(x, r) *)
  SUBGOAL_THEN `IMAGE (e:real^3->A) (ball(z0,rho)) SUBSET
                mfd_ball (top,atlas) (g:A->real^3^3) (e z0) r`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:A). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) ((e:real^3->A) z0)
                  (sqrt((&1 + &0) / (R / &4)) * rho)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIM_PB_BALL_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                            `\x:real^3. mat 1:real^3^3`; `U:real^3->bool`;
                            `IMAGE (e:real^3->A) U`; `e'':A->real^3`] THEN
      ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; P2BN_FLAT_BALL; REAL_LE_REFL] THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LID; REAL_ADD_RID;
                                          REAL_MUL_LID] THEN
        MATCH_MP_TAC(REAL_ARITH `(R * Z) / &4 <= W ==> R / &4 * Z <= W`) THEN
        MATCH_MP_TAC P2BN_ARITH_QF_UP THEN
        MAP_EVERY EXISTS_TAC [`eps:real`; `&2 / norm(y:real^3) pow 2 * ((v:real^3) dot v)`] THEN
        USE_THEN "qf" (MP_TAC o SPECL [`y:real^3`; `v:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[DOT_POS_LE] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_MUL; REAL_LE_DIV; REAL_POS; REAL_LE_POW_2;
                     DOT_POS_LE]];
      MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN EXPAND_TAC "rho" THEN
      SUBGOAL_THEN `sqrt((&1 + &0) / (R / &4)) = &2 / sqrt R` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ADD_RID] THEN
        SUBGOAL_THEN `&1 / (R / &4) = &4 / R` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        ASM_SIMP_TAC[SQRT_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
        SUBGOAL_THEN `sqrt(&4) = &2` SUBST1_TAC THENL
         [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; REFL_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&2 / sqrt R * r * sqrt R / &10 = r / &5` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt R` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the volume of the image of the flat ball *)
  SUBGOAL_THEN
   `mfd_has_volume (top,atlas) (g:A->real^3^3) (IMAGE (e:real^3->A) (ball(z0,rho)))
      (mfd_volume (top,atlas) g (IMAGE e (ball(z0,rho))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN EXISTS_TAC `IMAGE (e:real^3->A) K` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `\x:real^3. mat 1:real^3^3`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:real^3->bool`; `IMAGE (e:real^3->A) U`; `e:real^3->A`; `e'':A->real^3`;
                 `ball(z0:real^3,rho)`; `&4 / &3 * pi * rho pow 3`;
                 `mfd_volume (top,atlas) (g:A->real^3^3) (IMAGE (e:real^3->A) (ball(z0,rho)))`;
                 `R:real`; `&0`] LIM_VOL_IMAGE_LOWER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GEOL_EUCLID_FACTS; P2BN_FLAT_BALL_VOLUME; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LID; REAL_SUB_RZERO;
                                      REAL_MUL_LID] THEN
    MATCH_MP_TAC P2BN_ARITH_QF_LOW THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `&2 / norm(y:real^3) pow 2 * ((w:real^3) dot w)`] THEN
    USE_THEN "qf" (MP_TAC o SPECL [`y:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[DOT_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_MUL_LID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `IMAGE (e:real^3->A) (ball(z0,rho))`;
                 `mfd_ball (top,atlas) (g:A->real^3^3) ((e:real^3->A) z0) r`;
                 `mfd_volume (top,atlas) (g:A->real^3^3) (IMAGE (e:real^3->A) (ball(z0,rho)))`;
                 `mfd_volume (top,atlas) (g:A->real^3^3)
                    (mfd_ball (top,atlas) g ((e:real^3->A) z0) r)`] MFD_HAS_VOLUME_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* arithmetic *)
  ABBREV_TAC `sR = sqrt R` THEN
  SUBGOAL_THEN `R = sR pow 2` SUBST_ALL_TAC THENL
   [EXPAND_TAC "sR" THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `&4 / &3 * pi * rho pow 3 <=
               sR pow 2 * sR *
               mfd_volume (top,atlas) (g:A->real^3^3) (IMAGE (e:real^3->A) (ball(z0,rho)))` THEN
  SUBGOAL_THEN `rho pow 3 = (r * sR / &10) pow 3` SUBST1_TAC THENL
   [EXPAND_TAC "rho" THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sR pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 / &3 * pi * (r * sR / &10) pow 3 = (pi / &750 * r pow 3) * sR pow 3 /\
    sR pow 2 * sR * mfd_volume (top,atlas) (g:A->real^3^3) (IMAGE (e:real^3->A) (ball(z0,rho))) =
    mfd_volume (top,atlas) g (IMAGE e (ball(z0,rho))) * sR pow 3`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The backward and volume hypotheses of local compactness                   *)
(* for sets of strong-neck centres (general forms of R1 and R2 of           *)
(* pc_p2b_lcreqg).  An open set W at time 0 of a view whose points are      *)
(* centres of strong eps-necks with R <= K persists on (-1/K, 0] with       *)
(* |Rm| <= K1 K there (P2BN_NECK_SET_BACKWARD); a ball of radius r about a  *)
(* neck centre with |Rm| <= K and compact closure has volume at least       *)
(* pi/750 min(r, K^(-1/2))^3 (P2BN_NECK_BALL_VOLUME).                        *)
(* ========================================================================= *)

(* Facts at the centre of a neck (P2BN_NECK_CENTRE_FACTS).                   *)

let P2BN_NECK_CENTRE_FACTS = prove
 (`!top atlas (g:A->real^3^3) eps x e.
     rfs_neck (top,atlas) g eps x e
     ==> smooth_manifold_atlas top atlas /\ x IN topspace top /\
         &0 < mfd_scalar atlas g x /\ x IN IMAGE e (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` (MP_TAC o CONJUNCT1 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[]);;

(* Backward neighbourhoods: persistence and the curvature bound.  The two   *)
(* hypotheses on V are the slice and diffeomorphism clauses of               *)
(* p2c_regular_view.                                                          *)

let P2BN_NECK_SET_BACKWARD = prove
 (`?K1. &0 < K1 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      eps W K.
        (!s. ~(topspace(rfs_vtop V s) = {})
             ==> riemannian_metric (rfs_vatlas V s) (rfs_vmetric V s)) /\
        (!N a b s. a < s /\ s <= b /\ rfs_persists V N a b
                   ==> mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) N
                                  (rfs_vtop V b) (rfs_vatlas V b) N (\y:A. y) (\y. y)) /\
        &0 < eps /\ eps <= &1 / &4 /\ &0 < K /\
        open_in (rfs_vtop V (&0)) W /\ ~(W = {}) /\
        (!w. w IN W ==> (?e. rfs_strong_neck V eps w (&0) e) /\
                        rfs_vscalar V (&0) w <= K)
        ==> rfs_persists V W (--inv K) (&0) /\
            !s w. --inv K < s /\ s <= &0 /\ w IN W
                  ==> mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) w <= K1 * K`,
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm"))
    (INST_TYPE [`:A`,`:A`] P2BN_EVNECK_RM) THEN
  EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rg") (CONJUNCTS_THEN2 (LABEL_TAC "df")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk")))))))) THEN
  SUBGOAL_THEN
   `!w:A. w IN W
          ==> ?e. rfs_evolving_neck V eps w (&0) (&1) e /\
                  w IN IMAGE e (rfs_neck_dom eps) /\
                  &0 < rfs_vscalar V (&0) w /\ rfs_vscalar V (&0) w <= K /\
                  rfs_persists V (IMAGE e (rfs_neck_dom eps)) (--inv K) (&0)`
  (LABEL_TAC "pn") THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN W`)) THEN
    REWRITE_TAC[rfs_strong_neck] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real^3->A`) ASSUME_TAC) THEN
    EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2BN_EVOLVING_NECK_ALT]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS)
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pe") (K ALL_TAC)))) THEN
    REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2BN_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "pe" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv K <= &1 / rfs_vscalar V (&0) (w:A)` MP_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BN_PERSISTS_COVER THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_NEG_LT0; REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) N (rfs_vtop V (&0)) (rfs_vatlas V (&0)) N
                   (\y:A. y) (\y. y)`
      MP_TAC THENL
       [USE_THEN "df" MATCH_MP_TAC THEN EXISTS_TAC `--inv K` THEN ASM_REWRITE_TAC[];
        SIMP_TAC[mfd_diffeo]];
      X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      USE_THEN "pn" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN W`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `w:A`] THEN STRIP_TAC THEN
  USE_THEN "pn" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN W`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `s:real` (GEN_REWRITE_RULE I [P2BN_PERSISTS_ALT]
    (ASSUME `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3)) (IMAGE (e:real^3->A) (rfs_neck_dom eps)) (--inv K) (&0)`))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A) IN topspace(rfs_vtop V s)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) s) (IMAGE (e:real^3->A) (rfs_neck_dom eps))`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas V s) (rfs_vmetric (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)`
  ASSUME_TAC THENL
   [USE_THEN "rg" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop V s) (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)
                  (rfs_neck_dom eps) (e:real^3->A)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2BN_EVOLVING_NECK_ALT]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^3->A) = (\y:A. y) o e` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (&0)`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) (&0)`;
      `IMAGE (e:real^3->A) (rfs_neck_dom eps)`; `IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
      `\y:A. y`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "df" MATCH_MP_TAC THEN
    EXISTS_TAC `--inv K` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) < s * rfs_vscalar V (&0) (w:A) /\ s * rfs_vscalar V (&0) w <= &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `--inv K * rfs_vscalar V (&0) (w:A)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_NEG2] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv K * K` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
          ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "rm" (MP_TAC o SPECL
    [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `eps:real`; `w:A`; `&0`; `&1`; `e:real^3->A`; `s * rfs_vscalar V (&0) (w:A)`]) THEN
  SUBGOAL_THEN `&0 + (s * rfs_vscalar V (&0) (w:A)) / rfs_vscalar V (&0) w = s`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `&0 < rfs_vscalar V (&0) (w:A)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `K1 * rfs_vscalar V (&0) (w:A)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* Volume lower bound for a ball about a neck centre.                        *)

let P2BN_NECK_BALL_VOLUME = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x (e:real^3->A) r K.
        &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ &0 < r /\ &0 < K /\ mfd_rm_norm atlas g x <= K /\
        compact_in top (top closure_of mfd_ball (top,atlas) g x r)
        ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\
                pi / &750 * min r (inv(sqrt K)) pow 3 <= v`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_NONCOLL) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r' = min r (inv(sqrt K))` THEN
  SUBGOAL_THEN `&0 < r' /\ r' <= r /\ mfd_rm_norm atlas (g:A->real^3^3) x <= inv(r' pow 2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(sqrt K)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r' /\ r' <= r /\ r' <= inv(sqrt K)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r' pow 2 <= inv K` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv K = inv(sqrt K) pow 2` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  USE_THEN "nc" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `r':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_volume (top,atlas) (g:A->real^3^3) (mfd_ball (top,atlas) g x r)
      (mfd_volume (top,atlas) g (mfd_ball (top,atlas) g x r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN
    EXISTS_TAC `top closure_of mfd_ball (top,atlas) (g:A->real^3^3) x r` THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_SIMP_TAC[MFD_BALL_OPEN];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_volume (top,atlas) (g:A->real^3^3) (mfd_ball (top,atlas) g x r)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v':real` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `mfd_ball (top,atlas) (g:A->real^3^3) x r'`;
                 `mfd_ball (top,atlas) (g:A->real^3^3) x r`; `v':real`;
                 `mfd_volume (top,atlas) (g:A->real^3^3) (mfd_ball (top,atlas) g x r)`]
                MFD_HAS_VOLUME_MONO) THEN
  ASM_SIMP_TAC[P2BN_MFD_BALL_MONO]);;

(* ========================================================================= *)
(* The scalar curvature along an evolving neck, R(e y, t + s/R) / R(x,t)     *)
(* within alpha of 1/(1 - s), used by pc_p2c_horns2.  Renamed copies of      *)
(* P3H_CYL_SCALAR_STAB and P3H_NECK_SCALAR of pc_p3_c172d; their use of the  *)
(* cylinder bound is P2BN_CYL_RM_BOUND above.  (pc_p3_c172d loads            *)
(* pc_p3_route.)                                                             *)
(* ========================================================================= *)

let P2BN_CYL_SCALAR_STAB = prove
 (`!alpha. &0 < alpha
     ==> ?eta. &0 < eta /\
           !s S (G:real^3->real^3^3) y.
              s <= &0 /\ open S /\ S SUBSET ((:real^3) DELETE vec 0) /\ metric_field S G /\
              y IN S /\ lck_dist2 2 (cylinder_flow s) G y < eta pow 2
              ==> abs(lscalar G y - &1 / (&1 - s)) <= alpha`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_TAC `K0:real` P2BN_CYL_RM_BOUND THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] (SPECL [`K0:real`; `alpha:real`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `S:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`S:real^3->bool`; `cylinder_flow s`; `G:real^3->real^3^3`;
                                `y:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `lscalar (cylinder_flow s) y = &1 / (&1 - s)` SUBST1_TAC THENL
   [MATCH_MP_TAC RFB_CYL_SCALAR THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

let P2BN_NECK_SCALAR = prove
 (`!alpha. &0 < alpha
     ==> ?eps2. &0 < eps2 /\
           !V eps x t a (e:real^3->A) s y0.
              p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\ eps <= eps2 /\
              --a < s /\ s <= &0 /\ y0 IN rfs_neck_dom eps
              ==> abs(rfs_vscalar V (t + s / rfs_vscalar V t x) (e y0) / rfs_vscalar V t x -
                      &1 / (&1 - s)) <= alpha`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BN_CYL_SCALAR_STAB) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  EXISTS_TAC `min eta (&1 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`; `s:real`] P2B9_REGULAR_NECK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2B9_EVOLVING_NECK_ALT] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[rfs_close_fam; IN_ELIM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t x` THEN
  ABBREV_TAC `u = t + s / Q` THEN
  ABBREV_TAC `H = \z. Q %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) (e:real^3->A)
                     (rfs_vmetric V u) z` THEN
  SUBGOAL_THEN `lscalar (H:real^3->real^3^3) y0 = rfs_vscalar (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u (e y0) / Q`
  (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[P2B9_RFS_VSCALAR] THEN
    MATCH_MP_TAC P2B9_PARAM_LSCALAR_SCALED THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                          `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "st" MATCH_MP_TAC THEN EXISTS_TAC `rfs_neck_dom eps` THEN
  ASM_REWRITE_TAC[APX_NECK_DOM_OPEN; P2BL_NECK_DOM_NZ] THEN CONJ_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow s) (H:real^3->real^3^3) y0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
        EXISTS_TAC `rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "H" THEN EXPAND_TAC "u" THEN USE_THEN "cl" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

