(* ========================================================================= *)
(* Unit pc_p2c_cg (Part 2C): MT Cor 5.10 (via Thm 5.9) on the carrier        *)
(* real^3.  The view slices rescaled by Q n satisfy the hypotheses of        *)
(* p2cu_seq (scaling of balls, curvature derivatives and volumes); the       *)
(* embeddings of pc_p2c_cgemb are re-indexed along a diagonal subsequence    *)
(* (the k-th map lives on W k and has C^m error < 1 / (k + 1) for m <= k);   *)
(* this gives p3_slice_limit, i.e. P2CK_CG_COMPACT                           *)
(* |- P2C_CG_COMPACT_STATEMENT u (:real^3), where the statement              *)
(* P2C_REQ_CGT_STATEMENT is CMP_T2_CGT (pc_cmp_cgt) and the relative volume  *)
(* bound is CMP_RELVOL (pc_cmp_relvol, used in pc_p2c_cgunif).               *)
(* ========================================================================= *)

needs "src/pc_p2c_cgemb.ml";;
needs "src/pc_cmp_cgt.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_p2b_lim.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The scaling reduction.  The view slices with the metrics                  *)
(* rescaled by Q n form a sequence p2cu_seq: balls of radius A for the       *)
(* rescaled metric are the balls of radius A / sqrt(Q n) (MFD_BALL_SCALE),   *)
(* the curvature derivatives scale by inv(Q n) pow (l + 2)                   *)
(* (RFA_LRM_DERIV_NORM2_SCALE) and volumes by sqrt(Q n pow 3)                *)
(* (MFD_HAS_VOLUME_SCALE).                                                   *)
(* ------------------------------------------------------------------------- *)

let P2CK_VOL_ARITH = prove
 (`!s kappa r0 v.
     &0 < s /\ kappa * (r0 * inv s) pow 3 <= v
     ==> kappa * r0 pow 3 <= sqrt((s pow 2) pow 3) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt((s pow 2) pow 3) = s pow 3` SUBST1_TAC THENL
   [SUBGOAL_THEN `(s pow 2) pow 3 = (s pow 3) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW; ARITH_RULE `2 * 3 = 3 * 2`]; ALL_TAC] THEN
    MATCH_MP_TAC POW_2_SQRT THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  UNDISCH_TAC `kappa * (r0 * inv s) pow 3 <= v` THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let P2CK_SCALED_SEQ = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q.
       (!n. hausdorff_space (rfs_vtop (V n) (t n)) /\
            smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n)) /\
            riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
            (x n:A) IN topspace(rfs_vtop (V n) (t n)) /\ &0 < Q n) /\
       (!A. &0 < A
            ==> ?N. !n. N <= n
                        ==> compact_in (rfs_vtop (V n) (t n))
                              (rfs_vtop (V n) (t n) closure_of
                               rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))) /\
       (!A l. &0 < A
              ==> ?CAl N. !n y. N <= n /\
                                y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                ==> p3_vderiv2 (V n) l (t n) y <= CAl * Q n pow (l + 2)) /\
       (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
          !n. N <= n
              ==> ?v. mfd_has_volume (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                        (rfs_vmetric (V n) (t n))
                        (rfs_vball (V n) (t n) (x n) (r0 * inv(sqrt(Q n)))) v /\
                      kappa * (r0 * inv(sqrt(Q n))) pow 3 <= v)
       ==> p2cu_seq (\k. rfs_vtop (V k) (t k)) (\k. rfs_vatlas (V k) (t k))
                    (\k z. Q k %% rfs_vmetric (V k) (t k) z) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (LABEL_TAC "vol")))) THEN
  SUBGOAL_THEN
   `!n r. rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) n) ((t:num->real) n) ((x:num->A) n) r =
          mfd_ball (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))
                   (x n) r`
  (LABEL_TAC "vb") THENL
   [REPEAT GEN_TAC THEN
    SPEC_TAC(`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) n`,
             `v:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n r. mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) n) ((t:num->real) n),
                    rfs_vatlas (V n) (t n))
                   (\z. (Q:num->real) n %% rfs_vmetric (V n) (t n) z) ((x:num->A) n) r =
          mfd_ball (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))
                   (x n) (r * inv(sqrt(Q n)))`
  (LABEL_TAC "bs") THENL
   [REPEAT GEN_TAC THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) n) ((t:num->real) n)`;
                   `rfs_vatlas ((V:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) ((t:num->real) n)`;
                   `rfs_vmetric ((V:num->(real->A topology)#
                                     (real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) n) ((t:num->real) n)`;
                   `(Q:num->real) n`; `(x:num->A) n`; `r:real`] MFD_BALL_SCALE) THEN
    ASM_SIMP_TAC[real_div];
    ALL_TAC] THEN
  REWRITE_TAC[p2cu_seq] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL; ETA_AX];
    X_GEN_TAC `R:real` THEN DISCH_TAC THEN
    USE_THEN "cpt" (MP_TAC o C MP (ASSUME `&0 < R`) o SPEC `R:real`) THEN
    USE_THEN "vb" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "bs" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`R:real`; `l:num`] THEN DISCH_TAC THEN
    USE_THEN "der" (MP_TAC o C MP (ASSUME `&0 < R`) o SPECL [`R:real`; `l:num`]) THEN
    USE_THEN "vb" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "bs" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[p3_vderiv2; METRIC_LOCAL_CMUL; ETA_AX] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "d"))) THEN
    EXISTS_TAC `C:real` THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "d" (MP_TAC o SPECL [`k:num`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t. (y:A) IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `mfd_ball (rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k),rfs_vatlas (V k) (t k)) (rfs_vmetric (V k) (t k))
                     ((x:num->A) k) (R * inv(sqrt((Q:num->real) k)))` THEN
      ASM_SIMP_TAC[P2CU_BALL_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k)`;
                   `rfs_vatlas ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k)`; `y:A`] CHART_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL
     [`IMAGE (SND(chart_at (rfs_vatlas ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k))
          (y:A)))
        (FST(chart_at (rfs_vatlas (V k) (t k)) y))`;
      `metric_local (rfs_vatlas ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k))
        (chart_at (rfs_vatlas (V k) (t k)) (y:A)) (rfs_vmetric (V k) (t k))`;
      `(Q:num->real) k`; `l:num`;
      `SND(chart_at (rfs_vatlas ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k))
          (y:A)) y`]
     RFA_LRM_DERIV_NORM2_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (rfs_vatlas ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k))
          (rfs_vmetric (V k) (t k))` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&0 < (Q:num->real) k pow (l + 2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_INV] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ];
    USE_THEN "vol" (X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `kappa:real`
      (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`r0:real`; `kappa:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= k`) o SPEC `k:num`) THEN
    USE_THEN "vb" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    EXISTS_TAC `sqrt((Q:num->real) k pow dimindex(:3)) * v` THEN
    USE_THEN "bs" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k)`;
                   `rfs_vatlas ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k)`;
                   `rfs_vmetric ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k)`;
                   `mfd_ball (rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     ((t:num->real) k),rfs_vatlas (V k) (t k)) (rfs_vmetric (V k) (t k))
                     ((x:num->A) k) (r0 * inv(sqrt((Q:num->real) k)))`;
                   `v:real`; `(Q:num->real) k`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[DIMINDEX_3] THEN
    SUBGOAL_THEN `(Q:num->real) k = sqrt(Q k) pow 2` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC P2CK_VOL_ARITH THEN ASM_SIMP_TAC[SQRT_POS_LT]]);;

(* ------------------------------------------------------------------------- *)
(* The diagonal re-indexing.  Given, for every level j, maps                 *)
(* Fm j n that are eventually diffeomorphisms of W j sending xl to x (sq n)  *)
(* and whose pulled-back metrics converge in every lck_dist2 m on the        *)
(* closure of W j, choose r k (strictly increasing) beyond the thresholds   *)
(* of level k for the orders m <= k and the error 1 / (k + 1); the k-th map  *)
(* is Fm k (r k) on W k.  A compact K lies in some W k1 (exhaustion), so for *)
(* k >= k1 + k2 + m the error at order m on K is < 1 / (k + 1) < eta.        *)
(* ------------------------------------------------------------------------- *)

let P2CK_DIAGONAL = prove
 (`!(top:num->A topology) atlas (h:num->A->real^3^3) (x:num->A) (M:(real^3)topology)
    (atlasM:((real^3->bool)#(real^3->real^3))->bool) (g:real^3->real^3^3) (xl:real^3)
    (W:num->real^3->bool) (sq:num->num).
     (!k. open_in M (W k) /\ M closure_of W k SUBSET W (SUC k)) /\
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
                             ==> lck_dist2 m (metric_local atlasM (chart_at atlasM y) g)
                                   (\z. rfs_pullback (atlas(sq n))
                                          (Fm n o chart_inv (chart_at atlasM y))
                                          (h(sq n)) z)
                                   (SND(chart_at atlasM y) y) < eta))
     ==> ?sub (phi:num->real^3->A).
           (!m n. m < n ==> sub m < sub n) /\
           (!k. phi k xl = x(sub k)) /\
           (!k. ?psi. mfd_diffeo M atlasM (W k) (top(sub k)) (atlas(sub k))
                        (IMAGE (phi k) (W k)) (phi k) psi) /\
           (!K m eta.
              compact_in M K /\ &0 < eta
              ==> ?k0. !k. k0 <= k
                           ==> K SUBSET W k /\
                               !y. y IN K
                                   ==> lck_dist2 m (metric_local atlasM (chart_at atlasM y) g)
                                         (\z. rfs_pullback (atlas(sub k))
                                                (phi k o chart_inv (chart_at atlasM y))
                                                (h(sub k)) z)
                                         (SND(chart_at atlasM y) y) < eta)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ex") (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (CONJUNCTS_THEN2 (LABEL_TAC "sq") MP_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Fm:num->num->real^3->A` MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `N0:num->num` (LABEL_TAC "n0") o REWRITE_RULE[SKOLEM_THM])
    (X_CHOOSE_THEN `Nl:num->num->real->num` (LABEL_TAC "nl") o
     REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) o
    REWRITE_RULE[FORALL_AND_THM]) THEN
  SUBGOAL_THEN `!k. ?b. (N0:num->num) k <= b /\
                        !m. m <= k ==> (Nl:num->num->real->num) k m (inv(&k + &1)) <= b`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`\m. (Nl:num->num->real->num) k m (inv(&k + &1))`; `{m:num | m <= k}`]
           UPPER_BOUND_FINITE_SET) THEN
    REWRITE_TAC[FINITE_NUMSEG_LE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN EXISTS_TAC `a + (N0:num->num) k` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x <= a ==> x <= a + b:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bd:num->num` (LABEL_TAC "bd") o REWRITE_RULE[SKOLEM_THM]) THEN
  SUBGOAL_THEN `?r:num->num. (!n. bd n <= r n) /\ (!n. r n < r(SUC n))` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN
    REWRITE_TAC[ARITH_RULE `a <= x /\ b < x <=> MAX a (SUC b) <= x`] THEN
    MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (r:num->num) m < r n` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_REWRITE_TAC[] THEN MESON_TAC[LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. (N0:num->num) k <= r k /\
                    !m. m <= k ==> (Nl:num->num->real->num) k m (inv(&k + &1)) <= r k`
  (LABEL_TAC "rb") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "bd" (MP_TAC o SPEC `k:num`) THEN
    SUBGOAL_THEN `(bd:num->num) k <= r k` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MESON_TAC[LE_TRANS];
    ALL_TAC] THEN
  EXISTS_TAC `\k:num. (sq:num->num)((r:num->num) k)` THEN
  EXISTS_TAC `\k:num. (Fm:num->num->real^3->A) k ((r:num->num) k)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    USE_THEN "sq" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN USE_THEN "n0" (MP_TAC o SPECL [`k:num`; `(r:num->num) k`]) THEN
    USE_THEN "rb" (MP_TAC o CONJUNCT1 o SPEC `k:num`) THEN MESON_TAC[];
    X_GEN_TAC `k:num` THEN USE_THEN "n0" (MP_TAC o SPECL [`k:num`; `(r:num->num) k`]) THEN
    USE_THEN "rb" (MP_TAC o CONJUNCT1 o SPEC `k:num`) THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. (W:num->real^3->bool) k SUBSET W (SUC k)` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `M closure_of (W:num->real^3->bool) k` THEN
    USE_THEN "ex" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:(real^3)topology`; `W:num->real^3->bool`; `K:real^3->bool`]
         P2B_COMPACT_IN_EXHAUST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k1:num`) THEN
  MP_TAC(ISPEC `W:num->real^3->bool` P2B_EXHAUST_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "mono") THEN
  MP_TAC(ISPEC `eta:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k1 + k2 + m:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET W (k:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(W:num->real^3->bool) k1` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv(&k + &1) /\ inv(&k + &1) < eta` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&k2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "nl" (MP_TAC o SPECL [`k:num`; `m:num`; `inv(&k + &1)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(r:num->num) k`; `y:real^3`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "rb" (MATCH_MP_TAC o CONJUNCT2 o SPEC `k:num`) THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `!s t. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `(W:num->real^3->bool) k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
        EXISTS_TAC `K:real^3->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
        USE_THEN "ex" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&k + &1)` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MT Cor 5.10 on the carrier real^3: the rescaled view slices               *)
(* (P2CK_SCALED_SEQ) have a complete pointed limit with embeddings of an     *)
(* exhaustion (P2CE_EMBED); the diagonal re-indexing (P2CK_DIAGONAL) and the *)
(* scaling of pullbacks give p3_slice_limit for a subsequence, under the     *)
(* statement P2C_REQ_CGT_STATEMENT (P2CK_CG_COMPACT_CGT).  That statement is *)
(* CMP_T2_CGT (pc_cmp_cgt), and the relative volume bound CMP_RELVOL         *)
(* (pc_cmp_relvol) is used inside pc_p2c_cgunif, so P2CK_CG_COMPACT holds    *)
(* with no hypotheses.                                                       *)
(* ------------------------------------------------------------------------- *)

let P2CK_CG_COMPACT_CGT = prove
 (`!u:A->bool. P2C_REQ_CGT_STATEMENT (:A) ==> P2C_CG_COMPACT_STATEMENT u (:real^3)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[P2C_CG_COMPACT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`] THEN
  DISCH_TAC THEN FIRST_ASSUM(LABEL_TAC "base" o CONJUNCT1) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2CK_SCALED_SEQ) THEN
  MP_TAC(ISPECL
   [`\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) k) ((t:num->real) k)`;
    `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) k) ((t:num->real) k)`;
    `\k z. (Q:num->real) k %% rfs_vmetric ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                      ((t:num->real) k) z`;
    `x:num->A`] P2CE_EMBED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:(real^3)topology` (X_CHOOSE_THEN
    `atlasM:((real^3->bool)#(real^3->real^3))->bool` (X_CHOOSE_THEN `g:real^3->real^3^3`
    (X_CHOOSE_THEN `xl:real^3` (X_CHOOSE_THEN `W:num->real^3->bool`
    (X_CHOOSE_THEN `sq:num->num` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL
   [`\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) k) ((t:num->real) k)`;
    `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) k) ((t:num->real) k)`;
    `\k z. (Q:num->real) k %% rfs_vmetric ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                      ((t:num->real) k) z`;
    `x:num->A`; `M:(real^3)topology`; `atlasM:((real^3->bool)#(real^3->real^3))->bool`;
    `g:real^3->real^3^3`; `xl:real^3`; `W:num->real^3->bool`; `sq:num->num`]
   P2CK_DIAGONAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!atl (e:real^3->A) (G:A->real^3^3) c.
      rfs_pullback atl e (\z. c %% G z) = (\z. c %% rfs_pullback atl e G z)`
  (LABEL_TAC "cmul") THENL
   [REWRITE_TAC[rfs_pullback; METRIC_LOCAL_CMUL; mpullback; FUN_EQ_THM] THEN
    REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `phi:num->real^3->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (fun th -> USE_THEN "cmul" (fun c ->
           LABEL_TAC "lk" (REWRITE_RULE[c; ETA_AX] th)))))))) THEN
  MAP_EVERY EXISTS_TAC
   [`sub:num->num`; `M:(real^3)topology`; `atlasM:((real^3->bool)#(real^3->real^3))->bool`;
    `g:real^3->real^3^3`; `xl:real^3`] THEN
  ASM_REWRITE_TAC[p3_subseq; p3_slice_limit; o_THM] THEN
  MAP_EVERY EXISTS_TAC [`W:num->real^3->bool`; `phi:num->real^3->A`] THEN
  ASM_REWRITE_TAC[]);;

let P2CK_CG_COMPACT = prove
 (`!u:A->bool. P2C_CG_COMPACT_STATEMENT u (:real^3)`,
  GEN_TAC THEN MATCH_MP_TAC P2CK_CG_COMPACT_CGT THEN
  MP_TAC(SPEC `(:A)` CMP_T2_CGT) THEN
  REWRITE_TAC[CMP_T2_CGT_STATEMENT; P2C_REQ_CGT_STATEMENT]);;

let P2CK_CG_COMPACT_ROUTE = prove
 (`!u:A->bool. P2C_CG_COMPACT_ROUTE_STATEMENT u (:real^3)`,
  REWRITE_TAC[P2C_CG_COMPACT_ROUTE_STATEMENT; P2CK_CG_COMPACT]);;

