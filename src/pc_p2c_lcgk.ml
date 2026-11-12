(* ========================================================================= *)
(* Unit pc_p2c_lcgk (Part 2C, the general form G of local compactness): the  *)
(* G instance of the general CG levels, the diagonal with a per-level        *)
(* predicate, the Brouwer image lemma, normal charts onto metric balls,      *)
(* images in U and the path lifting.                                         *)
(* ========================================================================= *)

needs "src/pc_p2c_lcga.ml";;
needs "src/pc_p2c_lcgb.ml";;
needs "src/pc_p2c_lcge.ml";;
needs "src/pc_p2b_lim.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The G instance of p2gb_levels (P2GA_LEVELS_RAW; the shift                *)
(* clause from P2GA_Y_SHIFT and the nets of the next level, whose balls have *)
(* radius rho/32, so the shift also holds with rho/32).                      *)
(* ------------------------------------------------------------------------- *)

let P2GK_LEVELS_G = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z.
     p2ga_hyp V U z
     ==> ?d0 rho K N0 B P yc.
           &0 < d0 /\ (!n. z n IN p2ga_dp (V n) (U n) d0) /\
           p2gb_seq (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                    (\k. rfs_vmetric (V k) (&0)) z /\
           p2gb_levels (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                       (\k. rfs_vmetric (V k) (&0)) z rho K N0 B (\j m. N0 j) P N0 yc /\
           (!j. rho j <= d0 / &2 pow j / &16) /\
           (!j k s. N0 j <= k
                    ==> yc j k s IN p2ga_dp (V k) (U k) (d0 / &2 pow j) /\
                        mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                 (rfs_vmetric (V k) (&0)) (yc j k s) (rho j) SUBSET U k) /\
           (!j k p. N0 j <= k /\
                    p IN p2ga_Y (V k) (U k) (z k) (d0 / &2 pow j) (&j + &1 / &2)
                    ==> ?s. s < P j /\
                            p IN mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                          (rfs_vmetric (V k) (&0)) (yc j k s) (rho j / &32)) /\
           (!j k s. N0 j <= k /\ N0 (SUC j) <= k
                    ==> mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                 (rfs_vmetric (V k) (&0)) (yc j k s) (rho j) SUBSET
                        {p | ?i. i < P (SUC j) /\
                                 p IN mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                               (rfs_vmetric (V k) (&0)) (yc (SUC j) k i)
                                               (rho (SUC j) / &32)})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2GA_LEVELS_RAW) THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `rho:num->real` (X_CHOOSE_THEN `K:num->real`
    (X_CHOOSE_THEN `N0:num->num` (X_CHOOSE_THEN `B:num->num->real` (X_CHOOSE_THEN `P:num->num`
    (X_CHOOSE_THEN `yc:num->num->num->A` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rho") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
    (CONJUNCTS_THEN2 (LABEL_TAC "cm") (LABEL_TAC "net"))))))))))))) THEN
  MAP_EVERY EXISTS_TAC [`d0:real`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                        `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!k. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) k) (&0)) /\
        smooth_manifold_atlas (rfs_vtop (V k) (&0)) (rfs_vatlas (V k) (&0)) /\
        riemannian_metric (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) /\
        (z:num->A) k IN topspace (rfs_vtop (V k) (&0))`
  (LABEL_TAC "sl") THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`;
                                `k:num`] P2GA_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j k s. (N0:num->num) j <= k /\ N0 (SUC j) <= k
            ==> mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) k) (&0),rfs_vatlas (V k) (&0))
                         (rfs_vmetric (V k) (&0)) ((yc:num->num->num->A) j k s) ((rho:num->real) j) SUBSET
                {p | ?i. i < (P:num->num) (SUC j) /\
                         p IN mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                       (rfs_vmetric (V k) (&0)) (yc (SUC j) k i) (rho (SUC j) / &32)}`
  (LABEL_TAC "sh32") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `q:A` THEN DISCH_TAC THEN
      USE_THEN "sl" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      SUBGOAL_THEN `&0 < d0 / &2 pow j /\ d0 / &2 pow (SUC j) = d0 / &2 pow j / &2`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < &2 pow j` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
        REWRITE_TAC[real_pow] THEN UNDISCH_TAC `&0 < &2 pow j` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `(yc:num->num->num->A) j k s IN
                    p2ga_Y (V k) (U k) ((z:num->A) k) (d0 / &2 pow j) (&j + &1)`
      ASSUME_TAC THENL
       [USE_THEN "net" (MP_TAC o C MP (ASSUME `(N0:num->num) j <= k`) o
                        SPECL [`j:num`; `k:num`]) THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(q:A) IN p2ga_Y (V k) (U k) ((z:num->A) k) (d0 / &2 pow j / &2)
                               ((&j + &1) + (rho:num->real) j)` ASSUME_TAC THENL
       [MATCH_MP_TAC P2GA_Y_SHIFT THEN EXISTS_TAC `(yc:num->num->num->A) j k s` THEN
        ASM_REWRITE_TAC[P2CO_VBALL] THEN
        USE_THEN "rho" (MP_TAC o SPEC `j:num`) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(q:A) IN p2ga_Y (V k) (U k) ((z:num->A) k) (d0 / &2 pow (SUC j))
                               (&(SUC j) + &1 / &2)` ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `p2ga_Y (V k) (U k) ((z:num->A) k) (d0 / &2 pow j / &2)
                           ((&j + &1) + (rho:num->real) j)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GA_Y_MONO THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
        USE_THEN "rho" (MP_TAC o SPEC `j:num`) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "net" (MP_TAC o C MP (ASSUME `(N0:num->num) (SUC j) <= k`) o
                      SPECL [`SUC j`; `k:num`]) THEN
      DISCH_THEN(MP_TAC o SPEC `q:A` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2gb_seq] THEN USE_THEN "sl" ACCEPT_TAC;
    REWRITE_TAC[p2gb_levels] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "rho" (MP_TAC o SPEC `j:num`) THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "bd" (MP_TAC o SPECL [`j:num`; `k:num`; `s:num`]) THEN
      ASM_SIMP_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "cm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "net" (MP_TAC o C MP (ASSUME `(N0:num->num) j <= k`) o SPECL [`j:num`; `k:num`]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:num` THEN
      USE_THEN "sl" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k`; `(U:num->A->bool) k`; `(z:num->A) k`;
                     `d0 / &2 pow j`; `&j + &1`] P2GA_Y_BALL) THEN
      ASM_REWRITE_TAC[P2CO_VBALL] THEN REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "sh32" (MP_TAC o C MP (CONJ (ASSUME `(N0:num->num) j <= k`)
                                          (ASSUME `(N0:num->num) (SUC j) <= k`)) o
                       SPECL [`j:num`; `k:num`; `s:num`]) THEN
      MATCH_MP_TAC(SET_RULE `t SUBSET u ==> s SUBSET t ==> (s:A->bool) SUBSET u`) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:A) IN s ==> x IN t`) THEN
      MATCH_MP_TAC P2CU_BALL_MONO THEN USE_THEN "rho" (MP_TAC o SPEC `SUC j`) THEN
      REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "bd" (MP_TAC o SPECL [`j:num`; `k:num`; `s:num`]) THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "net" (MP_TAC o C MP (ASSUME `(N0:num->num) j <= k`) o SPECL [`j:num`; `k:num`]) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    USE_THEN "sh32" ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The diagonal of P2CK_DIAGONAL (pc_p2c_cg) with an extra                   *)
(* per-level predicate Q and the re-indexing r made explicit: if, for each   *)
(* level j, the maps Fm j n are diffeomorphisms of W j, fix the base point   *)
(* and satisfy Q j (sq n) (Fm j n) for all large n, then the diagonal maps   *)
(* Fm k (r k) at the indices sq (r k) satisfy Q k (sq (r k)) (Fm k (r k))    *)
(* as well.  Q carries the G-specific facts (images in U, path lifting).     *)
(* ------------------------------------------------------------------------- *)

let P2GK_DIAGONAL_Q = prove
 (`!(top:num->A topology) atlas (h:num->A->real^3^3) (x:num->A) (M:(real^3)topology)
    (atlasM:((real^3->bool)#(real^3->real^3))->bool) (g:real^3->real^3^3) (xl:real^3)
    (W:num->real^3->bool) (sq:num->num) (Q:num->num->(real^3->A)->bool)
    (Fm:num->num->real^3->A).
     (!k. open_in M (W k) /\ M closure_of W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace M /\
     (!m n. m < n ==> sq m < sq n) /\
     (!j. (?N. !n. N <= n
                   ==> (?G. mfd_diffeo M atlasM (W j) (top(sq n)) (atlas(sq n))
                              (IMAGE (Fm j n) (W j)) (Fm j n) G) /\
                       Fm j n xl = x(sq n) /\ Q j (sq n) (Fm j n)) /\
          (!m eta.
             &0 < eta
             ==> ?N. !n y. N <= n /\ y IN M closure_of W j
                           ==> lck_dist2 m (metric_local atlasM (chart_at atlasM y) g)
                                 (\z. rfs_pullback (atlas(sq n))
                                        (Fm j n o chart_inv (chart_at atlasM y))
                                        (h(sq n)) z)
                                 (SND(chart_at atlasM y) y) < eta))
     ==> ?r:num->num.
           (!m n. m < n ==> r m < r n) /\
           (!k. Fm k (r k) xl = x(sq(r k))) /\
           (!k. ?psi. mfd_diffeo M atlasM (W k) (top(sq(r k))) (atlas(sq(r k)))
                        (IMAGE (Fm k (r k)) (W k)) (Fm k (r k)) psi) /\
           (!k. Q k (sq(r k)) (Fm k (r k))) /\
           (!K m eta.
              compact_in M K /\ &0 < eta
              ==> ?k0. !k. k0 <= k
                           ==> K SUBSET W k /\
                               !y. y IN K
                                   ==> lck_dist2 m (metric_local atlasM (chart_at atlasM y) g)
                                         (\z. rfs_pullback (atlas(sq(r k)))
                                                (Fm k (r k) o chart_inv (chart_at atlasM y))
                                                (h(sq(r k))) z)
                                         (SND(chart_at atlasM y) y) < eta)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ex") (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (CONJUNCTS_THEN2 (LABEL_TAC "sq") MP_TAC))) THEN
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
  EXISTS_TAC `r:num->num` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "n0" (MP_TAC o SPECL [`k:num`; `(r:num->num) k`]) THEN
    USE_THEN "rb" (MP_TAC o CONJUNCT1 o SPEC `k:num`) THEN MESON_TAC[];
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
(* The Brouwer image lemma.  A continuous map of cball(0,r)                  *)
(* moving no point by r - r' or more covers ball(0,r') by the image of       *)
(* ball(0,r) (the fixed point of w - f w + y, BROUWER_BALL).                  *)
(* ------------------------------------------------------------------------- *)

let P2GK_BROUWER_IMAGE = prove
 (`!f:real^N->real^N r r'.
     &0 < r' /\ r' < r /\ f continuous_on cball(vec 0,r) /\
     (!w. w IN cball(vec 0,r) ==> norm(f w - w) < r - r')
     ==> ball(vec 0,r') SUBSET IMAGE f (ball(vec 0,r))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near")))) THEN
  REWRITE_TAC[SUBSET; IN_BALL_0; IN_IMAGE] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w:real^N. w IN cball(vec 0,r) ==> norm((w - f w) + y) < r`
  (LABEL_TAC "lt") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "near" (MP_TAC o C MP (ASSUME `(w:real^N) IN cball(vec 0,r)`) o
                     SPEC `w:real^N`) THEN
    MP_TAC(ISPECL [`w - (f:real^N->real^N) w`; `y:real^N`] NORM_TRIANGLE) THEN
    MP_TAC(ISPECL [`w:real^N`; `(f:real^N->real^N) w`] NORM_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:real^N. (w - f w) + y`; `vec 0:real^N`; `r:real`] BROUWER_BALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_CBALL_0] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^N` THEN
  SUBGOAL_THEN `(f:real^N->real^N) w = y` ASSUME_TAC THENL
   [UNDISCH_TAC `(\w:real^N. (w - f w) + y) w = w` THEN REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(w:real^N) = (w - f w) + y` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A normal chart of the levels covers the metric balls around               *)
(* its centre up to its radius (MFD_EXP_BALL with GEON_NORMAL_PARAM).        *)
(* ------------------------------------------------------------------------- *)

let P2GK_NCH_ONTO = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k r p.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ r <= rho(NUMFST a) /\
     p IN mfd_ball (top k,atlas k) (h k) (p2cg_ctr yc k a) r
     ==> ?w. norm w < r /\ p2cg_nch top atlas h yc k a w = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GB_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o GEN_REWRITE_RULE I [p2gb_seq]) THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) yc k a`; `(rho:num->real)(NUMFST a)`]
                GEON_NORMAL_PARAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `(rho:num->real)(NUMFST a)`] MFD_EXP_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(p:A) IN IMAGE (p2cg_nch top atlas (h:num->A->real^3^3) yc k a)
                   (ball(vec 0,(rho:num->real)(NUMFST a)))`
  MP_TAC THENL
   [REWRITE_TAC[P2CE_NCH_EQ] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s t (y:A). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                         ((h:num->A->real^3^3) k) (p2cg_ctr (yc:num->num->num->A) k a) r` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GB_NCH_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(p:A) IN mfd_ball ((top:num->A topology) k,
                                  (atlas:num->((A->bool)#(A->real^3))->bool) k)
                                 ((h:num->A->real^3^3) k) (p2cg_ctr (yc:num->num->num->A) k a) r` THEN
  ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The images of the closure of W j under the level-j maps lie               *)
(* in the normal chart balls of the CG charts, hence in U when these balls   *)
(* do (as for G: P2GK_LEVELS_G).                                              *)
(* ------------------------------------------------------------------------- *)

let P2GK_NCH_IN_BALL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k w.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ norm w < rho(NUMFST a)
     ==> p2cg_nch top atlas h yc k a w IN
         mfd_ball (top k,atlas k) (h k) (p2cg_ctr yc k a) (rho(NUMFST a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GB_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GB_NCH_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o GEN_REWRITE_RULE I [p2gb_seq]) THEN
  ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  UNDISCH_TAC `p2cg_ctr (yc:num->num->num->A) k a IN
               mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                        ((h:num->A->real^3^3) k) ((x:num->A) k) (&(NUMFST a) + &1)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]);;

let P2GK_IMAGE_U = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp (U:num->A->bool) j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     (!i k s. N0 i <= k ==> mfd_ball (top k,atlas k) (h k) (yc i k s) (rho i) SUBSET U k)
     ==> ?N. !n p. N <= n /\ p IN p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j
                   ==> p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)) p IN
                       U (sq n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inU")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CE_COMPACT_EVENTUALLY THEN
  EXISTS_TAC `p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN topspace(p2cl_top (p2cg_dm (rho:num->real))
                                                 (kp:num->real^3->real^3))` MP_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)
                                 closure_of p2gc_W rho (P:num->num) kp j` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^3) IN s ==> x IN t`) THEN
    REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs (P:num->num) j`]) P2GE_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`(P:num->num) (j + 2)`; `c:num`; `z0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_COVER) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y0:real^3) IN p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)
                                 closure_of p2gc_W rho (P:num->num) kp j` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N1:num` (LABEL_TAC "im")) (K ALL_TAC))))) THEN
  EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) c) (ball(z0,r))` THEN
  EXISTS_TAC `N1 + p2cg_nv (N0:num->num) (Nn:num->num) c + N0 (NUMFST c)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`;
                          `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `p:real^3`] THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `N1 <= n /\ p2cg_nv (N0:num->num) (Nn:num->num) c <= (sq:num->num) n /\
                N0 (NUMFST c) <= sq n` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      aconv (concl th) `!n. n <= (sq:num->num) n`)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "im" (MP_TAC o C MP (CONJ (ASSUME `N1 <= n:num`)
                                      (ASSUME `(z:real^3) IN ball(z0,r)`)) o
                  SPECL [`n:num`; `z:real^3`]) THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!s t (y:A). y IN s /\ s SUBSET t ==> y IN t`) THEN
  EXISTS_TAC `mfd_ball ((top:num->A topology) ((sq:num->num) n),
                        (atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
                       ((h:num->A->real^3^3) (sq n))
                       (p2cg_ctr (yc:num->num->num->A) (sq n) c) ((rho:num->real) (NUMFST c))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`c:num`; `(sq:num->num) n`; `w:real^3`]) P2GK_NCH_IN_BALL) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p2cg_ctr] THEN USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The path-lifting step: for i < j, a level-(i+1) normal ball of radius    *)
(* rho/8 lies in the image of W i under the level-j maps for all large n    *)
(* (uniform goodness on cball(0,rho/6), margin rho/24, P2GK_BROUWER_IMAGE).  *)

let P2GK_PIECE_LIFT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i s.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ i < j /\ s < P (SUC i)
     ==> ?N. !n. N <= n
             ==> mfd_ball (top (sq n),atlas (sq n)) (h (sq n))
                          (yc (SUC i) (sq n) s) (rho (SUC i) / &8) SUBSET
                 IMAGE (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))
                       (p2gc_W rho P kp i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `a = NUMPAIR (SUC i) s` THEN
  SUBGOAL_THEN `NUMFST a = SUC i /\ NUMSND a = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[NUMPAIR_DEST]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rho:num->real) (SUC i)` (LABEL_TAC "rp") THENL
   [MP_TAC(ISPECL (p2cg_std @ [`SUC i`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the closed ball of radius rho/6 is mapped into W i, inside the domain *)
  SUBGOAL_THEN
   `!z. z IN cball(vec 0,(rho:num->real) (SUC i) / &6)
        ==> z IN p2cg_dm rho a /\ (kp:num->real^3->real^3) a z IN p2gc_W rho P kp i`
  (LABEL_TAC "inW") THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN CONJ_TAC THENL
     [USE_THEN "rp" MP_TAC THEN UNDISCH_TAC `norm(z:real^3) <= (rho:num->real) (SUC i) / &6` THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[p2gc_W; IN_UNIONS; EXISTS_IN_GSPEC] THEN EXISTS_TAC `s:num` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_BALL_0] THEN USE_THEN "rp" MP_TAC THEN
      UNDISCH_TAC `norm(z:real^3) <= (rho:num->real) (SUC i) / &6` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* goodness of the level-j maps at every point of the closed ball *)
  SUBGOAL_THEN
   `!z. z IN cball(vec 0,(rho:num->real) (SUC i) / &6)
        ==> p2ce_good top atlas (h:num->A->real^3^3) yc rho (kp:num->real^3->real^3) sq
              (\n. p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) a z`
  (LABEL_TAC "gd") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "inW" (MP_TAC o C MP (ASSUME `(z:real^3) IN cball(vec 0,(rho:num->real) (SUC i) / &6)`) o
                    SPEC `z:real^3`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs (P:num->num) j`]) P2GE_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_COVER) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!t. (y:real^3) IN t ==> t SUBSET u ==> y IN u`) THEN
    MATCH_MP_TAC(SET_RULE `!s. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `p2gc_W (rho:num->real) (P:num->num) (kp:num->real^3->real^3) j` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `!m n. m <= n ==> p2gc_W (rho:num->real) (P:num->num)
                                       (kp:num->real^3->real^3) m SUBSET p2gc_W rho P kp n`
      MP_TAC THENL
       [MATCH_MP_TAC P2B_EXHAUST_MONO THEN X_GEN_TAC `k:num` THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) closure_of
                    p2gc_W rho (P:num->num) kp k` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
        MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(kp:num->real^3->real^3) a z IN p2gc_W (rho:num->real) (P:num->num) kp i` THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                        (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                                        (P(j + 2))`;
                             `a:num`; `cball(vec 0:real^3,(rho:num->real) (SUC i) / &6)`])
                P2GE_GOOD_UNIFORM) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "cl"))))) THEN
  USE_THEN "cl" (MP_TAC o SPEC `(rho:num->real) (SUC i) / &24`) THEN
  ANTS_TAC THENL [USE_THEN "rp" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "c2")) THEN
  EXISTS_TAC `N1 + N2 + p2cg_nv (N0:num->num) (Nn:num->num) a` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ N2 <= n /\ p2cg_nv (N0:num->num) (Nn:num->num) a <= (sq:num->num) n`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      aconv (concl th) `!n. n <= (sq:num->num) n`)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ball(vec 0,(rho:num->real) (SUC i) / &8) SUBSET
    IMAGE (\w. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho ((sq:num->num) n) a
                 (p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2)) (kp a w)))
          (ball(vec 0,rho (SUC i) / &6))`
  (LABEL_TAC "br") THENL
   [MATCH_MP_TAC P2GK_BROUWER_IMAGE THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rp" MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "rp" MP_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o CONJUNCT1 o CONJUNCT2 o
                 CONJUNCT2) THEN
      SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "c2" (MP_TAC o SPECL [`n:num`; `w:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `(sq:num->num) n`; `(rho:num->real) (SUC i) / &8`;
                             `q:A`]) P2GK_NCH_ONTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2cg_ctr] THEN USE_THEN "rp" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "br" (MP_TAC o SPEC `y:real^3` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_BALL_0; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(kp:num->real^3->real^3) a w` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(w:real^3) IN cball(vec 0,(rho:num->real) (SUC i) / &6)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL_0] THEN
      UNDISCH_TAC `norm(w:real^3) < (rho:num->real) (SUC i) / &6` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2)) ((kp:num->real^3->real^3) a w)` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    USE_THEN "inW" (MP_TAC o SPEC `w:real^3`) THEN REWRITE_TAC[IN_CBALL_0] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `norm(w:real^3) < (rho:num->real) (SUC i) / &6` THEN REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The per-level predicate of the G diagonal: for the level-j               *)
(* maps, the image of W j lies in U, and every level-(i+1) normal ball of    *)
(* radius rho/8 with i < j lies in the image of W i, for all large n.        *)
(* ------------------------------------------------------------------------- *)

(* Finitely many eventual properties hold together eventually. *)

let P2GK_EVENTUALLY_FINITE = prove
 (`!(R:num->num->num->bool) j (P:num->num).
     (!i s. i < j /\ s < P (SUC i) ==> ?N. !n. N <= n ==> R i s n)
     ==> ?N. !n. N <= n ==> !i s. i < j /\ s < P (SUC i) ==> R i s n`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:num->num->num` (LABEL_TAC "nn")) THEN
  SUBGOAL_THEN `!i. ?b. !s. s < (P:num->num) (SUC i) ==> (NN:num->num->num) i s <= b`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`(NN:num->num->num) i`; `{s:num | s < (P:num->num) (SUC i)}`]
                  UPPER_BOUND_FINITE_SET) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `b:num->num` (LABEL_TAC "b")) THEN
  MP_TAC(ISPECL [`b:num->num`; `{i:num | i < j}`] UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "a")) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `s:num`] THEN STRIP_TAC THEN
  USE_THEN "nn" (MP_TAC o SPECL [`i:num`; `s:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(b:num->num) i` THEN CONJ_TAC THENL
   [USE_THEN "b" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "a" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let p2gk_Q = new_definition
 `p2gk_Q (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
         (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real) (P:num->num)
         (kp:num->real^3->real^3) (U:num->A->bool) j k (Fm:real^3->A) <=>
    IMAGE Fm (p2gc_W rho P kp j) SUBSET U k /\
    (!i s. i < j /\ s < P (SUC i)
           ==> mfd_ball (top k,atlas k) (h k) (yc (SUC i) k s) (rho (SUC i) / &8) SUBSET
               IMAGE Fm (p2gc_W rho P kp i))`;;

let P2GK_LEVEL_Q = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp (U:num->A->bool) j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     (!i k s. N0 i <= k ==> mfd_ball (top k,atlas k) (h k) (yc i k s) (rho i) SUBSET U k)
     ==> ?N. !n. N <= n
             ==> p2gk_Q top atlas h yc rho P kp U j (sq n)
                   (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2ce_std @ [`U:num->A->bool`; `j:num`]) P2GK_IMAGE_U) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "u")) THEN
  MP_TAC(ISPECL [`\i s n. mfd_ball ((top:num->A topology) ((sq:num->num) n),
                                    (atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
                                   ((h:num->A->real^3^3) (sq n))
                                   ((yc:num->num->num->A) (SUC i) (sq n) s)
                                   ((rho:num->real) (SUC i) / &8) SUBSET
                          IMAGE (p2ce_F top atlas h yc rho (kp:num->real^3->real^3)
                                   (p2ce_cs (P:num->num) j) (sq n) (P(j + 2)))
                                (p2gc_W rho P kp i)`;
                 `j:num`; `P:num->num`] P2GK_EVENTUALLY_FINITE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `s:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2GK_PIECE_LIFT THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `K:num->real`; `N0:num->num`; `B:num->num->real`;
                          `NB:num->num->num`; `Nn:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                          `Gl:num->real^3->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "l")) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[p2gk_Q] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    USE_THEN "u" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t (y:real^3). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `p2gc_W (rho:num->real) (P:num->num) (kp:num->real^3->real^3) j` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN SIMP_TAC[];
    USE_THEN "l" MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The space part of G (everything but the flow clause) as a                 *)
(* predicate, and its derivation from the output of the diagonal with the    *)
(* per-level predicate (images in U and the ball lifts) and the covering of  *)
(* the level regions (path lifting through P2GA_CURVE_IN_Y).                  *)
(* ------------------------------------------------------------------------- *)

let p2gk_space = new_definition
 `p2gk_space (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3))
             (U:num->A->bool) (z:num->A) (sub:num->num) (top:(real^3)topology)
             (atlas:((real^3->bool)#(real^3->real^3))->bool) (g:real^3->real^3^3)
             (zl:real^3) (W:num->real^3->bool) (phi:num->real^3->A) <=>
    p3_subseq sub /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ zl IN topspace top /\
    (!k. open_in top (W k) /\ zl IN W k /\ compact_in top (top closure_of W k) /\
         top closure_of W k SUBSET W (SUC k)) /\
    UNIONS {W k | k IN (:num)} = topspace top /\
    (!k. phi k zl = z (sub k)) /\
    (!k. IMAGE (phi k) (W k) SUBSET U (sub k) /\
         ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V (sub k)) (&0))
                          (rfs_vatlas (V (sub k)) (&0))
                          (IMAGE (phi k) (W k)) (phi k) psi) /\
    (!K m eta. compact_in top K /\ &0 < eta
               ==> ?k0. !k. k0 <= k
                            ==> K SUBSET W k /\
                                !y. y IN K
                                    ==> lck_dist2 m
                                          (metric_local atlas (chart_at atlas y) g)
                                          (rfs_pullback (rfs_vatlas (V (sub k)) (&0))
                                             (phi k o chart_inv (chart_at atlas y))
                                             (rfs_vmetric (V (sub k)) (&0)))
                                          (SND(chart_at atlas y) y) < eta) /\
    (!delta A. &0 < delta /\ &0 < A
               ==> ?m k0. m <= k0 /\
                    !k gamma.
                      k0 <= k /\
                      mfd_c1_curve (rfs_vtop (V (sub k)) (&0),
                                    rfs_vatlas (V (sub k)) (&0)) gamma (&0) (&1) /\
                      gamma (&0) = z (sub k) /\
                      mfd_length (rfs_vatlas (V (sub k)) (&0))
                                 (rfs_vmetric (V (sub k)) (&0)) gamma (&0) (&1) <= A /\
                      (!s. &0 <= s /\ s <= &1
                           ==> p2b_lc_deep (V (sub k)) (U (sub k)) (gamma s) delta)
                      ==> !s. &0 <= s /\ s <= &1
                              ==> ?y'. y' IN W m /\ phi k y' = gamma s)`;;

(* A level index for given depth and length. *)

let P2GK_LEVEL_FOR = prove
 (`!d0 delta A. &0 < d0 /\ &0 < delta
                ==> ?i. d0 / &2 pow (SUC i) <= delta /\ A < &(SUC i) + &1 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inv(&2)`; `delta / d0`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
  MP_TAC(SPEC `A:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `n2:num`) THEN
  EXISTS_TAC `n1 + n2:num` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_POW_INV] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC(REAL_ARITH `!y. x <= y /\ y < z ==> x <= z`) THEN
    EXISTS_TAC `inv(&2) pow n1 * d0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC;
      UNDISCH_TAC `inv(&2) pow n1 < delta / d0` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]];
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `A <= &n2` THEN REAL_ARITH_TAC]);;

let P2GK_SPACE_FROM_DIAG = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d0 (rho:num->real) (P:num->num) (yc:num->num->num->A) (N0:num->num)
    (M:(real^3)topology) atlasM g zl (W:num->real^3->bool) (sub:num->num)
    (phi:num->real^3->A).
     p2ga_hyp V U z /\ &0 < d0 /\
     (!j k p. N0 j <= k /\ p IN p2ga_Y (V k) (U k) (z k) (d0 / &2 pow j) (&j + &1 / &2)
              ==> ?s. s < P j /\
                      p IN mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                    (rfs_vmetric (V k) (&0)) (yc j k s) (rho j / &8)) /\
     hausdorff_space M /\ smooth_manifold_atlas M atlasM /\ riemannian_metric atlasM g /\
     zl IN topspace M /\
     (!k. open_in M (W k) /\ zl IN W k /\ compact_in M (M closure_of W k) /\
          M closure_of W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace M /\
     (!m n. m < n ==> sub m < sub n) /\
     (!k. phi k zl = z (sub k)) /\
     (!k. ?psi. mfd_diffeo M atlasM (W k) (rfs_vtop (V (sub k)) (&0))
                          (rfs_vatlas (V (sub k)) (&0))
                          (IMAGE (phi k) (W k)) (phi k) psi) /\
     (!k. IMAGE (phi k) (W k) SUBSET U (sub k) /\
          !i s. i < k /\ s < P (SUC i)
                ==> mfd_ball (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0))
                             (rfs_vmetric (V (sub k)) (&0)) (yc (SUC i) (sub k) s)
                             (rho (SUC i) / &8) SUBSET
                    IMAGE (phi k) (W i)) /\
     (!K m eta. compact_in M K /\ &0 < eta
                ==> ?k0. !k. k0 <= k
                             ==> K SUBSET W k /\
                                 !y. y IN K
                                     ==> lck_dist2 m
                                           (metric_local atlasM (chart_at atlasM y) g)
                                           (\z. rfs_pullback (rfs_vatlas (V (sub k)) (&0))
                                                  (phi k o chart_inv (chart_at atlasM y))
                                                  (rfs_vmetric (V (sub k)) (&0)) z)
                                           (SND(chart_at atlasM y) y) < eta)
     ==> p2gk_space V U z sub M atlasM g zl W phi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hyp") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ycov") MP_TAC))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[ETA_AX] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[p2gk_space; p3_subseq] THEN
  MAP_EVERY X_GEN_TAC [`delta:real`; `A:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d0:real`; `delta:real`; `A:real`] P2GK_LEVEL_FOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `SUC i + (N0:num->num) (SUC i)`] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `gamma:real->A`] THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `k <= (sub:num->num) k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "hyp" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2ga_hyp]) THEN
  DISCH_THEN(MP_TAC o SPEC `(sub:num->num) k`) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2c_regular_view] o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(gamma:real->A) (&0)` THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) ((sub:num->num) k)`;
                 `(U:num->A->bool) ((sub:num->num) k)`; `(z:num->A) ((sub:num->num) k)`; `gamma:real->A`;
                 `delta:real`; `A:real`; `d0 / &2 pow (SUC i)`; `&(SUC i) + &1 / &2`]
                P2GA_CURVE_IN_Y) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "ycov" (MP_TAC o SPECL [`SUC i`; `(sub:num->num) k`;
                                   `(gamma:real->A) s`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> t = `U:num->A->bool`)) (concl th) && is_forall (concl th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `s':num`] o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `(gamma:real->A) s`) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The level-up lemma for the finer G nets (radius rho/32):                  *)
(* copies of P2GC_NET_COVER and P2GC_LEVEL_UP with the shift clause of       *)
(* P2GK_LEVELS_G at radius rho/32 as a hypothesis.                           *)
(* ------------------------------------------------------------------------- *)

let P2GK_NET_COVER32 = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D b z.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     (!j k s. Nn j <= k /\ Nn (SUC j) <= k
              ==> mfd_ball (top k,atlas k) (h k) (yc j k s) (rho j) SUBSET
                  {p | ?i. i < P (SUC j) /\
                           p IN mfd_ball (top k,atlas k) (h k) (yc (SUC j) k i)
                                         (rho (SUC j) / &32)}) /\
     p2cg_dsys top atlas h yc rho s D /\ z IN cball(vec 0,rho(NUMFST b) / &2)
     ==> ?i. i < P (SUC (NUMFST b)) /\
             p2cg_dv D (NUMPAIR (SUC (NUMFST b)) i) (vec 0) b z <= rho (SUC (NUMFST b)) / &32`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `j = NUMFST b` THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  FIRST_ASSUM(LABEL_TAC "big" o MATCH_MP MONOTONE_BIGGER) THEN
  SUBGOAL_THEN `&0 < (rho:num->real) j /\ rho j < &1 /\ &0 < rho (SUC j) /\ rho (SUC j) < &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`j:num`]) P2GB_RHO_POS) THEN
    MP_TAC(ISPECL (p2cg_std @ [`SUC j`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^3) < (rho:num->real) j` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN cball(vec 0,(rho:num->real) j / &2)` THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. p2cg_nv (N0:num->num) (Nn:num->num) b + N0 (SUC j) + Nn (SUC j) <= n
        ==> ?i. i < (P:num->num) (SUC j) /\
                p2cg_dk (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3)
                  (yc:num->num->num->A) ((s:num->num) n) (NUMPAIR (SUC j) i) (vec 0) b z <
                (rho:num->real) (SUC j) / &32`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ABBREV_TAC `k = (s:num->num) n` THEN
    SUBGOAL_THEN `p2cg_nv (N0:num->num) (Nn:num->num) b <= k /\ N0 (SUC j) + Nn (SUC j) <= k`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o GEN_REWRITE_RULE I [p2gb_seq]) THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2GB_NCH_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c0") (LABEL_TAC "nb")) THEN
    USE_THEN "nb" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "nb" (MP_TAC o SPEC `vec 0:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_0]; ALL_TAC] THEN
    USE_THEN "c0" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A) k b z IN
      mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
               ((h:num->A->real^3^3) k) ((yc:num->num->num->A) j k (NUMSND b)) ((rho:num->real) j)`
    ASSUME_TAC THENL
     [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      SUBGOAL_THEN `p2cg_ctr (yc:num->num->num->A) k b = yc j k (NUMSND b)` (SUBST1_TAC o SYM) THENL
       [ASM_REWRITE_TAC[p2cg_ctr]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`; `NUMSND b`] o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&32`)) (concl th))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `p2cg_nv (N0:num->num) (Nn:num->num) b <= k` THEN
      ASM_REWRITE_TAC[p2cg_nv] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p2cg_nch (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3)
                                (yc:num->num->num->A) k b z`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR (SUC j) i`; `k:num`]) P2GB_NCH_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[p2cg_dk] THEN
    UNDISCH_TAC `p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3)
                   (yc:num->num->num->A) k b z IN
                 mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                          ((h:num->A->real^3^3) k) (yc (SUC j) k i) ((rho:num->real) (SUC j) / &32)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM; p2cg_ctr; NUMPAIR_DEST] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2CC_PIGEONHOLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "freq")) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `NUMPAIR (SUC j) i`; `b:num`;
                 `vec 0:real^3`; `z:real^3`] P2CG_D_SEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NUMPAIR_DEST; CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1) (NUMPAIR (SUC j) i) (vec 0) b z - (rho:num->real) (SUC j) / &32`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
  USE_THEN "freq" (MP_TAC o SPEC `N2:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "n2" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  UNDISCH_TAC `p2cg_dk (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3)
                 (yc:num->num->num->A) ((s:num->num) n) (NUMPAIR (SUC j) i) (vec 0) b z <
               (rho:num->real) (SUC j) / &32` THEN
  REAL_ARITH_TAC);;

(* A point of a chart at level j is a point of a level-(j+1) chart near its *)
(* centre.                                                                    *)

let P2GK_LEVEL_UP32 = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (kp:num->real^3->real^3) b z.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     (!j k s. Nn j <= k /\ Nn (SUC j) <= k
              ==> mfd_ball (top k,atlas k) (h k) (yc j k s) (rho j) SUBSET
                  {p | ?i. i < P (SUC j) /\
                           p IN mfd_ball (top k,atlas k) (h k) (yc (SUC j) k i)
                                         (rho (SUC j) / &32)}) /\
     p2cg_dsys top atlas h yc rho s D /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     z IN p2cg_dm rho b
     ==> ?i w. i < P (SUC (NUMFST b)) /\ norm w <= rho (SUC (NUMFST b)) / &32 /\
               kp b z = kp (NUMPAIR (SUC (NUMFST b)) i) w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o REWRITE_RULE[p2cg_dm] o
              check (fun th -> concl th = `(z:real^3) IN p2cg_dm (rho:num->real) b`)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `z:real^3`]) P2GK_NET_COVER32) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `j = SUC(NUMFST b)` THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR j i`]) P2GB_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `NUMPAIR j i`; `vec 0:real^3`; `b:num`; `z:real^3`]) P2GB_DV_SYM) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i)` ASSUME_TAC THENL
   [REWRITE_TAC[P2CG_IN_OM; NUMPAIR_DEST; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `NUMPAIR j i`; `z:real^3`]) P2GB_TR_PROPS) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN STRIP_TAC THEN
  EXISTS_TAC `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i) z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1) b z (NUMPAIR j i) (vec 0)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2GB_DV_ZERO_NORM THEN
    MAP_EVERY EXISTS_TAC (p2cg_std @ [`s:num->num`]) THEN
    ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
    UNDISCH_TAC `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i) z IN ball(vec 0,rho j / &4)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o SPECL [`b:num`; `NUMPAIR j i`; `z:real^3`;
                                `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i) z`] o
                GEN_REWRITE_RULE I [p2cl_glue]) THEN
    ASM_REWRITE_TAC[p2cg_dm; NUMPAIR_DEST]]);;

(* ------------------------------------------------------------------------- *)
(* Near-identity of the level-j maps in the CG charts of level               *)
(* at most j+1: images in the normal chart, smoothness on ball(0,rho/6), and *)
(* all partials of order at most j within 1/(j+1) of those of the identity  *)
(* on cball(0,rho/7), for all large n (uniform goodness, P2CI_NEAR_PARTIAL,  *)
(* compactness).  Along the final diagonal this gives near-identity of the   *)
(* maps phi k in every fixed chart.                                          *)
(* ------------------------------------------------------------------------- *)

let P2GK_ITER_NEAR = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f l.
     p2ci_near z0 Fs f /\ ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
     ==> p2ci_near z0 (\n. iterated_partial l (Fs n)) (iterated_partial l f)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[iterated_partial; ALL; ETA_AX] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_PARTIAL THEN ASM_SIMP_TAC[]);;

let P2GK_PARTIALS_COMPACT = prove
 (`!(K:real^M->bool) (Fs:num->real^M->real^N) f l e.
     compact K /\ (!z. z IN K ==> p2ci_near z Fs f) /\
     ALL (\j. 1 <= j /\ j <= dimindex(:M)) l /\ &0 < e
     ==> ?N. !n y. N <= n /\ y IN K
                   ==> norm(iterated_partial l (Fs n) y - iterated_partial l f y) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^M->bool`; `\n. iterated_partial l ((Fs:num->real^M->real^N) n)`;
                 `iterated_partial l (f:real^M->real^N)`] P2CI_NEAR_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2GK_ITER_NEAR THEN ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[]]);;

(* Finitely many eventual properties over charts i <= m, s < Q i. *)

let P2GK_EVENTUALLY_CHARTS = prove
 (`!(R:num->num->num->bool) m (Q:num->num).
     (!i s. i <= m /\ s < Q i ==> ?N. !n. N <= n ==> R i s n)
     ==> ?N. !n. N <= n ==> !i s. i <= m /\ s < Q i ==> R i s n`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:num->num->num` (LABEL_TAC "nn")) THEN
  SUBGOAL_THEN `!i. ?b. !s. s < (Q:num->num) i ==> (NN:num->num->num) i s <= b`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`(NN:num->num->num) i`; `{s:num | s < (Q:num->num) i}`]
                  UPPER_BOUND_FINITE_SET) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `b:num->num` (LABEL_TAC "b")) THEN
  MP_TAC(ISPECL [`b:num->num`; `{i:num | i <= m}`] UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[FINITE_NUMSEG_LE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "a")) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `s:num`] THEN STRIP_TAC THEN
  USE_THEN "nn" (MP_TAC o SPECL [`i:num`; `s:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(b:num->num) i` THEN CONJ_TAC THENL
   [USE_THEN "b" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "a" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let p2gk_near3 = new_definition
 `p2gk_near3 (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
             (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real) (P:num->num)
             (kp:num->real^3->real^3) j k (Fm:real^3->A) <=>
    !i s. i <= SUC j /\ s < P i
          ==> (!w. w IN ball(vec 0,rho i / &6)
                   ==> Fm (kp (NUMPAIR i s) w) IN
                       IMAGE (p2cg_nch top atlas h yc k (NUMPAIR i s)) (ball(vec 0,rho i))) /\
              smooth_map_on (ball(vec 0,rho i / &6))
                (\w. p2ce_L top atlas h yc rho k (NUMPAIR i s) (Fm (kp (NUMPAIR i s) w))) /\
              !l w. ALL (\q. 1 <= q /\ q <= 3) l /\ LENGTH l <= j /\
                    w IN cball(vec 0,rho i / &7)
                    ==> norm(iterated_partial l
                               (\w. p2ce_L top atlas h yc rho k (NUMPAIR i s)
                                           (Fm (kp (NUMPAIR i s) w))) w -
                             iterated_partial l (\w:real^3. w) w) < inv(&j + &1)`;;

(* The pieces of the charts of level at most j+1 lie in W j. *)

let P2GK_CHART_IN_W = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i s z.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     i <= SUC j /\ s < P i /\ z IN ball(vec 0,rho i / &5)
     ==> kp (NUMPAIR i s) z IN p2gc_W rho P kp j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> p2gc_W (rho:num->real) (P:num->num)
                                    (kp:num->real^3->real^3) m SUBSET p2gc_W rho P kp n`
  (LABEL_TAC "mono") THENL
   [MATCH_MP_TAC P2B_EXHAUST_MONO THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) closure_of
                p2gc_W rho (P:num->num) kp k` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`i:num`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i = SUC j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[p2gc_W; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `NUMPAIR i s`; `z:real^3`])
                P2GC_LEVEL_UP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2cg_dm; NUMPAIR_DEST] THEN
    UNDISCH_TAC `(z:real^3) IN ball(vec 0,(rho:num->real) i / &5)` THEN
    REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `&0 < (rho:num->real) i` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(X_CHOOSE_THEN `i':num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!s t (y:real^3). y IN s /\ s SUBSET t ==> y IN t`) THEN
  EXISTS_TAC `p2gc_W (rho:num->real) (P:num->num) (kp:num->real^3->real^3) i` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2gc_W; IN_UNIONS; EXISTS_IN_GSPEC] THEN EXISTS_TAC `i':num` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0] THEN
    MP_TAC(ISPECL (p2cg_std @ [`SUC i`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm(w:real^3) <= (rho:num->real) (SUC i) / &8` THEN REAL_ARITH_TAC;
    USE_THEN "mono" MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let P2GK_LEVEL_NEAR3 = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> ?N. !n. N <= n
             ==> p2gk_near3 top atlas h yc rho P kp j (sq n)
                   (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  REWRITE_TAC[p2gk_near3] THEN MATCH_MP_TAC P2GK_EVENTUALLY_CHARTS THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `s:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`i:num`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* goodness on the closed ball of radius rho/6 *)
  SUBGOAL_THEN
   `!z. z IN cball(vec 0,(rho:num->real) i / &6)
        ==> p2ce_good top atlas (h:num->A->real^3^3) yc rho (kp:num->real^3->real^3) sq
              (\n. p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) (NUMPAIR i s) z`
  (LABEL_TAC "gd") THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs (P:num->num) j`]) P2GE_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[p2cg_dm; NUMPAIR_DEST; IN_BALL_0] THEN
      UNDISCH_TAC `&0 < (rho:num->real) i` THEN
      UNDISCH_TAC `norm(z:real^3) <= (rho:num->real) i / &6` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_COVER) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!t. (y:real^3) IN t ==> t SUBSET u ==> y IN u`) THEN
    MATCH_MP_TAC(SET_RULE `!s. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `p2gc_W (rho:num->real) (P:num->num) (kp:num->real^3->real^3) j` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2GK_CHART_IN_W THEN
      MAP_EVERY EXISTS_TAC [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
        `h:num->A->real^3^3`; `x:num->A`; `K:num->real`; `N0:num->num`; `B:num->num->real`;
        `NB:num->num->num`; `Nn:num->num`; `yc:num->num->num->A`; `sq:num->num`;
        `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[IN_BALL_0] THEN
      UNDISCH_TAC `&0 < (rho:num->real) i` THEN
      UNDISCH_TAC `norm(z:real^3) <= (rho:num->real) i / &6` THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1 o CONJUNCT2) THEN STRIP_TAC THEN
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                        (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                                        (P(j + 2))`;
                             `NUMPAIR i s`; `cball(vec 0:real^3,(rho:num->real) i / &6)`])
                P2GE_GOOD_UNIFORM) THEN
  REWRITE_TAC[NUMPAIR_DEST] THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc") (K ALL_TAC))))) THEN
  (* the partials on cball(0,rho/7) *)
  SUBGOAL_THEN
   `?N2. !n. N2 <= n
             ==> !l w. ALL (\q. 1 <= q /\ q <= 3) l /\ LENGTH l <= j /\
                       w IN cball(vec 0,(rho:num->real) i / &7)
                       ==> norm(iterated_partial l
                                  (\w. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3)
                                         yc rho ((sq:num->num) n) (NUMPAIR i s)
                                         (p2ce_F top atlas h yc rho (kp:num->real^3->real^3)
                                            (p2ce_cs P j) (sq n) (P(j + 2)) (kp (NUMPAIR i s) w))) w -
                                iterated_partial l (\w:real^3. w) w) < inv(&j + &1)`
  (X_CHOOSE_THEN `N2:num` (LABEL_TAC "pt")) THENL
   [SUBGOAL_THEN
     `!l. ALL (\q. 1 <= q /\ q <= 3) l /\ LENGTH l <= j
          ==> ?N. !n w. N <= n /\ w IN cball(vec 0,(rho:num->real) i / &7)
                        ==> norm(iterated_partial l
                                   (\w. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3)
                                  yc rho ((sq:num->num) n) (NUMPAIR i s)
                                  (p2ce_F top atlas h yc rho (kp:num->real^3->real^3)
                                     (p2ce_cs P j) (sq n) (P(j + 2)) (kp (NUMPAIR i s) w))) w -
                                 iterated_partial l (\w:real^3. w) w) < inv(&j + &1)`
    MP_TAC THENL
     [X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`cball(vec 0:real^3,(rho:num->real) i / &7)`;
        `\n w. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3)
                                  yc rho ((sq:num->num) n) (NUMPAIR i s)
                                  (p2ce_F top atlas h yc rho (kp:num->real^3->real^3)
                                     (p2ce_cs P j) (sq n) (P(j + 2)) (kp (NUMPAIR i s) w))`;
        `\w:real^3. w`; `l:num list`; `inv(&j + &1)`] P2GK_PARTIALS_COMPACT) THEN
      REWRITE_TAC[DIMINDEX_3; COMPACT_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &j + &1`] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "gd" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN cball(vec 0,(rho:num->real) i / &7)` THEN
        REWRITE_TAC[IN_CBALL_0] THEN UNDISCH_TAC `&0 < (rho:num->real) i` THEN REAL_ARITH_TAC;
        REWRITE_TAC[p2ce_good] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `NL:num list->num` (LABEL_TAC "nl")) THEN
    MP_TAC(ISPECL [`NL:num list->num`;
                   `{l:num list | ALL (\q. 1 <= q /\ q <= 3) l /\ LENGTH l <= j}`]
                  UPPER_BOUND_FINITE_SET) THEN
    REWRITE_TAC[PDE_MULTI_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "ub")) THEN
    EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `w:real^3`] THEN STRIP_TAC THEN
    USE_THEN "nl" (MP_TAC o SPEC `l:num list`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `M:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3) IN ball(vec 0,(rho:num->real) i / &6)` THEN
      REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_BALL] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN EXISTS_TAC `ball(w:real^3,lam)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    USE_THEN "loc" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3) IN ball(vec 0,(rho:num->real) i / &6)` THEN
      REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      SIMP_TAC[]];
    USE_THEN "pt" MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Small pieces.  A chart piece kp_a(ball(0,rho_a/6)) around                 *)
(* a point p (with p = kp_a w, abs w <= rho_a/32) lies in any open set X     *)
(* containing p once rho_a is small (the limit metric is at most twice the  *)
(* Euclidean metric in the CG charts, so segments are short).                *)
(* ------------------------------------------------------------------------- *)

let P2GK_SMALL_PIECE_IN = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3)
    X p.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     open_in (p2cl_top (p2cg_dm rho) kp) X /\ p IN X
     ==> ?e. &0 < e /\
             !a w. w IN cball(vec 0,rho(NUMFST a) / &32) /\ kp a w = p /\ rho(NUMFST a) < e
                   ==> IMAGE (kp a) (ball(vec 0,rho(NUMFST a) / &6)) SUBSET X`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_metric (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) Gl`;
                 `X:real^3->bool`; `p:real^3`] MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` (LABEL_TAC "br")) THEN
  EXISTS_TAC `r:real` THEN USE_THEN "br" (fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `w:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (rho:num->real) (NUMFST a)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_atlas")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_local")) (concl th)))) THEN
  USE_THEN "br" (MATCH_MP_TAC o REWRITE_RULE[SUBSET] o CONJUNCT2) THEN
  SUBGOAL_THEN `ball(vec 0:real^3,(rho:num->real)(NUMFST a) / &6) SUBSET p2cg_dm rho a /\
                (w:real^3) IN ball(vec 0,rho(NUMFST a) / &6)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_dm; SUBSET; IN_BALL_0] THEN
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,(rho:num->real)(NUMFST a) / &32)` THEN
    REWRITE_TAC[IN_CBALL_0] THEN UNDISCH_TAC `&0 < (rho:num->real) (NUMFST a)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ball(vec 0:real^3,(rho:num->real)(NUMFST a) / &6) SUBSET
    IMAGE (SND(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) a))
          (FST(p2cl_chart (p2cg_dm rho) kp a))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `(kp:num->real^3->real^3) a y` THEN
    SUBGOAL_THEN `(y:real^3) IN p2cg_dm (rho:num->real) a` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[w:real^3,z] SUBSET ball(vec 0,(rho:num->real)(NUMFST a) / &6)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_BALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `FST(p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) a)`;
                 `SND(p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) a)`;
                 `w:real^3`; `z:real^3`] GRGD_CHART_SEGMENT) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_metric (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) Gl`;
                 `FST(p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) a)`;
                 `SND(p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) a)`;
                 `w:real^3`; `z:real^3`; `inv(&2)`; `&2`;
                 `ball(vec 0:real^3,(rho:num->real)(NUMFST a) / &6)`]
                GRGD_SEGMENT_LENGTH_UPPER) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [X_GEN_TAC `y:real^3` THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN p2cg_dm (rho:num->real) a` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_local (p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))
                    (p2cl_chart (p2cg_dm rho) kp a) (p2cl_metric (p2cg_dm rho) kp Gl) y =
                  Gl a y` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_local")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_metric")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `inv(&2)`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `v:real^3`] o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball(vec 0,(rho:num->real)(NUMFST a) / &6)` THEN
      REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `&0 < (rho:num->real) (NUMFST a)` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) a)
              (w + &0 % (z - w)) = p /\
    chart_inv (p2cl_chart (p2cg_dm rho) kp a) (w + &1 % (z - w)) = kp a z`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `w + &0 % (z - w) = w /\ w + &1 % (z - w) = z:real^3`] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `(kp:num->real^3->real^3) a w = p`)) THEN
    CONJ_TAC THEN MATCH_MP_TAC P2CL_CHART_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`;
                          `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN
    EXISTS_TAC `\t. chart_inv (p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) a)
                              (w + t % (z - w))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_metric (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) Gl`;
                 `\t. chart_inv (p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) a)
                                (w + t % (z - w))`;
                 `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dist(w:real^3,z) <= (rho:num->real)(NUMFST a) / &32 + rho(NUMFST a) / &6`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN cball(vec 0,(rho:num->real)(NUMFST a) / &32)` THEN
    UNDISCH_TAC `(z:real^3) IN ball(vec 0,(rho:num->real)(NUMFST a) / &6)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) <= &3 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * dist(w:real^3,z) <=
                &3 / &2 * ((rho:num->real)(NUMFST a) / &32 + rho(NUMFST a) / &6)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[DIST_POS_LE] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(rho:num->real)(NUMFST a) < r` THEN
  UNDISCH_TAC `&0 < (rho:num->real) (NUMFST a)` THEN
  UNDISCH_TAC `sqrt(&2) * dist(w:real^3,z) <=
               &3 / &2 * ((rho:num->real)(NUMFST a) / &32 + rho(NUMFST a) / &6)` THEN
  UNDISCH_TAC `mfd_length (p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))
                 (p2cl_metric (p2cg_dm rho) kp Gl)
                 (\t. chart_inv (p2cl_chart (p2cg_dm rho) kp a) (w + t % (z - w))) (&0) (&1) <=
               sqrt (&2) * dist(w,z)` THEN
  REAL_ARITH_TAC);;

(* Every point of the limit has coordinates of size at most rho/32 in CG     *)
(* charts of every deeper level (repeated P2GK_LEVEL_UP32).                   *)

let P2GK_DEEP_CHART_AT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3) p.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     (!j k s. Nn j <= k /\ Nn (SUC j) <= k
              ==> mfd_ball (top k,atlas k) (h k) (yc j k s) (rho j) SUBSET
                  {p | ?i. i < P (SUC j) /\
                           p IN mfd_ball (top k,atlas k) (h k) (yc (SUC j) k i)
                                         (rho (SUC j) / &32)}) /\
     p IN topspace(p2cl_top (p2cg_dm rho) kp)
     ==> !m. ?a w. m <= NUMFST a /\ NUMSND a < P (NUMFST a) /\
                   w IN cball(vec 0,rho(NUMFST a) / &32) /\ kp a w = p`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sh")
    ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  SUBGOAL_THEN
   `!b z. z IN p2cg_dm (rho:num->real) b
          ==> ?i w. i < (P:num->num) (SUC (NUMFST b)) /\
                    w IN cball(vec 0,rho (SUC (NUMFST b)) / &32) /\
                    (kp:num->real^3->real^3) b z = kp (NUMPAIR (SUC (NUMFST b)) i) w`
  (LABEL_TAC "up") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `b:num`; `z:real^3`]) P2GK_LEVEL_UP32) THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3 a. w IN cball(vec 0,(rho:num->real)(NUMFST a) / &32)
                             ==> w IN p2cg_dm rho a` (LABEL_TAC "dm") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p2cg_dm; IN_CBALL_0; IN_BALL_0] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(p:real^3) IN topspace(p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))` THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  INDUCT_TAC THENL
   [USE_THEN "up" (MP_TAC o C MP (ASSUME `(z:real^3) IN p2cg_dm (rho:num->real) b`) o
                    SPECL [`b:num`; `z:real^3`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`NUMPAIR (SUC (NUMFST b)) i`; `w:real^3`] THEN
    ASM_REWRITE_TAC[NUMPAIR_DEST; LE_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  USE_THEN "up" (MP_TAC o SPECL [`a:num`; `w:real^3`]) THEN
  ANTS_TAC THENL [USE_THEN "dm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`NUMPAIR (SUC (NUMFST a)) i`; `w':real^3`] THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A map near the identity in the CG chart (i,s) (the near-identity property *)
(* p2gk_near3 with 1/(j+1) <= rho_i/56) covers the normal ball of radius     *)
(* rho_i/8 by the image of the piece of radius rho_i/7 (P2GK_BROUWER_IMAGE). *)
(* ------------------------------------------------------------------------- *)

let P2GK_NEAR_BALL_IN = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j k (Fm:real^3->A) i s.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     p2gk_near3 top atlas h yc rho P kp j k Fm /\
     i <= SUC j /\ s < P i /\ inv(&j + &1) <= rho i / &56 /\
     p2cg_nv N0 Nn (NUMPAIR i s) <= k
     ==> mfd_ball (top k,atlas k) (h k) (yc i k s) (rho i / &8) SUBSET
         IMAGE Fm (IMAGE (kp (NUMPAIR i s)) (ball(vec 0,rho i / &7)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`i:num`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `s:num`] o GEN_REWRITE_RULE I [p2gk_near3] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gk_near3"))
                         (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "im") (CONJUNCTS_THEN2 (LABEL_TAC "sm") (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN
   `ball(vec 0,(rho:num->real) i / &8) SUBSET
    IMAGE (\w. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho k (NUMPAIR i s)
                 ((Fm:real^3->A) ((kp:num->real^3->real^3) (NUMPAIR i s) w)))
          (ball(vec 0,rho i / &7))`
  (LABEL_TAC "br") THENL
   [MATCH_MP_TAC P2GK_BROUWER_IMAGE THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < (rho:num->real) i` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < (rho:num->real) i` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,(rho:num->real) i / &6)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN USE_THEN "sm" ACCEPT_TAC;
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
        UNDISCH_TAC `&0 < (rho:num->real) i` THEN REAL_ARITH_TAC];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "cl" (MP_TAC o C MP (ASSUME `(w:real^3) IN cball(vec 0,(rho:num->real) i / &7)`) o
                     REWRITE_RULE[ALL; LENGTH; LE_0; iterated_partial] o
                     SPECL [`[]:num list`; `w:real^3`]) THEN
      UNDISCH_TAC `inv(&j + &1) <= (rho:num->real) i / &56` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR i s`; `k:num`; `(rho:num->real) i / &8`; `q:A`])
                P2GK_NCH_ONTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2cg_ctr; NUMPAIR_DEST] THEN
    UNDISCH_TAC `&0 < (rho:num->real) i` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "br" (MP_TAC o SPEC `y:real^3` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_BALL_0; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(kp:num->real^3->real^3) (NUMPAIR i s) w` THEN
  CONJ_TAC THENL
   [ALL_TAC; EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[IN_BALL_0]] THEN
  USE_THEN "im" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `norm(w:real^3) < (rho:num->real) i / &7` THEN
    UNDISCH_TAC `&0 < (rho:num->real) i` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR i s`; `k:num`]) P2GE_L_FACTS) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(MP_TAC o SPEC `(Fm:real^3->A) ((kp:num->real^3->real^3) (NUMPAIR i s) w)` o
             CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

(* Deep charts at a point in the pair form NUMPAIR i s with s < P i (the     *)
(* form of the charts of p2gk_near3); the proof of P2GK_DEEP_CHART_AT.       *)

let P2GK_DEEP_PAIR_AT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3) p.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     (!j k s. Nn j <= k /\ Nn (SUC j) <= k
              ==> mfd_ball (top k,atlas k) (h k) (yc j k s) (rho j) SUBSET
                  {p | ?i. i < P (SUC j) /\
                           p IN mfd_ball (top k,atlas k) (h k) (yc (SUC j) k i)
                                         (rho (SUC j) / &32)}) /\
     p IN topspace(p2cl_top (p2cg_dm rho) kp)
     ==> !m. ?i s w. m <= i /\ s < P i /\ w IN cball(vec 0,rho i / &32) /\
                     kp (NUMPAIR i s) w = p`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sh")
    ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  SUBGOAL_THEN
   `!b z. z IN p2cg_dm (rho:num->real) b
          ==> ?i w. i < (P:num->num) (SUC (NUMFST b)) /\
                    w IN cball(vec 0,rho (SUC (NUMFST b)) / &32) /\
                    (kp:num->real^3->real^3) b z = kp (NUMPAIR (SUC (NUMFST b)) i) w`
  (LABEL_TAC "up") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `b:num`; `z:real^3`]) P2GK_LEVEL_UP32) THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3 a. w IN cball(vec 0,(rho:num->real)(NUMFST a) / &32)
                             ==> w IN p2cg_dm rho a` (LABEL_TAC "dm") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p2cg_dm; IN_CBALL_0; IN_BALL_0] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(p:real^3) IN topspace(p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))` THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  INDUCT_TAC THENL
   [USE_THEN "up" (MP_TAC o C MP (ASSUME `(z:real^3) IN p2cg_dm (rho:num->real) b`) o
                    SPECL [`b:num`; `z:real^3`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`SUC (NUMFST b)`; `i:num`; `w:real^3`] THEN
    ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i0:num` (X_CHOOSE_THEN `s0:num` (X_CHOOSE_THEN `w:real^3`
    STRIP_ASSUME_TAC))) THEN
  USE_THEN "up" (MP_TAC o SPECL [`NUMPAIR i0 s0`; `w:real^3`]) THEN
  ANTS_TAC THENL [USE_THEN "dm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NUMPAIR_DEST]; ALL_TAC] THEN
  REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`SUC i0`; `i:num`; `w':real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

