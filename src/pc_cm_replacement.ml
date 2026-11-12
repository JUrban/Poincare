(* ========================================================================= *)
(* Unit pc_cm_replacement: the chain theorem CM_CHAIN_CM_REPLACEMENT         *)
(* (CM_TIGHTEN, CM 2008 Thm 2.1) from CM_REPLACEMENT, CM_CONVEXITY and       *)
(* CM_EPS_REG, with the pre-step Contr (pc_cmr_low), CM Lemmas 3.11, 3.34,   *)
(* 3.39 (pc_cmr_l312, pc_cmr_l339), the non-harmonic slices (pc_cmr_nonharm) *)
(* and CM_SPHERE_GAP (pc_hm_reg_sph).                                        *)
(*                                                                           *)
(* First: harmonic spheres depend only on the values on S^2; constant maps   *)
(* have zero energy; the trivial bound for almost harmonic maps; facts on    *)
(* replacement families.                                                     *)
(* ========================================================================= *)

needs "src/pc_cmr_low.ml";;
needs "src/pc_hm_reg_sph.ml";;

prioritize_real();;
type_invention_error := true;;

let CMR_SHARMONIC_SPHERE_EQ = prove
 (`!S (G:real^K->real^K^K) (u:real^3->real^K) u'.
     (!y. y IN sphere(vec 0,&1) ==> u y = u' y) /\ cm_sharmonic S G u
     ==> cm_sharmonic S G u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_sharmonic] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `wan_rext (u:real^3->real^K)` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC CMT_REXT_SPHERE_EQ THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `phi:real^3->real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\e. cm_sen G (\y. closest_point S ((u':real^3->real^K) y + e % phi y))) =
      (\e. cm_sen G (\y. closest_point S (u y + e % phi y)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC CMT_SEN_SPHERE_EQ THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]]]);;

(* A map that is constant on S^2 has zero energy.                            *)

let CMR_SEN_CONST0 = prove
 (`!S (G:real^K->real^K^K) Lam (u:real^3->real^K) q.
     CMR_GCOND G Lam /\ wan_s2_w12 u /\ q IN S /\
     (!y. y IN sphere(vec 0,&1) ==> u y = q)
     ==> cm_sen G u = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_HEMIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!Q. orthogonal_matrix Q ==> (\x. (u:real^3->real^K)(cm_capmap Q x)) = (\x. q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_ID; CMR_QB_FACTS] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `q:real^K`; `vec 0:real^2`; `&1`;
                 `Lam:real`] CMW_CONST_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN
    UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN SIMP_TAC[CMR_GCOND];
    SIMP_TAC[cm_gen] THEN REAL_ARITH_TAC]);;

(* The trivial bound for the almost-harmonic sums: at most 4/lam times the   *)
(* G-energy of the family.                                                  *)

let CMR_AH_BOUND = prove
 (`!S (G:real^K->real^K^K) Lam lam (u:real^3->real^K) n (Q:num->real^3^3) (c:num->real^2)
    r (v:num->real^2->real^K).
     CMR_GCOND G Lam /\ cm_smap S u /\ &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
     (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k) /\ &0 < r k) /\
     (!k. 1 <= k /\ k <= n
          ==> cm_minimizer S G (ball(c k,r k / &8)) (v k) /\
              wan_w120 (ball(c k,r k / &8)) (\y. v k y - u(cm_capmap (Q k) y)))
     ==> sum(1..n) (\k. wan_dir (ball(c k,r k / &8)) (\y. u(cm_capmap (Q k) y) - v k y))
         <= &4 / lam * sum(1..n) (\k. wan_gdir (ball(c k,r k)) G (\y. u(cm_capmap (Q k) y)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "Qr") (LABEL_TAC "vk")))))) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "Qr" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "vk" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `f = \y. (u:real^3->real^K)(cm_capmap (Q(k:num)) y)` THEN
  ABBREV_TAC `B = ball((c:num->real^2) k,r k)` THEN
  ABBREV_TAC `B' = ball((c:num->real^2) k,r k / &8)` THEN
  ABBREV_TAC `w = (v:num->real^2->real^K) k` THEN
  SUBGOAL_THEN `&0 < r(k:num) / &8` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open (B:real^2->bool) /\ open (B':real^2->bool) /\ B' SUBSET B`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B"; "B'"] THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cm_cmap S (B:real^2->bool) (f:real^2->real^K) /\ cm_cmap S B' f`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B"; "B'"; "f"] THEN CONJ_TAC THEN
    MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (B':real^2->bool) (f:real^2->real^K) /\ wan_w12 B (f:real^2->real^K) /\
                wan_w12 B' (w:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[cm_cmap]; ASM_MESON_TAC[cm_cmap];
      UNDISCH_TAC `cm_minimizer S G (B':real^2->bool) (w:real^2->real^K)` THEN
      SIMP_TAC[cm_minimizer; cm_wmap]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CMR_GCOND]) THEN
  SUBGOAL_THEN
   `lam * wan_dir B' (f:real^2->real^K) <= wan_gdir B' G f /\
    lam * wan_dir B' (w:real^2->real^K) <= wan_gdir B' G w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`B':real^2->bool`; `G:real^K->real^K^K`; `f:real^2->real^K`; `lam:real`;
                     `Lam:real`] HMD_GDIR_BOUNDS);
      MP_TAC(ISPECL [`B':real^2->bool`; `G:real^K->real^K^K`; `w:real^2->real^K`; `lam:real`;
                     `Lam:real`] HMD_GDIR_BOUNDS)] THEN
    (ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir B' G (w:real^2->real^K) <= wan_gdir B' G (f:real^2->real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a / &2 <= b / &2 ==> a <= b`) THEN
    REWRITE_TAC[GSYM cm_gen] THEN
    UNDISCH_TAC `cm_minimizer S G (B':real^2->bool) (w:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[cm_wmap] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
      UNDISCH_TAC `cm_cmap S (B':real^2->bool) (f:real^2->real^K)` THEN
      REWRITE_TAC[cm_cmap] THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(\x. (f:real^2->real^K) x - w x) = (\x. --((\y. w y - f y) x))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC WAN_W120_NEG THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "f" THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir B' G (f:real^2->real^K) <= wan_gdir B G f` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir B' (\y. (f:real^2->real^K) y - w y) <= &2 * wan_dir B' f + &2 * wan_dir B' w`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`B':real^2->bool`; `f:real^2->real^K`; `\y. --((w:real^2->real^K) y)`]
                  WAN_DIR_ADD_LE) THEN
    ASM_SIMP_TAC[WAN_W12_NEG; ETA_AX; GSYM VECTOR_SUB] THEN
    MP_TAC(ISPECL [`B':real^2->bool`; `w:real^2->real^K`] WAN_DIR_NEG) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 / lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / lam * (lam * wan_dir B' (f:real^2->real^K)) = &4 * wan_dir B' f /\
                &4 / lam * (lam * wan_dir B' (w:real^2->real^K)) = &4 * wan_dir B' w`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 / lam * (lam * wan_dir B' (f:real^2->real^K)) <= &4 / lam * wan_gdir B' G f /\
    &4 / lam * (lam * wan_dir B' (w:real^2->real^K)) <= &4 / lam * wan_gdir B' G w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 / lam * wan_gdir B' G (w:real^2->real^K) <= &4 / lam * wan_gdir B' G f /\
    &4 / lam * wan_gdir B' G (f:real^2->real^K) <= &4 / lam * wan_gdir B G f`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. (u:real^3->real^K)(cm_capmap (Q(k:num)) y) - w y) = (\y. f y - w y)`
  SUBST1_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Larger eta is weaker.                                                     *)

let CMR_AH_MONO = prove
 (`!S (G:real^K->real^K^K) e0 eta eta' (u:real^3->real^K).
     cm_almost_harmonic S G e0 eta u /\ eta <= eta'
     ==> cm_almost_harmonic S G e0 eta' u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_almost_harmonic] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Every map is almost harmonic with eta = 4 e0 / lam; a map constant on     *)
(* S^2 is almost harmonic with any eta >= 0.                                 *)

let CMR_AH_TRIVIAL = prove
 (`!S (G:real^K->real^K^K) Lam lam e0 eta (u:real^3->real^K).
     CMR_GCOND G Lam /\ cm_smap S u /\ &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\ &0 < e0 /\ &4 / lam * e0 <= eta
     ==> cm_almost_harmonic S G e0 eta u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_almost_harmonic] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 / lam * sum(1..n) (\k. wan_gdir (ball(c k,r k)) G
                                    (\y. (u:real^3->real^K)(cm_capmap (Q k) y)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMR_AH_BOUND THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `Lam:real`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 / lam * e0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_ARITH `&0 < &4`]]);;

let CMR_AH_CONST = prove
 (`!S (G:real^K->real^K^K) Lam lam e0 eta (u:real^3->real^K) q.
     CMR_GCOND G Lam /\ cm_smap S u /\ &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\ &0 <= eta /\ q IN S /\
     (!y. y IN sphere(vec 0,&1) ==> u y = q)
     ==> cm_almost_harmonic S G e0 eta u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_almost_harmonic] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 / lam * sum(1..n) (\k. wan_gdir (ball(c k,r k)) G
                                    (\y. (u:real^3->real^K)(cm_capmap (Q k) y)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMR_AH_BOUND THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `Lam:real`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\k. wan_gdir (ball(c k,r k)) G (\y. (u:real^3->real^K)(cm_capmap (Q k) y))) =
    &0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\y. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) y)) = (\y. q)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[CMR_CAPMAP_FACTS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `q:real^K`; `(c:num->real^2) k`;
                   `(r:num->real) k`; `Lam:real`] CMW_CONST_FACTS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN SIMP_TAC[CMR_GCOND];
      SIMP_TAC[]];
    ASM_REWRITE_TAC[REAL_MUL_RZERO]]);;

(* ========================================================================= *)
(* The almost-harmonic sum of a map g on a family B is at most 2/cc times    *)
(* the decrease of g by replacement on B/8 (convexity cmr_dirok, the cap sum *)
(* CMR_CAP_DIR_SUM, and uniqueness of minimizers).                           *)
(* ========================================================================= *)

(* One term: the minimizer v of the almost-harmonic property and the        *)
(* replacement cmr_minw give the same Dirichlet distance.                    *)

let CMR_AH_TERM = prove
 (`!S (G:real^K->real^K^K) e (f:real^2->real^K) (a:real^2) s v.
     cmw_repex S G e /\ &0 < s /\ cm_cmap S (ball(a,s)) f /\ wan_gdir (ball(a,s)) G f <= e /\
     cm_minimizer S G (ball(a,s)) v /\ wan_w120 (ball(a,s)) (\y. v y - f y)
     ==> wan_dir (ball(a,s)) (\y. f y - v y) =
         wan_dir (ball(a,s)) (\y. cmr_minw S G a s f y - f y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `a:real^2`; `s:real`;
                 `f:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmw_repex S (G:real^K->real^K^K) e` THEN REWRITE_TAC[cmw_repex] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^2`; `s:real`; `f:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^2->real^K` (MP_TAC o last o CONJUNCTS)) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `cmr_minw S G (a:real^2) s (f:real^2->real^K)` th) THEN
    MP_TAC(SPEC `v:real^2->real^K` th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `open(ball(a:real^2,s))` ASSUME_TAC THENL [REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,s)) (f:real^2->real^K) /\
                wan_w12 (ball(a,s)) (cmr_minw S G a s f)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,s)`; `f:real^2->real^K`;
                 `cmr_minw S G (a:real^2) s (f:real^2->real^K)`] CMW_DIR_SUB_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC HMD_DIR_AE THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | x IN ball(a:real^2,s) /\ ~((v:real^2->real^K) x = w0 x)} UNION
              {x | x IN ball(a,s) /\ ~(cmr_minw S G a s (f:real^2->real^K) x = w0 x)}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `a - b:real^N = a - c <=> b = c`] THEN MESON_TAC[]);;

let CMR_AH_SUM = prove
 (`!S (G:real^K->real^K^K) e Lam cc (g:real^3->real^K) n (Q:num->real^3^3)
    (c:num->real^2) r (v:num->real^2->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cmr_dirok S G e cc /\ &0 < cc /\
     cm_smap S g /\ cmr_dfam n Q c r /\
     (!k. 1 <= k /\ k <= n ==> &0 < r k) /\
     (!k. 1 <= k /\ k <= n
          ==> wan_gdir (ball(c k,r k)) G (\y. g(cm_capmap (Q k) y)) <= e) /\
     (!k. 1 <= k /\ k <= n
          ==> cm_minimizer S G (ball(c k,r k / &8)) (v k) /\
              wan_w120 (ball(c k,r k / &8)) (\y. v k y - g(cm_capmap (Q k) y)))
     ==> sum(1..n) (\k. wan_dir (ball(c k,r k / &8)) (\y. g(cm_capmap (Q k) y) - v k y))
         <= &2 / cc * (cm_sen G g - cm_sen G (cmr_repn S G n Q c (\j. r j / &8) g))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "rp") (CONJUNCTS_THEN2 (LABEL_TAC "en")
    (LABEL_TAC "vk"))))))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `g:real^3->real^K`;
                 `cmr_sen_on G (g:real^3->real^K) (cmr_fop n Q c r)`; `&1 / &8`]
                CMR_FAM_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN USE_THEN "en" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &8 * x = x / &8`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "en8") (K ALL_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmr_dfam] o check (fun th ->
    can (find_term ((=) `&8`)) (concl th))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `\j. (r:num->real) j / &8`;
                 `g:real^3->real^K`] CMR_REPN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "val") (K ALL_TAC))))) THEN
  ABBREV_TAC `h = cmr_repn S G n Q (c:num->real^2) (\j. (r:num->real) j / &8)
                    (g:real^3->real^K)` THEN
  SUBGOAL_THEN
   `cc * cm_sen (\y:real^K. mat 1) (\y. (h:real^3->real^K) y - g y) <=
    cm_sen G g - cm_sen G h`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    UNDISCH_TAC `cmr_dirok S (G:real^K->real^K^K) e cc` THEN REWRITE_TAC[cmr_dirok] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\k. wan_dir (ball(c k,r k / &8))
                    (\x. (h:real^3->real^K)(cm_capmap (Q k) x) - g(cm_capmap (Q k) x)))
    <= &2 * cm_sen (\y:real^K. mat 1) (\y. h y - g y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`;
                   `\j. (r:num->real) j / &8`; `\y. (h:real^3->real^K) y - g y`]
                  CMR_CAP_DIR_SUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CMR_S2_W12_SUB THEN ASM_MESON_TAC[cm_smap]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n
        ==> wan_dir (ball(c k,r k / &8)) (\y. (g:real^3->real^K)(cm_capmap (Q k) y) - v k y) =
            wan_dir (ball(c k,r k / &8))
              (\x. (h:real^3->real^K)(cm_capmap (Q k) x) - g(cm_capmap (Q k) x))`
  (LABEL_TAC "term") THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    USE_THEN "rp" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "vk" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 < r(k:num) / &8` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ball((c:num->real^2) k,r k / &8)`;
                   `\x. (h:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x) -
                        g(cm_capmap (Q k) x)`;
                   `\x. cmr_minw S G ((c:num->real^2) k) (r k / &8)
                          (\x. (g:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) x -
                        g(cm_capmap (Q k) x)`] CMW_DIR_EQ_ON) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      USE_THEN "val" (MP_TAC o SPECL [`k:num`; `x:real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`;
                   `\x. (g:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`;
                   `(c:num->real^2) k`; `r(k:num) / &8`; `(v:num->real^2->real^K) k`]
                  CMR_AH_TERM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "en8" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. wan_dir (ball(c k,r k / &8))
                (\x. (h:real^3->real^K)(cm_capmap (Q k) x) - g(cm_capmap (Q k) x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN USE_THEN "term" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * cm_sen (\y:real^K. mat 1) (\y. (h:real^3->real^K) y - g y)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * cm_sen (\y:real^K. mat 1) (\y. (h:real^3->real^K) y - g y) =
                &2 / cc * (cc * cm_sen (\y:real^K. mat 1) (\y. h y - g y))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < cc` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The slice u0 of energy >= 3e/4 and the two families F1, F2 of energy <=   *)
(* e/8 of CM's construction: the chain u0, u1 = H(u0,F1), gamma = H(u1,F2)   *)
(* and the hypotheses of Lemma 3.11 along it.                                *)
(* ========================================================================= *)

let CMR_CORE_CHAIN = prove
 (`!S (G:real^K->real^K^K) d e M (QQ:num->real^3^3) (ce:num->real^2) R1 R2
    (u0:real^3->real^K).
     cmr_ctx S G d e /\ cm_smap S u0 /\ &3 * e / &4 <= cm_sen G u0 /\
     cmr_dfam M QQ ce R1 /\ cmr_dfam M QQ ce R2 /\
     cmr_sen_on G u0 (cmr_fop M QQ ce R1) <= e / &8 /\
     cmr_sen_on G u0 (cmr_fop M QQ ce R2) <= e / &8
     ==> cmr_l3hyp S G e M QQ ce R1 M QQ ce R2 u0 /\
         cmr_l3hyp S G e M QQ ce R2 M QQ ce R1 u0 /\
         cm_smap S (cmr_repn S G M QQ ce R1 u0) /\
         cm_smap S (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0)) /\
         cmr_sen_on G (cmr_repn S G M QQ ce R1 u0) (cmr_fop M QQ ce R2) <= e / &4 /\
         cmr_l3hyp S G e M QQ ce R2 M QQ ce R2 (cmr_repn S G M QQ ce R1 u0) /\
         &0 <= cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce R1 u0) /\
         cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce R1 u0) <= e / &8 /\
         &0 <= cm_sen G (cmr_repn S G M QQ ce R1 u0) -
               cm_sen G (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0)) /\
         &5 * e / &8 <= cm_sen G (cmr_repn S G M QQ ce R1 u0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK) THEN
  SUBGOAL_THEN `cmr_l3hyp S G e M QQ (ce:num->real^2) R1 M QQ ce R2 (u0:real^3->real^K) /\
                cmr_l3hyp S G e M QQ ce R2 M QQ ce R1 u0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cmr_l3hyp] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`; `u0:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `u1 = cmr_repn S G M QQ (ce:num->real^2) R1 (u0:real^3->real^K)` THEN
  SUBGOAL_THEN `cmr_sen_on G (u1:real^3->real^K) (cmr_fop M QQ (ce:num->real^2) R2) <= e / &4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (u0:real^3->real^K) (cmr_fop M QQ (ce:num->real^2) R2) +
                cmr_sen_on G u0 (cmr_fop M QQ ce R1)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "u1" THEN MATCH_MP_TAC CMR_REPN_FOP_BOUND THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`; `u0:real^3->real^K`]
                CMR_L3_DROP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  SUBGOAL_THEN `&5 * e / &8 <= cm_sen G (u1:real^3->real^K)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cmr_l3hyp S G e M QQ (ce:num->real^2) R2 M QQ ce R2 (u1:real^3->real^K)`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmr_l3hyp] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`; `u1:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`; `u1:real^3->real^K`]
                CMR_L3_DROP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Replacement on the half caps decreases the energy less.                  *)

let CMR_HALF_LE = prove
 (`!S (G:real^K->real^K^K) e Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
     ==> cm_sen G (cmr_repn S G n2 Q2 c2 r2 u) <=
         cm_sen G (cmr_repn S G n2 Q2 c2 (\j. r2 j / &2) u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_HALF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV (SPEC `&1 / &2` th)) THEN
    MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV (SPEC `&1` th))) THEN
  REWRITE_TAC[REAL_MUL_LID; ETA_AX; REAL_ARITH `&1 / &2 * x = x / &2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "en1")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC)))) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= a ==> x - a <= x - b`) THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC CMR_DEC_MONO THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[cmr_l3hyp; cm_smap];
    ASM_MESON_TAC[cmr_l3hyp; cmr_dfam];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    USE_THEN "en1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* CM (3.43): the improvement e(t) bounds the decrease D from below.        *)

let CMR_CORE_343 = prove
 (`!S (G:real^K->real^K^K) d e kappa M (QQ:num->real^3^3) (ce:num->real^2) R1 R2
    (u0:real^3->real^K).
     cmr_ctx S G d e /\ &0 < kappa /\ kappa * e <= &1 /\
     (!n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2 (u:real^3->real^K).
        cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
        ==> kappa * (cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. r2 j / &2) u)) pow 2
            <= cm_sen G u -
               cm_sen G (cmr_repn S G n2 Q2 c2 r2 (cmr_repn S G n1 Q1 c1 r1 u))) /\
     cm_smap S u0 /\ &3 * e / &4 <= cm_sen G u0 /\
     cmr_dfam M QQ ce R1 /\ cmr_dfam M QQ ce R2 /\
     cmr_sen_on G u0 (cmr_fop M QQ ce R1) <= e / &8 /\
     cmr_sen_on G u0 (cmr_fop M QQ ce R2) <= e / &8 /\
     (cmr_e S G (&3 * e / &64) u0 <=
      &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce (\j. R1 j / &2) u0)) \/
      cmr_e S G (&3 * e / &64) u0 <=
      &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce (\j. R2 j / &2) u0)))
     ==> kappa * (cmr_e S G (&3 * e / &64) u0 / &8) pow 2
         <= cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "l312")
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`; `R2:num->real`;
                 `u0:real^3->real^K`] CMR_CORE_CHAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                 `&3 * e / &64`; `u0:real^3->real^K`] CMR_ESET_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `et = cmr_e S G (&3 * e / &64) (u0:real^3->real^K)` THEN
  ABBREV_TAC `u1 = cmr_repn S G M QQ (ce:num->real^2) R1 (u0:real^3->real^K)` THEN
  SUBGOAL_THEN `&0 <= et / &8` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN
     `cm_sen G u1 <= cm_sen G (cmr_repn S G M QQ (ce:num->real^2) (\j. R1 j / &2)
                                 (u0:real^3->real^K))`
    ASSUME_TAC THENL
     [EXPAND_TAC "u1" THEN MATCH_MP_TAC CMR_HALF_LE THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`; `M:num`; `QQ:num->real^3^3`;
                            `ce:num->real^2`; `R2:num->real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `et / &8` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kappa * e` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `kappa * (cm_sen G (u0:real^3->real^K) -
                         cm_sen G (cmr_repn S G M QQ (ce:num->real^2) (\j. R2 j / &2) u0)) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "u1" THEN USE_THEN "l312" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* CM (3.44): Lemma 3.11 (3.13) twice and the definition of e(t).           *)

let CMR_CORE_344 = prove
 (`!S (G:real^K->real^K^K) d e kappa M (QQ:num->real^3^3) (ce:num->real^2) R1 R2
    (u0:real^3->real^K) n (Q:num->real^3^3) (c:num->real^2) r.
     cmr_ctx S G d e /\ &0 < kappa /\
     (!mu n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2 (u:real^3->real^K).
        &0 < mu /\ mu <= &1 / &2 /\ cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
        ==> cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) -
            cm_sen G (cmr_repn S G n2 Q2 c2 (\j. mu * r2 j) (cmr_repn S G n1 Q1 c1 r1 u))
            <= sqrt(cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u)) / kappa +
               (cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. (&2 * mu) * r2 j) u))) /\
     cm_smap S u0 /\ &3 * e / &4 <= cm_sen G u0 /\
     cmr_dfam M QQ ce R1 /\ cmr_dfam M QQ ce R2 /\
     cmr_sen_on G u0 (cmr_fop M QQ ce R1) <= e / &8 /\
     cmr_sen_on G u0 (cmr_fop M QQ ce R2) <= e / &8 /\
     cmr_dfam n Q c r /\ cmr_sen_on G u0 (cmr_fop n Q c r) <= &3 * e / &64 /\
     cmr_sen_on G (cmr_repn S G M QQ ce R1 u0) (cmr_fop n Q c r) <= e / &4
     ==> cm_sen G (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0)) -
         cm_sen G (cmr_repn S G n Q c (\j. r j / &8)
                     (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0)))
         <= &2 * sqrt(cm_sen G u0 -
                      cm_sen G (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0))) / kappa +
            cmr_e S G (&3 * e / &64) u0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "l313") (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`; `R2:num->real`;
                 `u0:real^3->real^K`] CMR_CORE_CHAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK) THEN
  ABBREV_TAC `u1 = cmr_repn S G M QQ (ce:num->real^2) R1 (u0:real^3->real^K)` THEN
  ABBREV_TAC `ga = cmr_repn S G M QQ (ce:num->real^2) R2 (u1:real^3->real^K)` THEN
  (* (3.13) for u1, F2 and B with mu = 1/8 *)
  USE_THEN "l313" (MP_TAC o SPECL
   [`&1 / &8`; `M:num`; `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`;
    `n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u1:real^3->real^K`]) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[cmr_l3hyp] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &8 * x = x / &8`; REAL_ARITH `(&2 * &1 / &8) * x = &1 / &4 * x`] THEN
  DISCH_TAC THEN
  (* (3.13) for u0, F1 and B with mu = 1/4 *)
  USE_THEN "l313" (MP_TAC o SPECL
   [`&1 / &4`; `M:num`; `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`;
    `n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u0:real^3->real^K`]) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[cmr_l3hyp] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(&2 * &1 / &4) * x = x / &2`] THEN
  DISCH_TAC THEN
  (* the half-ball decrease of u0 on B is at most e(t) *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                 `&3 * e / &64`; `u0:real^3->real^K`] CMR_ESET_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `cm_sen G (u0:real^3->real^K) -
                            cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. r j / &2) u0)` o
             last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  (* square roots *)
  SUBGOAL_THEN
   `sqrt(cm_sen G (u1:real^3->real^K) - cm_sen G (ga:real^3->real^K)) / kappa <=
    sqrt(cm_sen G (u0:real^3->real^K) - cm_sen G ga) / kappa /\
    sqrt(cm_sen G (u0:real^3->real^K) - cm_sen G (u1:real^3->real^K)) / kappa <=
    sqrt(cm_sen G u0 - cm_sen G (ga:real^3->real^K)) / kappa`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* CM's (B_Psi) at a slice of energy >= 3e/4 (end of the proof of CM Thm     *)
(* 2.1): either D is large and the trivial bound applies, or the families of *)
(* the test have small energy for the earlier maps (stability), and (3.43),  *)
(* (3.44) and convexity give the bound A sqrt(D).                            *)
(* ========================================================================= *)

(* Lemma 3.11 with any smaller constant.                                    *)

let CMR_L312_ANY = prove
 (`!S (G:real^K->real^K^K) d e.
     cmr_ctx S G d e
     ==> ?k0. &0 < k0 /\
           !kappa. &0 < kappa /\ kappa <= k0
                   ==> !n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                        (u:real^3->real^K).
                         cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
                         ==> kappa * (cm_sen G u -
                                      cm_sen G (cmr_repn S G n2 Q2 c2 (\j. r2 j / &2) u))
                                     pow 2
                             <= cm_sen G u -
                                cm_sen G (cmr_repn S G n2 Q2 c2 r2
                                            (cmr_repn S G n1 Q1 c1 r1 u))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real` STRIP_ASSUME_TAC o MATCH_MP CMR_L312) THEN
  EXISTS_TAC `k0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `k0 * (cm_sen G (u:real^3->real^K) -
                    cm_sen G (cmr_repn S G n2 Q2 (c2:num->real^2) (\j. r2 j / &2) u)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CMR_L313_ANY = prove
 (`!S (G:real^K->real^K^K) d e.
     cmr_ctx S G d e
     ==> ?k0. &0 < k0 /\
           !kappa. &0 < kappa /\ kappa <= k0
                   ==> !mu n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                        (u:real^3->real^K).
                         &0 < mu /\ mu <= &1 / &2 /\ cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
                         ==> cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) -
                             cm_sen G (cmr_repn S G n2 Q2 c2 (\j. mu * r2 j)
                                         (cmr_repn S G n1 Q1 c1 r1 u))
                             <= sqrt(cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u)) /
                                kappa +
                                (cm_sen G u -
                                 cm_sen G (cmr_repn S G n2 Q2 c2 (\j. (&2 * mu) * r2 j) u))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k0:real` STRIP_ASSUME_TAC o MATCH_MP CMR_L313) THEN
  EXISTS_TAC `k0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(cm_sen G (u:real^3->real^K) -
                   cm_sen G (cmr_repn S G n1 Q1 (c1:num->real^2) r1 u)) / k0 +
              (cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 (c2:num->real^2)
                                        (\j. (&2 * mu) * r2 j) u))` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `n1:num`;
                   `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`;
                   `&1`] CMR_L3_HALF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
      UNDISCH_TAC `cmr_l3hyp S (G:real^K->real^K^K) e n1 Q1 (c1:num->real^2) r1 n2 Q2
                     (c2:num->real^2) r2 (u:real^3->real^K)` THEN
      REWRITE_TAC[cmr_l3hyp] THEN SIMP_TAC[];
      REWRITE_TAC[REAL_MUL_LID; ETA_AX] THEN SIMP_TAC[]];
    ASM_SIMP_TAC[REAL_LE_INV2]]);;

(* The core.                                                                 *)

let CMR_TIGHT_CORE = prove
 (`!S (G:real^K->real^K^K) d e.
     cmr_ctx S G d e
     ==> ?A. &0 < A /\
           !M (QQ:num->real^3^3) (ce:num->real^2) R1 R2 (u0:real^3->real^K).
             cm_smap S u0 /\ &3 * e / &4 <= cm_sen G u0 /\
             cmr_dfam M QQ ce R1 /\ cmr_dfam M QQ ce R2 /\
             cmr_sen_on G u0 (cmr_fop M QQ ce R1) <= e / &8 /\
             cmr_sen_on G u0 (cmr_fop M QQ ce R2) <= e / &8 /\
             (cmr_e S G (&3 * e / &64) u0 <=
              &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce (\j. R1 j / &2) u0)) \/
              cmr_e S G (&3 * e / &64) u0 <=
              &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce (\j. R2 j / &2) u0)))
             ==> cm_almost_harmonic S G (e / &32)
                   (A * sqrt(cm_sen G u0 -
                             cm_sen G (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0))))
                   (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k12:real` STRIP_ASSUME_TAC o MATCH_MP CMR_L312_ANY) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k13:real` STRIP_ASSUME_TAC o MATCH_MP CMR_L313_ANY) THEN
  ABBREV_TAC `kappa = min k12 (min k13 (inv e))` THEN
  SUBGOAL_THEN `&0 < kappa /\ kappa <= k12 /\ kappa <= k13 /\ kappa * e <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv e /\ inv e * e = &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_LINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < kappa /\ kappa <= k12 /\ kappa <= k13 /\ kappa <= inv e`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "kappa" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv e * e` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `kappa:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `k13:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "l313")] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `kappa:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `k12:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "l312")] THEN
  (* the constants *)
  ABBREV_TAC `Ks = CS * sqrt(e / &2 + e pow 2 / &4)` THEN
  SUBGOAL_THEN `&0 <= e / &2 + e pow 2 / &4` ASSUME_TAC THENL
   [MP_TAC(SPEC `e:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Ks` ASSUME_TAC THENL
   [EXPAND_TAC "Ks" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = e / (&32 * (&2 * Ks + &1))` THEN
  SUBGOAL_THEN `&0 < s0 /\ &2 * Ks * s0 <= e / &32` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * Ks * e / (&32 * (&2 * Ks + &1)) =
                  (e / &32) * ((&2 * Ks) / (&2 * Ks + &1))` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `~(b = &0) ==> &2 * k * e / (&32 * b) = (e / &32) * ((&2 * k) / b)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= k ==> &0 < &2 * k + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A1 = &2 / cc * (&2 / kappa + &8 / sqrt kappa)` THEN
  ABBREV_TAC `A2 = &4 / lam * (&2 * Ks + &1)` THEN
  SUBGOAL_THEN `&0 < sqrt kappa /\ &0 <= A1 /\ &0 < A2 /\ A2 * s0 = &4 / lam * (e / &32)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt kappa` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "A1" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "A2" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MAP_EVERY EXPAND_TAC ["A2"; "s0"] THEN
      UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 <= Ks` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `A1 + A2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`M:num`; `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`;
                       `R2:num->real`; `u0:real^3->real^K`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`; `R2:num->real`;
                 `u0:real^3->real^K`] CMR_CORE_CHAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `kappa:real`;
                 `M:num`; `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`;
                 `R2:num->real`; `u0:real^3->real^K`] CMR_CORE_343) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "l312" ACCEPT_TAC; DISCH_TAC] THEN
  ABBREV_TAC `u1 = cmr_repn S G M QQ (ce:num->real^2) R1 (u0:real^3->real^K)` THEN
  ABBREV_TAC `ga = cmr_repn S G M QQ (ce:num->real^2) R2 (u1:real^3->real^K)` THEN
  ABBREV_TAC `et = cmr_e S G (&3 * e / &64) (u0:real^3->real^K)` THEN
  ABBREV_TAC `D = cm_sen G (u0:real^3->real^K) - cm_sen G (ga:real^3->real^K)` THEN
  ABBREV_TAC `sD = sqrt D` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sD` ASSUME_TAC THENL
   [EXPAND_TAC "sD" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* et <= 8 sqrt(D) / sqrt(kappa) *)
  SUBGOAL_THEN `et <= &8 * sD / sqrt kappa` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                   `&3 * e / &64`; `u0:real^3->real^K`] CMR_ESET_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `et / &8 <= sqrt(D / kappa)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SQRT_DIV] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the test families *)
  REWRITE_TAC[cm_almost_harmonic] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                       `v:num->real^2->real^K`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Qr") (CONJUNCTS_THEN2 (LABEL_TAC "disj")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vk")))) THEN
  ABBREV_TAC `Sg = sum(1..n) (\k. wan_gdir (ball(c k,r k)) G
                                   (\y. (ga:real^3->real^K)(cm_capmap (Q k) y)))` THEN
  SUBGOAL_THEN `cmr_dfam n Q (c:num->real^2) r` ASSUME_TAC THENL
   [REWRITE_TAC[cmr_dfam] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "Qr" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN USE_THEN "disj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> orthogonal_matrix((Q:num->real^3^3) k) /\ &0 < r k`
  (LABEL_TAC "Qr2") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "Qr" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s0 <= sD` THENL
   [(* the trivial bound *)
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 / lam * Sg` THEN CONJ_TAC THENL
     [EXPAND_TAC "Sg" THEN MATCH_MP_TAC CMR_AH_BOUND THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "Qr2" ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 / lam * Sg <= &4 / lam * (e / &32)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `A2 * s0 <= A2 * sD /\ &0 <= A1 * sD` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* small D: the energies on the test family *)
  ABBREV_TAC `W = cmr_fop n Q (c:num->real^2) r` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  SUBGOAL_THEN `cmr_sen_on G (ga:real^3->real^K) W = Sg / &2` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN EXPAND_TAC "Sg" THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `ga:real^3->real^K`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] CMR_SEN_FAM_SUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[cm_gen; real_div; SUM_RMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `CS:real`;
                 `M:num`; `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`; `u0:real^3->real^K`;
                 `W:real^3->bool`] CMR_L3_WDIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `CS:real`;
                 `M:num`; `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`; `M:num`;
                 `QQ:num->real^3^3`; `ce:num->real^2`; `R2:num->real`; `u1:real^3->real^K`;
                 `W:real^3->bool`] CMR_L3_WDIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `CS * sqrt(cm_sen G (u0:real^3->real^K) - cm_sen G (u1:real^3->real^K)) *
    sqrt(e / &2 + e pow 2 / &4) <= Ks * sD /\
    CS * sqrt(cm_sen G (u1:real^3->real^K) - cm_sen G (ga:real^3->real^K)) *
    sqrt(e / &2 + e pow 2 / &4) <= Ks * sD`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ks" THEN EXPAND_TAC "sD" THEN
    ONCE_REWRITE_TAC[REAL_ARITH `CS * a * b = (CS * b) * a`] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE];
       MATCH_MP_TAC SQRT_MONO_LE THEN EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `Ks * sD <= Ks * s0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (u0:real^3->real^K) W <= &3 * e / &64 /\
    cmr_sen_on G (u1:real^3->real^K) W <= e / &4`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* (3.44) *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `kappa:real`;
                 `M:num`; `QQ:num->real^3^3`; `ce:num->real^2`; `R1:num->real`;
                 `R2:num->real`; `u0:real^3->real^K`; `n:num`; `Q:num->real^3^3`;
                 `c:num->real^2`; `r:num->real`] CMR_CORE_344) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "l313" ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* convexity *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `cc:real`;
                 `ga:real^3->real^K`; `n:num`; `Q:num->real^3^3`; `c:num->real^2`;
                 `r:num->real`; `v:num->real^2->real^K`] CMR_AH_SUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "Qr2" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Sg:real` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      EXPAND_TAC "Sg" THEN
      MP_TAC(ISPECL [`{k:num}`; `1..n`;
                     `\k. wan_gdir (ball((c:num->real^2) k,r k)) G
                            (\y. (ga:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) y))`]
                    SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_NUMSEG; IN_DIFF] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC CMW_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
      USE_THEN "Qr2" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN
      UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN SIMP_TAC[CMR_GCOND] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `ga:real^3->real^K`; `(Q:num->real^3^3) j`;
                     `(c:num->real^2) j`; `(r:num->real) j`] CMR_CHART_CMAP) THEN
      ASM_SIMP_TAC[cm_cmap]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* the arithmetic *)
  ABBREV_TAC `X = cm_sen G (ga:real^3->real^K) -
                  cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. r j / &8) ga)` THEN
  SUBGOAL_THEN `&2 / cc * X <= &2 / cc * (&2 * sD / kappa + &8 * sD / sqrt kappa)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 / cc * (&2 * sD / kappa + &8 * sD / sqrt kappa) = A1 * sD` ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A2 * sD` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The context from the chain hypotheses, the tightening of a sweepout       *)
(* (Lemma 3.39 and cmr_fam), and (B_Psi) at one slice in the three cases     *)
(* (constant slice; low energy after Contr; CM's case).                      *)
(* ========================================================================= *)

let CMR_REPEX_MONO = prove
 (`!S (G:real^K->real^K^K) e e'. cmw_repex S G e /\ e' <= e ==> cmw_repex S G e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_repex] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMR_CTX_FROM_CHAIN = prove
 (`CM_REPLACEMENT_STATEMENT (:K) /\ CM_CONVEXITY_STATEMENT (:K) /\ CM_EPS_REG_STATEMENT (:K)
   ==> !S (G:real^K->real^K^K) d.
         cm_target S G d
         ==> ?eR CR e1. &0 < eR /\ &0 < CR /\ cmw_repex S G eR /\ cmw_repcont S G eR /\
                        cmr_repest S G eR CR /\ &0 < e1 /\ e1 <= eR /\
                        !e. &0 < e /\ e <= e1 ==> cmr_ctx S G d e`,
  REWRITE_TAC[CM_REPLACEMENT_STATEMENT; CM_CONVEXITY_STATEMENT; CM_EPS_REG_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rep") (CONJUNCTS_THEN2 (LABEL_TAC "conv")
    (LABEL_TAC "eps"))) THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  USE_THEN "rep" (MP_TAC o C MATCH_MP (ASSUME `cm_target S (G:real^K->real^K^K) d`) o
                   SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `eR:real` (X_CHOOSE_THEN `CR:real` STRIP_ASSUME_TAC)) THEN
  USE_THEN "conv" (MP_TAC o C MATCH_MP (ASSUME `cm_target S (G:real^K->real^K^K) d`) o
                   SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `eC:real` (X_CHOOSE_THEN `cC:real` STRIP_ASSUME_TAC)) THEN
  USE_THEN "eps" (MP_TAC o C MATCH_MP (ASSUME `cm_target S (G:real^K->real^K^K) d`) o
                   SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `eE:real` (X_CHOOSE_THEN `CE:num->real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `cmw_repex S (G:real^K->real^K^K) eR /\ cmw_repcont S G eR /\
                cmr_repest S G eR CR`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cmw_repex; cmw_repcont; cmr_repest] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`eR:real`; `CR:real`; `min eR (min eC eE)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN REWRITE_TAC[cmr_ctx] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMR_REPEX_MONO THEN EXISTS_TAC `eR:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`eE:real`; `CE:num->real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`eC:real`; `cC:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

(* The tightening of a sweepout: Lemma 3.39 and the family construction.    *)

let CMR_TIGHTEN_SWEEP = prove
 (`!S (G:real^K->real^K^K) d e Lam C eps Estar (sigma:real^3->real->real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     cmr_repest S G e C /\ &0 <= C /\ CMR_GCOND G Lam /\ &0 < eps /\ &4 * eps <= e /\
     cm_sweep S sigma /\
     (!t. t IN real_interval[&0,&1] /\ Estar <= cm_sen G (\y. sigma y t)
          ==> &0 < cmr_e S G (eps / &8) (\y. sigma y t))
     ==> ?gamma. cm_sweep S gamma /\ cm_shomotopic S sigma gamma /\
                 (!t. t IN real_interval[&0,&1]
                      ==> cm_sen G (\y. gamma y t) <= cm_sen G (\y. sigma y t)) /\
                 !t. t IN real_interval[&0,&1]
                     ==> ?M (QQ:num->real^3^3) (cc:num->real^2) R1 R2.
                           (\y. gamma y t) =
                           cmr_repn S G M QQ cc R2 (cmr_repn S G M QQ cc R1 (\y. sigma y t)) /\
                           (!j. orthogonal_matrix (QQ j)) /\
                           cmr_dfam M QQ cc R1 /\ cmr_dfam M QQ cc R2 /\
                           cmr_sen_on G (\y. sigma y t) (cmr_fop M QQ cc R1) <= eps / &3 /\
                           cmr_sen_on G (\y. sigma y t) (cmr_fop M QQ cc R2) <= eps / &3 /\
                           (Estar <= cm_sen G (\y. sigma y t)
                            ==> cmr_e S G (eps / &8) (\y. sigma y t) <=
                                &8 * (cm_sen G (\y. sigma y t) -
                                      cm_sen G (cmr_repn S G M QQ cc (\j. R1 j / &2)
                                                  (\y. sigma y t))) \/
                                cmr_e S G (eps / &8) (\y. sigma y t) <=
                                &8 * (cm_sen G (\y. sigma y t) -
                                      cm_sen G (cmr_repn S G M QQ cc (\j. R2 j / &2)
                                                  (\y. sigma y t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `C:real`; `eps:real`; `Estar:real`; `sigma:real^3->real->real^K`]
                CMR_L339) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `QQ:num->real^3^3`
    (X_CHOOSE_THEN `cc:num->real^2` (X_CHOOSE_THEN `RR:num->real->real`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "split")))))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps:real`;
                 `M:num`; `QQ:num->real^3^3`; `cc:num->real^2`; `RR:num->real->real`;
                 `sigma:real^3->real->real^K`] CMR_FAMOK_FROM_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "split" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `R1:num->real` (X_CHOOSE_THEN `R2:num->real`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`R1:num->real`; `R2:num->real`] THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  EXISTS_TAC `cmr_fam S G M QQ (cc:num->real^2) RR (sigma:real^3->real->real^K) (&1)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMR_FAM_SWEEP THEN MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMR_FAM_HOMOTOPIC THEN MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMR_FAM_SEN_LE THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "split" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `R1:num->real` (X_CHOOSE_THEN `R2:num->real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`M:num`; `QQ:num->real^3^3`; `cc:num->real^2`; `R1:num->real`;
                          `R2:num->real`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FUN_EQ_THM; cmr_fam; REAL_MUL_LID] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `QQ:num->real^3^3`;
                   `cc:num->real^2`; `\j. (RR:num->real->real) j t`; `R1:num->real`;
                   `R2:num->real`; `\y. (sigma:real^3->real->real^K) y t`] CMR_REPN_SPLIT) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* The replacement chain without lower energy bound.                        *)

let CMR_CHAIN_FACTS = prove
 (`!S (G:real^K->real^K^K) e Lam M (QQ:num->real^3^3) (cc:num->real^2) R1 R2
    (u0:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 <= e /\ cm_smap S u0 /\
     cmr_dfam M QQ cc R1 /\ cmr_dfam M QQ cc R2 /\
     cmr_sen_on G u0 (cmr_fop M QQ cc R1) <= e / &8 /\
     cmr_sen_on G u0 (cmr_fop M QQ cc R2) <= e / &8
     ==> cm_smap S (cmr_repn S G M QQ cc R1 u0) /\
         cm_smap S (cmr_repn S G M QQ cc R2 (cmr_repn S G M QQ cc R1 u0)) /\
         cm_sen G (cmr_repn S G M QQ cc R1 u0) <= cm_sen G u0 /\
         cm_sen G (cmr_repn S G M QQ cc R2 (cmr_repn S G M QQ cc R1 u0)) <=
         cm_sen G (cmr_repn S G M QQ cc R1 u0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= M /\ &0 < R1 k
        ==> wan_gdir (ball((cc:num->real^2) k,R1 k)) G
              (\x. (u0:real^3->real^K)(cm_capmap ((QQ:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u0:real^3->real^K`; `M:num`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `R1:num->real`; `k:num`]
                  CMR_FAM_CAP_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    REWRITE_TAC[cm_gen] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `cc:num->real^2`; `R1:num->real`; `u0:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `cc:num->real^2`; `R1:num->real`; `u0:real^3->real^K`]
                CMR_L3_DROP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `u1 = cmr_repn S G M QQ (cc:num->real^2) R1 (u0:real^3->real^K)` THEN
  SUBGOAL_THEN `cmr_sen_on G (u1:real^3->real^K) (cmr_fop M QQ (cc:num->real^2) R2) <= e / &4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (u0:real^3->real^K) (cmr_fop M QQ (cc:num->real^2) R2) +
                cmr_sen_on G u0 (cmr_fop M QQ cc R1)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "u1" THEN MATCH_MP_TAC CMR_REPN_FOP_BOUND THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= M /\ &0 < R2 k
        ==> wan_gdir (ball((cc:num->real^2) k,R2 k)) G
              (\x. (u1:real^3->real^K)(cm_capmap ((QQ:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u1:real^3->real^K`; `M:num`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `R2:num->real`; `k:num`]
                  CMR_FAM_CAP_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    REWRITE_TAC[cm_gen] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `cc:num->real^2`; `R2:num->real`; `u1:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `cc:num->real^2`; `R2:num->real`; `u1:real^3->real^K`]
                CMR_L3_DROP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* (B_Psi) at one slice: u0 = sigma(t), E0 = E(gamma0(t)).                   *)

let CMR_BPSI_SLICE = prove
 (`!S (G:real^K->real^K^K) d eL eR Lam lam A A' (u0:real^3->real^K) E0 M (QQ:num->real^3^3)
    (cc:num->real^2) R1 R2.
     cmr_ctx S G d eL /\ cmw_repex S G eR /\ cmw_repcont S G eR /\ &0 <= eR /\
     CMR_GCOND G Lam /\ &0 < lam /\ (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
     &0 <= A /\ A <= A' /\ &4 / lam * (eL / &32) <= A' * sqrt(eL / &4) /\
     (!M (QQ:num->real^3^3) (ce:num->real^2) R1 R2 (u0:real^3->real^K).
        cm_smap S u0 /\ &3 * eL / &4 <= cm_sen G u0 /\
        cmr_dfam M QQ ce R1 /\ cmr_dfam M QQ ce R2 /\
        cmr_sen_on G u0 (cmr_fop M QQ ce R1) <= eL / &8 /\
        cmr_sen_on G u0 (cmr_fop M QQ ce R2) <= eL / &8 /\
        (cmr_e S G (&3 * eL / &64) u0 <=
         &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce (\j. R1 j / &2) u0)) \/
         cmr_e S G (&3 * eL / &64) u0 <=
         &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ ce (\j. R2 j / &2) u0)))
        ==> cm_almost_harmonic S G (eL / &32)
              (A * sqrt(cm_sen G u0 -
                        cm_sen G (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0))))
              (cmr_repn S G M QQ ce R2 (cmr_repn S G M QQ ce R1 u0))) /\
     cm_smap S u0 /\ cm_sen G u0 <= E0 /\
     ((?q. q IN S /\ !y. y IN sphere(vec 0,&1) ==> u0 y = q) \/ eL < E0) /\
     (!j. orthogonal_matrix (QQ j)) /\ cmr_dfam M QQ cc R1 /\ cmr_dfam M QQ cc R2 /\
     cmr_sen_on G u0 (cmr_fop M QQ cc R1) <= eL / &8 /\
     cmr_sen_on G u0 (cmr_fop M QQ cc R2) <= eL / &8 /\
     (&3 * eL / &4 <= cm_sen G u0
      ==> cmr_e S G (&3 * eL / &64) u0 <=
          &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ cc (\j. R1 j / &2) u0)) \/
          cmr_e S G (&3 * eL / &64) u0 <=
          &8 * (cm_sen G u0 - cm_sen G (cmr_repn S G M QQ cc (\j. R2 j / &2) u0)))
     ==> cm_almost_harmonic S G (eL / &32)
           (A' * sqrt(E0 - cm_sen G (cmr_repn S G M QQ cc R2 (cmr_repn S G M QQ cc R1 u0))))
           (cmr_repn S G M QQ cc R2 (cmr_repn S G M QQ cc R1 u0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "core")
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK o check (fun th ->
    can (find_term ((=) `cmr_ctx:(real^K->bool)->(real^K->real^K^K)->real->real->bool`))
        (concl th))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `eL:real`; `Lam:real`; `M:num`;
                 `QQ:num->real^3^3`; `cc:num->real^2`; `R1:num->real`; `R2:num->real`;
                 `u0:real^3->real^K`] CMR_CHAIN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `u1 = cmr_repn S G M QQ (cc:num->real^2) R1 (u0:real^3->real^K)` THEN
  ABBREV_TAC `ga = cmr_repn S G M QQ (cc:num->real^2) R2 (u1:real^3->real^K)` THEN
  SUBGOAL_THEN `&0 <= E0 - cm_sen G (ga:real^3->real^K)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `E0:real`)) (concl th))) THENL
   [(* constant slice *)
    DISCH_THEN(X_CHOOSE_THEN `q:real^K` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CMR_AH_CONST THEN
    MAP_EVERY EXISTS_TAC [`Lam:real`; `lam:real`; `q:real^K`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eR:real`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `R1:num->real`; `u0:real^3->real^K`;
                   `q:real^K`] CMR_REPN_CONST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `M:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eR:real`;
                   `QQ:num->real^3^3`; `cc:num->real^2`; `R2:num->real`; `u1:real^3->real^K`;
                   `q:real^K`] CMR_REPN_CONST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `M:num`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ASM_CASES_TAC `&3 * eL / &4 <= cm_sen G (u0:real^3->real^K)` THENL
   [(* CM's case *)
    MATCH_MP_TAC CMR_AH_MONO THEN
    EXISTS_TAC `A * sqrt(cm_sen G (u0:real^3->real^K) - cm_sen G (ga:real^3->real^K))` THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ga"; "u1"] THEN USE_THEN "core" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
        is_disj(rand(concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `A * sqrt(E0 - cm_sen G (ga:real^3->real^K))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE]];
    (* low energy after Contr: the trivial bound *)
    MATCH_MP_TAC CMR_AH_TRIVIAL THEN
    MAP_EVERY EXISTS_TAC [`Lam:real`; `lam:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A' * sqrt(eL / &4)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The slices of energy >= 3eL/4 after Contr are not critical (CMR_NONHARM,  *)
(* CM_SPHERE_GAP), and CM Thm 2.1: CM_TIGHTEN from CM_REPLACEMENT,           *)
(* CM_CONVEXITY and CM_EPS_REG, with e0 = eL/32 and Psi(x) = A' sqrt(x); the *)
(* chain theorem CM_CHAIN_CM_REPLACEMENT.                                    *)
(* ========================================================================= *)

(* The slices of energy >= Estar after Contr are not critical: cmr_e > 0.   *)

let CMR_LOW_POS = prove
 (`!S (G:real^K->real^K^K) d e Lam eg E2 Estar ee (gamma0:real^3->real->real^K) sigma.
     cm_target S G d /\ cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < ee /\ &2 * ee <= e /\
     &0 < Estar /\ E2 <= eg /\
     (!u:real^3->real^K. cm_sharmonic S G u ==> eg <= cm_sen G u) /\
     cm_sweep S sigma /\
     (!t. t IN real_interval[&0,&1] ==> ~cm_sharmonic S G (\y. gamma0 y t)) /\
     (!t. t IN real_interval[&0,&1]
          ==> cm_sen G (\y. sigma y t) <= cm_sen G (\y. gamma0 y t)) /\
     (!t. t IN real_interval[&0,&1] /\ E2 <= cm_sen G (\y. gamma0 y t)
          ==> !y. y IN sphere(vec 0,&1) ==> sigma y t = gamma0 y t)
     ==> !t. t IN real_interval[&0,&1] /\ Estar <= cm_sen G (\y. sigma y t)
             ==> &0 < cmr_e S G ee (\y. sigma y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `cm_smap S (\y. (sigma:real^3->real->real^K) y t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> (sigma:real^3->real->real^K) y t IN S`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_smap S (\y. (sigma:real^3->real->real^K) y t)` THEN SIMP_TAC[cm_smap];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `ee:real`;
                 `\y. (sigma:real^3->real->real^K) y t`] CMR_ESET_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `?c:real^K. !y. y IN sphere(vec 0,&1) ==> (sigma:real^3->real->real^K) y t = c` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `c:real^K`) THEN
    SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
     [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`;
                   `\y. (sigma:real^3->real->real^K) y t`; `c:real^K`] CMR_SEN_CONST0) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `cm_smap S (\y. (sigma:real^3->real->real^K) y t)` THEN SIMP_TAC[cm_smap];
        ASM_MESON_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `ee:real`; `\y. (sigma:real^3->real->real^K) y t`] CMR_NONHARM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `E2 <= cm_sen G (\y. (gamma0:real^3->real->real^K) y t)` THENL
   [SUBGOAL_THEN `cm_sharmonic S G (\y. (gamma0:real^3->real->real^K) y t)` MP_TAC THENL
     [MATCH_MP_TAC CMR_SHARMONIC_SPHERE_EQ THEN
      EXISTS_TAC `\y. (sigma:real^3->real->real^K) y t` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `E2:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eg <= cm_sen G (\y. (sigma:real^3->real->real^K) y t)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `eg:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cm_sen G (\y. (sigma:real^3->real->real^K) y t) <=
                cm_sen G (\y. (gamma0:real^3->real->real^K) y t)` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* CM Thm 2.1 (CM_TIGHTEN) from the three chain statements.                 *)

let CMR_TIGHTEN_FROM_CHAIN = prove
 (`CM_REPLACEMENT_STATEMENT (:K) /\ CM_CONVEXITY_STATEMENT (:K) /\ CM_EPS_REG_STATEMENT (:K)
   ==> CM_TIGHTEN_STATEMENT (:K)`,
  DISCH_TAC THEN REWRITE_TAC[CM_TIGHTEN_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `cm_target S (G:real^K->real^K^K) d`) o
    SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] o MATCH_MP CMR_CTX_FROM_CHAIN) THEN
  DISCH_THEN(X_CHOOSE_THEN `eR:real` (X_CHOOSE_THEN `CR:real` (X_CHOOSE_THEN `e1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))))))))))) THEN
  MP_TAC(ISPEC `(:K)` CM_SPHERE_GAP) THEN REWRITE_TAC[CM_SPHERE_GAP_STATEMENT] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `cm_target S (G:real^K->real^K^K) d`) o
    SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `eg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gap"))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam2:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `!z w:real^K. lam * norm w pow 2 <= w dot ((G:real^K->real^K^K) z ** w)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eR:real`; `CR:real`;
                 `Lam:real`] CMR_LOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ebar:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low"))) THEN
  ABBREV_TAC `eL = min (e1 / &4) (min (eg / &4) (Ebar / &8))` THEN
  SUBGOAL_THEN `&0 < eL /\ eL <= e1 / &4 /\ eL <= eg / &4 /\ eL <= Ebar / &8`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "eL" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cmr_ctx S (G:real^K->real^K^K) d eL` ASSUME_TAC THENL
   [USE_THEN "ctx" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `A:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "core")) o
    MATCH_MP CMR_TIGHT_CORE) THEN
  SUBGOAL_THEN `&0 < sqrt(eL / &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 / lam * (eL / &32) / sqrt(eL / &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A' = A + &4 / lam * (eL / &32) / sqrt(eL / &4)` THEN
  SUBGOAL_THEN `&0 <= A /\ A <= A' /\ &0 <= A' /\ &4 / lam * (eL / &32) <= A' * sqrt(eL / &4)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(A + &4 / lam * (eL / &32) / sqrt(eL / &4)) * sqrt(eL / &4) =
                  A * sqrt(eL / &4) + &4 / lam * (eL / &32)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt(eL / &4)` THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> y <= x + y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`eL / &32`; `\x. A' * sqrt x`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT];
    REWRITE_TAC[SQRT_0; REAL_MUL_RZERO];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`gamma0:real^3->real->real^K`; `W:real`] THEN STRIP_TAC THEN
  USE_THEN "low" (MP_TAC o SPECL [`eL:real`; `&2 * eL`; `gamma0:real^3->real->real^K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^3->real->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eR:real`; `Lam:real`;
                 `eg:real`; `&2 * eL`; `&3 * eL / &4`; `(&3 * eL / &8) / &8`;
                 `gamma0:real^3->real->real^K`; `sigma:real^3->real->real^K`] CMR_LOW_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eR:real`; `Lam:real`;
                 `CR:real`; `&3 * eL / &8`; `&3 * eL / &4`; `sigma:real^3->real->real^K`]
                CMR_TIGHTEN_SWEEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real^3->real->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "slice"))))) THEN
  EXISTS_TAC `gamma:real^3->real->real^K` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMW_SHOMOTOPIC_TRANS THEN EXISTS_TAC `sigma:real^3->real->real^K` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm_sen G (\y. (sigma:real^3->real->real^K) y t)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `cm_smap S (\y. (sigma:real^3->real->real^K) y t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  SUBGOAL_THEN `cm_sen G (\y. (sigma:real^3->real->real^K) y t) <=
                cm_sen G (\y. (gamma0:real^3->real->real^K) y t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(?q. q IN S /\ !y. y IN sphere(vec 0,&1) ==> (sigma:real^3->real->real^K) y t = q) \/
    eL < cm_sen G (\y. (gamma0:real^3->real->real^K) y t)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `cm_sen G (\y. (gamma0:real^3->real->real^K) y t) <= eL` THENL
     [DISJ1_TAC THEN EXISTS_TAC `(sigma:real^3->real->real^K) (basis 3) t` THEN
      SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
       [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `cm_smap S (\y. (sigma:real^3->real->real^K) y t)` THEN
        REWRITE_TAC[cm_smap] THEN DISCH_THEN(MP_TAC o SPEC `basis 3:real^3` o
          CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `basis 3:real^3`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      DISJ2_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "slice" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
  REWRITE_TAC[REAL_ARITH `(&3 * eL / &8) / &3 = eL / &8`;
              REAL_ARITH `(&3 * eL / &8) / &8 = &3 * eL / &64`] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `QQ:num->real^3^3`
    (X_CHOOSE_THEN `cc:num->real^2` (X_CHOOSE_THEN `R1:num->real`
     (X_CHOOSE_THEN `R2:num->real` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)))))) THEN
  MATCH_MP_TAC CMR_BPSI_SLICE THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `eR:real`; `Lam:real`; `lam:real`; `A:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CM_CHAIN_CM_REPLACEMENT = prove
 (`!kk:K->bool. CM_CHAIN_CM_REPLACEMENT_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_CHAIN_CM_REPLACEMENT_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC CMR_TIGHTEN_FROM_CHAIN THEN ASM_REWRITE_TAC[]);;

