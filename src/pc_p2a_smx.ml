(* ========================================================================= *)
(* pc_p2a_smx: smoothing of admissible curves without a smooth base point,   *)
(* and of curves with singular corners.  P2AXS_SMOOTHING: P2A_SMOOTHING_GEN  *)
(* without p2a_bsmooth (corners are rounded at times > 0 only; the region at *)
(* a corner comes from its smooth point, P2AXR_REGION_AT).                   *)
(* P2AXS_SMOOTHING_X: a p2a_admx curve is approximated in L-length, with the *)
(* same end points, by p2a_adm1 curves: each singular corner is cut out by a *)
(* chart segment (the L-length of the segment is at most the energy of the   *)
(* cut piece, Cauchy-Schwarz), then the corners are rounded.                 *)
(*                                                                           *)
(* First: rounding corners without p2a_bsmooth (copies of P2A_ROUND1,        *)
(* P2A_SMOOTH_INDUCT, P2A_SMOOTHING_GEN).                                    *)
(* ========================================================================= *)

needs "src/pc_p2a_rgx.ml";;
needs "src/pc_p2a_smth.ml";;
needs "src/pc_p2a_usc.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AXS_ROUND1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) P tau1 e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_adm V tt x b gamma /\
     p2a_pc1 V tt gamma (&0) b P /\ &0 < tau1 /\ tau1 < b /\
     p2a_atlas_const V (tt - tau1) /\ &0 < e
     ==> ?gamma1. p2a_adm V tt x b gamma1 /\ p2a_pc1 V tt gamma1 (&0) b (P DELETE tau1) /\
                  gamma1 b = gamma b /\
                  p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e /\
                  (!tau. ~(abs(tau - tau1) < e) ==> gamma1 tau = gamma tau) /\
                  (!tau. &0 <= tau /\ tau <= b
                         ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                      (p2a_vmetric V (tt - tau)) (gamma1 tau) (gamma tau) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s0. &0 < s0 /\ s0 pow 2 = tau1` (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `sqrt tau1` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  (* the region chart at the corner *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `s0:real`] P2AXR_REGION_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; P2AX_ADM_IMP]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  (* corner bounds *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `P:real->bool`; `s0:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`] P2A_CORNER_S_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0 + k0 / &2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[NORM_POS_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M`
  ASSUME_TAC THENL [REWRITE_TAC[p2a_cdata] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the slice atlas is constant near the corner time *)
  UNDISCH_TAC `p2a_atlas_const (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s0 pow 2)` THEN
  REWRITE_TAC[p2a_atlas_const] THEN
  DISCH_THEN(X_CHOOSE_THEN `da:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`s0:real`; `da:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k1. &0 < k1 /\ k1 < k0 /\ k1 <= ha` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (k0 / &2) ha` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* uniform slice distances near the corner *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `s0 - k1`; `s0 + k1`; `s0:real`;
                 `(gamma:real->A)(s0 pow 2)`] P2A_SLICE_DIST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `da:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vatlas")) (concl th))) THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x - y) < d ==> abs((t - x) - (t - y)) < d`) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ha:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DIST"))))) THEN
  SUBGOAL_THEN `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),r / &2) SUBSET
                IMAGE phi (U INTER W)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "DIST" (MP_TAC o SPECL [`s0:real`; `z:real^N`; `z:real^N`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* a bound for the s-Lagrangian near the corner *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - k1`; `s0 + k1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),r / &2)`;
                 `s0 - k1 / &2`; `s0 + k1 / &2`; `(&1 + p2a_bc) * M`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th) &&
      can (find_term ((=) `k0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB"))] THEN
  (* the choice of the scale k *)
  MP_TAC(SPECL [`r / &2`; `M:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KC"))) THEN
  MP_TAC(SPECL [`e:real`; `L * M`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KD"))) THEN
  MP_TAC(SPECL [`e:real`; `&3 * abs Kb`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ke:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KE"))) THEN
  MP_TAC(SPECL [`s0:real`; `e:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `he:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HE"))) THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k <= k1 / &2 /\ k <= r / &2 /\ k <= kc /\ k <= kd /\ k <= ke /\ k <= he / &2`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min (k1 / &2) (r / &2)) (min (min kc kd) (min ke (he / &2)))` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * M < r / &2 /\ k * (L * M) < e /\ k * (&3 * abs Kb) < e`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "KC" MATCH_MP_TAC; USE_THEN "KD" MATCH_MP_TAC; USE_THEN "KE" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k < k0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_YCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BC1") (CONJUNCTS_THEN2 (LABEL_TAC "BEQ")
    (LABEL_TAC "BNEAR"))) THEN
  (* the blend and the curve stay in the closed ball of radius r/2 *)
  SUBGOAL_THEN
   `!s. abs(s - s0) <= k
        ==> (phi:A->real^N)((gamma:real->A)(s pow 2)) IN cball(phi(gamma(s0 pow 2)),r / &2) /\
            p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k (lift s) IN
            cball(phi(gamma(s0 pow 2)),r / &2)`
  (LABEL_TAC "BALL") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    SUBGOAL_THEN `M * abs(s - s0) <= k * M` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * abs(s - s0)` THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "BNEAR" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < k
        ==> p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2)))
                      s0 k (lift s) IN IMAGE phi (U INTER W)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
      not(is_forall(concl th)))) THEN
    USE_THEN "BALL" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `p2a_round (gamma:real->A) U W (phi:A->real^N) s0 k` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_ROUND_SEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2A_ROUND_PC1 THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p2a_round] THEN
    SUBGOAL_THEN `~(b <= (s0 - &3 * k / &4) pow 2) /\ ~(b <= (s0 + &3 * k / &4) pow 2)`
    (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(s0 + &3 * k / &4) pow 2 < b /\ (s0 - &3 * k / &4) pow 2 <= (s0 + &3 * k / &4) pow 2`
    MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(s0 + k0) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2A_ROUND_LENGTH THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`; `Kb:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`s:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "BALL" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      CONJ_TAC THEN USE_THEN "KB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `k * Kb <= k * abs Kb` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_round] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(abs(tau - s0 pow 2) < e)` THEN REWRITE_TAC[] THEN
    USE_THEN "HE" (MP_TAC o SPEC `s0 - &3 * k / &4`) THEN
    USE_THEN "HE" (MP_TAC o SPEC `s0 + &3 * k / &4`) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2A_ROUND_DIST THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`; `r:real`;
                          `L:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2AXS_SMOOTH_INDUCT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ p2a_atlas_lc V
     ==> !P. FINITE P
             ==> !(gamma:real->A) e.
                   p2a_adm V tt x b gamma /\ p2a_pc1 V tt gamma (&0) b P /\
                   (!s. s IN P ==> &0 < s /\ s < b /\ p2a_atlas_const V (tt - s)) /\ &0 < e
                   ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                                p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                                (!tau. (!s. s IN P ==> ~(abs(tau - s) < e))
                                       ==> gamma' tau = gamma tau) /\
                                (!tau. &0 <= tau /\ tau <= b
                                       ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                                    (p2a_vmetric V (tt - tau))
                                                    (gamma' tau) (gamma tau) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`gamma:real->A`; `e:real`] THEN STRIP_TAC THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[p2a_adm1; REAL_LE_ADDR] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                   `tau:real`] P2A_ADM_DIST_REFL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau1:real`; `P:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`gamma:real->A`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau1 /\ tau1 < b /\
                p2a_atlas_const (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - tau1)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tau1:real`; `P:real->bool`] P2A_REAL_FINITE_AVOID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e1 = min (e / &2) (d / &3)` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= e / &2 /\ &3 * e1 <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `(tau1:real) INSERT P`; `tau1:real`; `e1:real`] P2AXS_ROUND1) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((tau1:real) INSERT P) DELETE tau1 = P` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S1") (LABEL_TAC "D1"))))))) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`gamma1:real->A`; `e1:real`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S2") (LABEL_TAC "D2")))))) THEN
  EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `(gamma1:real->A) tau` THEN CONJ_TAC THENL
     [USE_THEN "S2" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "S1" MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau1:real`) THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs(tau - tau1) < e1` THENL
   [SUBGOAL_THEN `(gamma':real->A) tau = gamma1 tau` SUBST1_TAC THENL
     [USE_THEN "S2" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e1:real` THEN
    CONJ_TAC THENL [USE_THEN "D1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(gamma1:real->A) tau = gamma tau` (SUBST1_TAC o SYM) THENL
     [USE_THEN "S1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e1:real` THEN
    CONJ_TAC THENL [USE_THEN "D2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

let P2AXS_SMOOTHING = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_adm V tt x b gamma /\ &0 < e
     ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                  p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                  !tau. &0 <= tau /\ tau <= b
                        ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                     (p2a_vmetric V (tt - tau)) (gamma' tau) (gamma tau) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?P. p2a_pc1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) tt gamma (&0) b P`
  (X_CHOOSE_TAC `P:real->bool`) THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `P:real->bool`]
                P2A_PC1_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2AXS_SMOOTH_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `{s | s IN P /\ &0 < s /\ s < b /\
                                p2a_atlas_const (V:(real->A topology)#
                                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                                  (tt - s)}`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[p2a_pc1]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `e:real`]) THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Displacement of the region-chart curve of a p2a_admx curve near a point   *)
(* where it may be singular, before (P2AXS_END_DISP) and after               *)
(* (P2AXS_START_DISP) it, and the end-point modification by a chart segment  *)
(* (copies of P2A_END_ENERGY, P2A_JCURVE, P2A_END_DISP for p2a_admx).        *)
(* ------------------------------------------------------------------------- *)

let P2AXS_END_ENERGY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) sa sb' s1 s c Kb.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s /\ s pow 2 <= b /\ sa < s1 /\ s < sb' /\
     (!r. sa < r /\ r < sb' ==> a' < tt - r pow 2 /\ tt - r pow 2 <= b'') /\
     (!r. s1 <= r /\ r <= s ==> gamma(r pow 2) IN U INTER W) /\
     (!r. s1 <= r /\ r <= s
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift r)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift r))) /\
     &0 < c /\
     (!r A. s1 <= r /\ r <= s
            ==> c * norm A pow 2 <=
                A dot (p2a_rlocal V W b'' (U INTER W,phi) (tt - r pow 2)
                         (phi(gamma(r pow 2))) ** A)) /\
     (!r. s1 <= r /\ r <= s
          ==> abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt r
                           (phi(gamma(r pow 2))) (vec 0)) <= Kb)
     ==> norm(phi(gamma(s pow 2)) - phi(gamma(s1 pow 2))) pow 2 <=
         (&2 / c) * (s - s1) *
         (real_integral (real_interval[s1 pow 2,s pow 2]) (p2a_L_integrand V tt gamma b) +
          Kb * (s - s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Gt = p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)` THEN
  SUBGOAL_THEN `(\x. vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                       (at x)) continuous_on interval[lift s1,lift s]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M. !r. s1 <= r /\ r <= s
            ==> norm(vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                       (at (lift r))) <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\x. vector_derivative
                               (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (at x))
                        (interval[lift s1,lift s])` COMPACT_IMP_BOUNDED) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                 `s1:real`; `s:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`; `{}:real->bool`; `sa:real`; `sb':real`;
                 `M:real`] P2A_LINT_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:real`; `O:A->bool`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`r:real`; `O:A->bool`] (MATCH_MP P2AXR_ADMX_SCONT (ASSUME
        `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt x b gamma`))) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `M:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[p2a_cL; LIFT_DROP] THEN
  ABBREV_TAC `En = real_integral (real_interval[s1,s])
                     (\r. norm(vector_derivative
                                (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                (at (lift r))) pow 2)` THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) sa sb'
                  (\r. (Gt:real->real^N->real^N^N)(tt - r pow 2))` ASSUME_TAC THENL
   [EXPAND_TAC "Gt" THEN MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. p2a_llag (Gt:real->real^N->real^N^N) tt r ((phi:A->real^N)((gamma:real->A)(r pow 2)))
                  (vector_derivative (\v:real^1. phi(gamma(drop v pow 2))) (at (lift r))))
      real_integrable_on real_interval[s1,s] /\
    (\r. norm(vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                (at (lift r))) pow 2) real_integrable_on real_interval[s1,s]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THENL
     [MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb':real`;
                     `Gt:real->real^N->real^N^N`; `tt:real`;
                     `\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`; `r:real`]
                    P2A_LLAG_CONT_AT) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL; o_DEF] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_LIFT_POW) THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_LIFT_NORM_COMPOSE) THEN
      REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(c / &2) * En - Kb * (s - s1) <=
    real_integral (real_interval[s1,s])
      (\r. p2a_llag (Gt:real->real^N->real^N^N) tt r ((phi:A->real^N)((gamma:real->A)(r pow 2)))
                    (vector_derivative (\v:real^1. phi(gamma(drop v pow 2))) (at (lift r))))`
  ASSUME_TAC THENL
   [EXPAND_TAC "En" THEN
    SUBGOAL_THEN `Kb * (s - s1) = real_integral (real_interval[s1,s]) (\r:real. Kb)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL] THEN
    W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUB o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[P2A_LLAG_SPLIT] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`r:real`; `vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                   (at (lift r))`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `c:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kb:real`)) (concl th))) THEN
    EXPAND_TAC "Gt" THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`; `s1:real`; `s:real`]
                P2A_CS_DISPLACEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s - s1) * En` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `En <= (&2 / c) *
                (real_integral (real_interval[s1,s])
                   (\r. p2a_llag (Gt:real->real^N->real^N^N) tt r
                          ((phi:A->real^N)((gamma:real->A)(r pow 2)))
                          (vector_derivative (\v:real^1. phi(gamma(drop v pow 2))) (at (lift r)))) +
                 Kb * (s - s1))`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < c / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!X. &2 / c * X = X / (c / &2)` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= s - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let P2AXS_JCURVE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s1 sa sb' p.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < sqrt b /\ sa < s1 /\ sqrt b < sb' /\
     (!s. sa < s /\ s < sb' ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     gamma(s1 pow 2) IN U INTER W /\
     (!s. s1 <= s /\ s <= sqrt b
          ==> phi(gamma(s1 pow 2)) + (inv(sqrt b - s1) * (s - s1)) % (p - phi(gamma(s1 pow 2)))
              IN IMAGE phi (U INTER W))
     ==> p2a_admx V tt x b (p2a_jcurve gamma U W phi s1 (sqrt b) p) /\
         p2a_jcurve gamma U W phi s1 (sqrt b) p b = chart_inv (U INTER W,phi) p /\
         p2a_L_length V tt (p2a_jcurve gamma U W phi s1 (sqrt b) p) b =
         p2a_L_length V tt gamma (s1 pow 2) +
         p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt
                (\v. phi(gamma(s1 pow 2)) +
                     (inv(sqrt b - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2))))
                s1 (sqrt b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b pow 2 = b /\ &0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < b` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                             (inv(sqrt b - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2)))`;
                 `s1:real`; `sqrt b`; `sa:real`; `sb':real`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `inv(sqrt b - s1) % ((p:real^N) - phi((gamma:real->A)(s1 pow 2)))` THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. vector_derivative
             (\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                         (inv(sqrt b - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2))))
             (at v)) =
      (\v. inv(sqrt b - s1) % ((p:real^N) - phi(gamma(s1 pow 2))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      REWRITE_TAC[CONTINUOUS_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`;
                 `\tau. chart_inv (U INTER W,phi:A->real^N)
                          ((phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                           (inv(sqrt b - s1) * (sqrt tau - s1)) % (p - phi(gamma(s1 pow 2))))`;
                 `gamma:real->A`; `p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 (sqrt b) p`;
                 `b:real`; `s1 pow 2`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AXR_ADMX_RESTRICT THEN EXISTS_TAC `b:real` THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[p2a_jcurve];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_jcurve] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2a_jcurve] THEN
    SUBGOAL_THEN `~(b <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `inv(sqrt b - s1) * (sqrt b - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_integral")) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let P2AXS_END_DISP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) sa sb' s1 c Kp eps.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < sqrt b /\ sa < s1 /\ sqrt b < sb' /\
     (!r. sa < r /\ r < sb' ==> a' < tt - r pow 2 /\ tt - r pow 2 <= b'') /\
     (!r. s1 <= r /\ r <= sqrt b ==> gamma(r pow 2) IN U INTER W) /\
     (!r. s1 <= r /\ r < sqrt b
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift r)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift r))) /\
     &0 < c /\
     (!r A. s1 <= r /\ r <= sqrt b
            ==> c * norm A pow 2 <=
                A dot (p2a_rlocal V W b'' (U INTER W,phi) (tt - r pow 2)
                         (phi(gamma(r pow 2))) ** A)) /\
     (!r. s1 <= r /\ r <= sqrt b
          ==> abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt r
                           (phi(gamma(r pow 2))) (vec 0)) <= Kp) /\
     (!s. s1 <= s /\ s <= sqrt b
          ==> real_integral (real_interval[s1 pow 2,s pow 2]) (p2a_L_integrand V tt gamma b)
              <= c * eps / &4) /\
     Kp * (sqrt b - s1) <= c * eps / &4 /\ &0 < eps
     ==> norm(phi(gamma b) - phi(gamma(s1 pow 2))) pow 2 <= &4 * eps * (sqrt b - s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b pow 2 = b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kp:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the bound strictly before the end point *)
  SUBGOAL_THEN
   `!s. s1 < s /\ s < sqrt b
        ==> norm((phi:A->real^N)((gamma:real->A)(s pow 2)) - phi(gamma(s1 pow 2))) pow 2 <=
            eps * (sqrt b - s1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `sa:real`; `sb':real`; `s1:real`; `s:real`; `c:real`; `Kp:real`]
                  P2AXS_END_ENERGY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 / c) * (s - s1) * (c * eps / &4 + c * eps / &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kp * (sqrt b - s1)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(&2 / c) * (s - s1) * (c * eps / &4 + c * eps / &4) = eps * (s - s1)`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity of the chart curve at the end point *)
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift s1,lift(sqrt b)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `s1:real`; `sqrt b`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2AXR_ADMX_SCONT (ASSUME
      `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`); REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `zeta = sqrt(eps * (sqrt b - s1))` THEN
  SUBGOAL_THEN `&0 < zeta /\ zeta pow 2 = eps * (sqrt b - s1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zeta" THEN
    SUBGOAL_THEN `&0 < eps * (sqrt b - s1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift s1,lift(sqrt b)]` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(sqrt b)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `zeta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = sqrt b - min dl (sqrt b - s1) / &2` THEN
  SUBGOAL_THEN `s1 < s /\ s < sqrt b /\ dist(lift s,lift(sqrt b)) < dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `dl:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `eps:real`)) (concl th) &&
    not(can (find_term ((=) `c:real`)) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((phi:A->real^N)((gamma:real->A)(s pow 2)) - phi(gamma(s1 pow 2))) <= zeta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * zeta) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!z:real^N. norm(y - z) < e /\ norm(z - w) <= e ==> norm(y - w) <= &2 * e`) THEN
    EXISTS_TAC `(phi:A->real^N)((gamma:real->A)(s pow 2))` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The displacement of the region-chart curve after a point s0 where it may  *)
(* be singular (mirror of P2AXS_END_DISP): C^1 on (s0,s2], the L-integrals  *)
(* over [s^2,s2^2] small, give |Y(s2) - Y(s0)|^2 <= 4 eps (s2 - s0).         *)

let P2AXS_START_DISP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) sa sb' s0 s2 c Kp eps.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s0 /\ s0 < s2 /\ s2 pow 2 <= b /\ sa < s0 /\ s2 < sb' /\
     (!r. sa < r /\ r < sb' ==> a' < tt - r pow 2 /\ tt - r pow 2 <= b'') /\
     (!r. s0 <= r /\ r <= s2 ==> gamma(r pow 2) IN U INTER W) /\
     (!r. s0 < r /\ r <= s2
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift r)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift r))) /\
     &0 < c /\
     (!r A. s0 <= r /\ r <= s2
            ==> c * norm A pow 2 <=
                A dot (p2a_rlocal V W b'' (U INTER W,phi) (tt - r pow 2)
                         (phi(gamma(r pow 2))) ** A)) /\
     (!r. s0 <= r /\ r <= s2
          ==> abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt r
                           (phi(gamma(r pow 2))) (vec 0)) <= Kp) /\
     (!s. s0 <= s /\ s <= s2
          ==> real_integral (real_interval[s pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b)
              <= c * eps / &4) /\
     Kp * (s2 - s0) <= c * eps / &4 /\ &0 < eps
     ==> norm(phi(gamma(s2 pow 2)) - phi(gamma(s0 pow 2))) pow 2 <= &4 * eps * (s2 - s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kp:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the bound strictly after the start point *)
  SUBGOAL_THEN
   `!s. s0 < s /\ s < s2
        ==> norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s pow 2))) pow 2 <=
            eps * (s2 - s0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `sa:real`; `sb':real`; `s:real`; `s2:real`; `c:real`; `Kp:real`]
                  P2AXS_END_ENERGY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 / c) * (s2 - s) * (c * eps / &4 + c * eps / &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "real_integral"))
              (concl th))) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kp * (s2 - s0)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(&2 / c) * (s2 - s) * (c * eps / &4 + c * eps / &4) = eps * (s2 - s)`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity of the chart curve at the start point *)
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift s0,lift s2]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `s0:real`; `s2:real`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2AXR_ADMX_SCONT (ASSUME
      `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`); REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `zeta = sqrt(eps * (s2 - s0))` THEN
  SUBGOAL_THEN `&0 < zeta /\ zeta pow 2 = eps * (s2 - s0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zeta" THEN
    SUBGOAL_THEN `&0 < eps * (s2 - s0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift s0,lift s2]` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `lift s0`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `zeta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = s0 + min dl (s2 - s0) / &2` THEN
  SUBGOAL_THEN `s0 < s /\ s < s2 /\ dist(lift s,lift s0) < dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `dl:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `eps:real`)) (concl th) &&
    not(can (find_term ((=) `c:real`)) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s pow 2))) <= zeta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * zeta) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!z:real^N. norm(y - z) <= e /\ norm(z - w) < e ==> norm(y - w) <= &2 * e`) THEN
    EXISTS_TAC `(phi:A->real^N)((gamma:real->A)(s pow 2))` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Curves with bad corners.  p2axs_pc1b V tt gamma a b P B: the conditions   *)
(* of p2a_pc1 with corner set P hold at every time outside the finite bad    *)
(* set B.  p2a_pc1 is the case B = {}; a p2a_pc1x curve with corner set P    *)
(* has bad set P.  Gluing at a regular time.                                 *)
(* ------------------------------------------------------------------------- *)

let p2axs_pc1b = new_definition
 `p2axs_pc1b (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) (tt:real) (gamma:real->A) (a:real) (b:real)
             (P:real->bool) (B:real->bool) <=>
    FINITE P /\ FINITE B /\
    !s0 c. a < s0 /\ s0 <= b /\ ~(s0 IN B) /\ c IN p2a_vatlas V (tt - s0) /\
           gamma s0 IN FST c
           ==> ?d. &0 < d /\
                   continuously_differentiable 1
                     {s | s0 - d <= drop s /\ drop s <= s0 /\ a < drop s /\
                          p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\
                          gamma(drop s) IN FST c}
                     (\s. SND c (gamma(drop s))) /\
                   continuously_differentiable 1
                     {s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= b /\
                          p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\
                          gamma(drop s) IN FST c}
                     (\s. SND c (gamma(drop s))) /\
                   (~(s0 IN P)
                    ==> continuously_differentiable 1
                          {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                               a < drop s /\ drop s <= b /\
                               p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\
                               gamma(drop s) IN FST c}
                          (\s. SND c (gamma(drop s))))`;;

let P2AXS_PC1B_EMPTY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma a b P.
     p2axs_pc1b V tt gamma a b P {} <=> p2a_pc1 V tt gamma a b P`,
  REWRITE_TAC[p2axs_pc1b; p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY]);;

let P2AXS_PC1X_PC1B = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) a b P.
     p2a_pc1x V tt gamma a b P ==> p2axs_pc1b V tt gamma a b P P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1x; p2axs_pc1b] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY DISCH_TAC THEN
  USE_THEN "T" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Shrinking the bad set to its part in (a,b].                              *)

let P2AXS_PC1B_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) a b P B B'.
     p2axs_pc1b V tt gamma a b P B /\ FINITE B' /\
     (!s. a < s /\ s <= b /\ s IN B ==> s IN B')
     ==> p2axs_pc1b V tt gamma a b P B'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2axs_pc1b] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "continuously_differentiable"))
        (concl th))) THEN
  ASM_MESON_TAC[]);;

let P2AXS_PC1B_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) a b b' P B.
     p2axs_pc1b V tt gamma a b P B /\ b' <= b ==> p2axs_pc1b V tt gamma a b' P B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2axs_pc1b] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "G"))) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "R") (LABEL_TAC "T")))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "R" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    USE_THEN "T" (MP_TAC o C MP (ASSUME `~((s0:real) IN P)`)) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let P2AXS_PC1B_RAISE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) a a' b P B.
     p2axs_pc1b V tt gamma a b P B /\ a <= a' ==> p2axs_pc1b V tt gamma a' b P B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2axs_pc1b] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "G"))) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T")))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "L" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    USE_THEN "T" (MP_TAC o C MP (ASSUME `~((s0:real) IN P)`)) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Gluing at a regular time b' (not bad for the first piece; the second    *)
(* piece is C^1 from the right at b').                                      *)

let P2AXS_GLUE_PC1B = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) gamma' gg a b b' P P' B B'.
        p2axs_pc1b V tt gamma b' b P B /\
        (!c. c IN p2a_vatlas V (tt - b') /\ gamma b' IN FST c
             ==> ?d. &0 < d /\
                     continuously_differentiable 1
                       {s | b' <= drop s /\ drop s <= b' + d /\ drop s <= b /\
                            p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - b') /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s)))) /\
        p2axs_pc1b V tt gamma' a b' P' B' /\ ~(b' IN B') /\
        a < b' /\ b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2axs_pc1b V tt gg a b (b' INSERT (P UNION P')) (B UNION B')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2axs_pc1b] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "G")))
   (CONJUNCTS_THEN2 (LABEL_TAC "RB")
   (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "G'")))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "E2")))))))) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s0 < b'` THENL
   [SUBGOAL_THEN `(gamma':real->A) s0 IN FST(c:(A->bool)#(A->real^N))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) s0 = gamma' s0` (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "G'" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "R1")
      (LABEL_TAC "T1"))))) THEN
    MP_TAC(SPECL [`d1:real`; `(b' - s0) / &2`] REAL_DOWN2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
      USE_THEN "R1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
      STRIP_TAC THEN
      USE_THEN "T1" (MP_TAC o C MP (ASSUME `~((s0:real) IN P')`)) THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER)] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma'(drop s)` SUBST_ALL_TAC THENL
      [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s0:real = b'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(gamma':real->A) b' IN FST(c:(A->bool)#(A->real^N)) /\
                  (gamma:real->A) b' IN FST c` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) b' = gamma' b' /\ (gg:real->A) b' = gamma b'`
        (fun th -> ASM_MESON_TAC[th]) THEN
      CONJ_TAC THENL [USE_THEN "E1" MATCH_MP_TAC; USE_THEN "E2" MATCH_MP_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "G'" (MP_TAC o SPECL [`b':real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "L1") (K ALL_TAC)))) THEN
    USE_THEN "RB" (MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2"))) THEN
    MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gg:real->A)(drop s) = gamma'(drop s)` SUBST_ALL_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "R2" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gg:real->A)(drop s) = gamma(drop s)` SUBST_ALL_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `b' < s0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s0 IN FST(c:(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real->A) s0 = gamma s0` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "R1")
    (LABEL_TAC "T1"))))) THEN
  MP_TAC(SPECL [`d1:real`; `(s0 - b') / &2`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    USE_THEN "R1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    STRIP_TAC THEN
    USE_THEN "T1" (MP_TAC o C MP (ASSUME `~((s0:real) IN P)`)) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER)] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma(drop s)` SUBST_ALL_TAC THENL
    [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* Removing one bad corner.  The displacement before an interior point       *)
(* (P2AXS_MID_DISP, as P2AXS_END_DISP); a bad corner at an interior time is  *)
(* cut out by a chart segment between two nearby regular times               *)
(* (P2AXS_INT_STEP), a bad corner at the end point by a chart segment to the *)
(* end point (P2AXS_END_STEP); the L-length grows by at most e.              *)
(* ------------------------------------------------------------------------- *)

let P2AXS_MID_DISP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) sa sb' s1 s0 c Kp eps.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s0 /\ s0 pow 2 <= b /\ sa < s1 /\ s0 < sb' /\
     (!r. sa < r /\ r < sb' ==> a' < tt - r pow 2 /\ tt - r pow 2 <= b'') /\
     (!r. s1 <= r /\ r <= s0 ==> gamma(r pow 2) IN U INTER W) /\
     (!r. s1 <= r /\ r < s0
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift r)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift r))) /\
     &0 < c /\
     (!r A. s1 <= r /\ r <= s0
            ==> c * norm A pow 2 <=
                A dot (p2a_rlocal V W b'' (U INTER W,phi) (tt - r pow 2)
                         (phi(gamma(r pow 2))) ** A)) /\
     (!r. s1 <= r /\ r <= s0
          ==> abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt r
                           (phi(gamma(r pow 2))) (vec 0)) <= Kp) /\
     (!s. s1 <= s /\ s <= s0
          ==> real_integral (real_interval[s1 pow 2,s pow 2]) (p2a_L_integrand V tt gamma b)
              <= c * eps / &4) /\
     Kp * (s0 - s1) <= c * eps / &4 /\ &0 < eps
     ==> norm(phi(gamma(s0 pow 2)) - phi(gamma(s1 pow 2))) pow 2 <= &4 * eps * (s0 - s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kp:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the bound strictly before the end point *)
  SUBGOAL_THEN
   `!s. s1 < s /\ s < s0
        ==> norm((phi:A->real^N)((gamma:real->A)(s pow 2)) - phi(gamma(s1 pow 2))) pow 2 <=
            eps * (s0 - s1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `sa:real`; `sb':real`; `s1:real`; `s:real`; `c:real`; `Kp:real`]
                  P2AXS_END_ENERGY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s0:real) pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 / c) * (s - s1) * (c * eps / &4 + c * eps / &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kp * (s0 - s1)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(&2 / c) * (s - s1) * (c * eps / &4 + c * eps / &4) = eps * (s - s1)`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity of the chart curve at the end point *)
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift s1,lift s0]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `s1:real`; `s0:real`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2AXR_ADMX_SCONT (ASSUME
      `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`); REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `zeta = sqrt(eps * ((s0:real) - s1))` THEN
  SUBGOAL_THEN `&0 < zeta /\ zeta pow 2 = eps * (s0 - s1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zeta" THEN
    SUBGOAL_THEN `&0 < eps * (s0 - s1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift s1,lift s0]` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(s0:real)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `zeta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = (s0:real) - min dl (s0 - s1) / &2` THEN
  SUBGOAL_THEN `s1 < s /\ s < s0 /\ dist(lift s,lift s0) < dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `dl:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `eps:real`)) (concl th) &&
    not(can (find_term ((=) `c:real`)) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((phi:A->real^N)((gamma:real->A)(s pow 2)) - phi(gamma(s1 pow 2))) <= zeta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * zeta) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!z:real^N. norm(y - z) < e /\ norm(z - w) <= e ==> norm(y - w) <= &2 * e`) THEN
    EXISTS_TAC `(phi:A->real^N)((gamma:real->A)(s pow 2))` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Bookkeeping for the replacement of [b1,b2] by a segment sig: the bad set *)
(* loses its points in (b1,b2].                                              *)

let P2AXS_REPLACE_PC1B = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) sig b b1 b2 P B.
     p2axs_pc1b V tt gamma (&0) b P B /\ p2a_lseg V tt b1 b2 sig /\
     b2 < b /\ ~(b1 IN B) /\ ~(b2 IN B) /\ sig b1 = gamma b1 /\ sig b2 = gamma b2
     ==> ?P'. p2axs_pc1b V tt
                (\tau. if tau <= b1 then gamma tau else if tau <= b2 then sig tau
                       else gamma tau)
                (&0) b P' {s | s IN B /\ (s <= b1 \/ b2 < s)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_lseg]) THEN
  SUBGOAL_THEN `FINITE (B:real->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2axs_pc1b]; ALL_TAC] THEN
  ABBREV_TAC `Bl = {s:real | s IN B /\ s <= b1}` THEN
  ABBREV_TAC `Br = {s:real | s IN B /\ b2 < s}` THEN
  SUBGOAL_THEN `FINITE (Bl:real->bool) /\ FINITE (Br:real->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Bl"; "Br"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the first glue, at b1 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `sig:real->A`; `gamma:real->A`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else sig tau`;
                 `&0`; `b2:real`; `b1:real`; `P':real->bool`; `P:real->bool`;
                 `{}:real->bool`; `Bl:real->bool`] P2AXS_GLUE_PC1B) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2AXS_PC1B_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AXS_PC1B_MONO THEN EXISTS_TAC `B:real->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2AXS_PC1B_RESTRICT THEN EXISTS_TAC `b:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Bl" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
      EXPAND_TAC "Bl" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      SIMP_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau:real = b1` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    DISCH_TAC] THEN
  (* the second glue, at b2 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else sig tau`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else if tau <= b2 then sig tau
                        else gamma tau`;
                 `&0`; `b:real`; `b2:real`; `P:real->bool`;
                 `b1 INSERT ((P':real->bool) UNION P)`;
                 `Br:real->bool`; `({}:real->bool) UNION Bl`] P2AXS_GLUE_PC1B) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AXS_PC1B_MONO THEN EXISTS_TAC `B:real->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2AXS_PC1B_RAISE THEN EXISTS_TAC `&0` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Br" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`b2:real`; `c:(A->bool)#(A->real^N)`] o CONJUNCT2 o
        CONJUNCT2 o GEN_REWRITE_RULE I [p2axs_pc1b] o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2axs_pc1b")) (concl th) &&
          can (find_term ((=) `B:real->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
      REWRITE_TAC[IN_UNION; NOT_IN_EMPTY] THEN EXPAND_TAC "Bl" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(tau <= b1)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau:real = b2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    DISCH_TAC] THEN
  EXISTS_TAC `b2 INSERT (P UNION b1 INSERT ((P':real->bool) UNION P))` THEN
  MATCH_MP_TAC P2AXS_PC1B_MONO THEN
  EXISTS_TAC `(Br:real->bool) UNION ({} UNION Bl)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXPAND_TAC ["Bl"; "Br"] THEN
    REWRITE_TAC[IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* Two arithmetic facts for the segment: the parameter of an affine         *)
(* segment lies in [0,1], and the cost bound of P2A_ZPIECE_LENGTH for a     *)
(* displacement d with norm d pow 2 <= 8 eps (s2 - s1).                     *)

let P2AXS_UNIT_PARAM = prove
 (`!a b s. a < b /\ a <= s /\ s <= b
           ==> &0 <= inv(b - a) * (s - a) /\ inv(b - a) * (s - a) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC);;

let P2AXS_ZBOUND = prove
 (`!(d:real^N) s1 s2 Cg Kp eps e1 e2.
     s1 < s2 /\ &0 <= Cg /\ norm d pow 2 <= &8 * eps * (s2 - s1) /\
     &4 * Cg * eps <= e1 /\ (s2 - s1) * Kp <= e2
     ==> (s2 - s1) * (inv(&2) * Cg * norm(inv(s2 - s1) % d) pow 2 + Kp) <= e1 + e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s2 - s1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `norm(d:real^N) pow 2 <= &8 * eps * (s2 - s1)` THEN
  UNDISCH_TAC `(s2 - s1) * Kp <= e2` THEN
  SPEC_TAC(`s2 - s1`,`h:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
  SUBGOAL_THEN `h * (inv(&2) * Cg * (inv h pow 2 * norm(d:real^N) pow 2) + Kp) =
                (Cg * norm d pow 2) * inv(&2 * h) + h * Kp` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= e1 /\ b <= e2 ==> a + b <= e1 + e2`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Cg * &8 * eps * h) * inv(&2 * h)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(Cg * &8 * eps * h) * inv(&2 * h) = &4 * Cg * eps` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* One interior bad corner tau0 = s0 pow 2 in (0,b) is cut out: in a region *)
(* chart at the corner the curve is replaced on [s1 pow 2,s2 pow 2], with   *)
(* s1 = s0 - k and s2 = s0 + k regular, by the chart segment between its    *)
(* end values.  The displacements on both sides are O(sqrt(eps k))          *)
(* (P2AXS_MID_DISP, P2AXS_START_DISP), so the segment costs at most         *)
(* 4 Cg eps + 2 k Kp, and the removed piece has small integral.             *)
(* ------------------------------------------------------------------------- *)

let P2AXS_INT_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) P B tau0 e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\
     p2axs_pc1b V tt gamma (&0) b P B /\ &0 < tau0 /\ tau0 < b /\ &0 < e
     ==> ?gamma1 P1. p2a_admx V tt x b gamma1 /\
                     p2axs_pc1b V tt gamma1 (&0) b P1 (B DELETE tau0) /\
                     gamma1 b = gamma b /\
                     p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (P:real->bool) /\ FINITE (B:real->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2axs_pc1b (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt gamma (&0) b P B` THEN
    REWRITE_TAC[p2axs_pc1b] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?s0. &0 < s0 /\ s0 pow 2 = tau0` (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC)
  THENL
   [EXISTS_TAC `sqrt tau0` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b /\ s0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LE];
    ALL_TAC] THEN
  (* the region chart at the corner and the punctured window *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `s0:real`] P2AXR_REGION_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `s0:real`]
                P2AXR_MINX_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))))) THEN
  ABBREV_TAC `h1 = min h (min s0 (sqrt b - s0)) / &2` THEN
  SUBGOAL_THEN `&0 < h1 /\ h1 < h /\ h1 < s0 /\ s0 + h1 < sqrt b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `min h (min s0 (sqrt b - s0)) / &2 = h1` (K ALL_TAC) THEN
  SUBGOAL_THEN `!s. s0 - h1 < s /\ s < s0 + h1 ==> a' < tt - s pow 2 /\ tt - s pow 2 < b''`
  (LABEL_TAC "WIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(s = &0)` (fun th -> SIMP_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - h1 < s /\ s < s0 + h1 ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  (LABEL_TAC "WINLE") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - h1 <= s /\ s <= s0 + h1 ==> s pow 2 < b` (LABEL_TAC "SB") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - h1 <= s /\ s <= s0 + h1 ==> (gamma:real->A)(s pow 2) IN U INTER W`
  (LABEL_TAC "MEM") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H2" MATCH_MP_TAC THEN
    USE_THEN "SB" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s0 - h1 <= s /\ s <= s0 + h1 /\ ~(s = s0)
        ==> (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) differentiable (at (lift s)) /\
            (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
              continuous (at (lift s))`
  (LABEL_TAC "C1") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H3" MATCH_MP_TAC THEN
    USE_THEN "SB" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s0 - h1) (s0 + h1)
                  (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `?rho0. &0 < rho0 /\
                       cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0) SUBSET
                       IMAGE phi (U INTER W)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[p2a_lsmooth] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th))) THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - h1`; `s0 + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)`;
                 `s0 - h1 / &2`; `s0 + h1 / &2`] P2A_LSMOOTH_QUAD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `Cg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QB"))))) THEN
  SUBGOAL_THEN `&0 <= Cg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - h1`; `s0 + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)`;
                 `s0 - h1 / &2`; `s0 + h1 / &2`; `&0`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB")) THEN
  ABBREV_TAC `Kp = abs Kb` THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL [EXPAND_TAC "Kp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. s0 - h1 / &2 <= s /\ s <= s0 + h1 / &2 /\
          y IN cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)
          ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b''
                 (U INTER W,phi)) tt s y (vec 0)) <= Kp`
  (LABEL_TAC "KP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Kp" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN USE_THEN "KB" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_0; REAL_LE_REFL];
    ALL_TAC]) THEN
  UNDISCH_THEN `abs Kb = Kp` (K ALL_TAC) THEN
  (SUBGOAL_THEN `?eps. &0 < eps /\ eps * (&16 * (Cg + &1)) = e`
  (X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / (&16 * (Cg + &1))` THEN
    SUBGOAL_THEN `&0 < &16 * (Cg + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN UNDISCH_TAC `&0 < &16 * (Cg + &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * Cg * eps <= e / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min (e / &8) (c * eps / &4)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= e / &8 /\ eta <= c * eps / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < c * eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  UNDISCH_THEN `min (e / &8) (c * eps / &4) = eta` (K ALL_TAC) THEN
  (SUBGOAL_THEN `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) tt gamma b
                real_integrable_on real_interval[&0,b]` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN DISCH_THEN(ACCEPT_TAC o last o CONJUNCTS); ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) tt gamma b`;
                 `&0`; `b:real`; `s0 pow 2`; `s0 pow 2`; `eta:real`]
                REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_INTEGRAL_REFL;
               REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KAP"))) THEN
  MP_TAC(SPECL [`s0:real`; `kap:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hk:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HK")))) THEN
  (SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(s0 - h1 / &2),lift(s0 + h1 / &2)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `s0 - h1 / &2`; `s0 + h1 / &2`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2AXR_ADMX_SCONT (ASSUME
      `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`)] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "WINLE" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift(s0 - h1 / &2),lift(s0 + h1 / &2)]` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `lift s0`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rho0 / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DY")))) THEN
  (MP_TAC(ISPECL [`s0 pow 2`; `(P:real->bool) UNION B`] P2A_REAL_FINITE_AVOID) THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `dP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DP"))) THEN
  MP_TAC(SPECL [`s0:real`; `dP:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HP"))) THEN
  MP_TAC(SPECL [`min (c * eps / &4) (e / &8)`; `Kp:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &4`]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KA"))) THEN
  ABBREV_TAC `k = min (min (h1 / &2) (min hk hP)) (min dy ka) / &4` THEN
  SUBGOAL_THEN `&0 < k /\ &2 * k <= ka /\ k < h1 / &2 /\ k < hk /\ k < hP /\ k < dy`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  UNDISCH_THEN `min (min (h1 / &2) (min hk hP)) (min dy ka) / &4 = k` (K ALL_TAC) THEN
  (ABBREV_TAC `s1 = s0 - k` THEN ABBREV_TAC `s2 = s0 + k` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < s0 /\ s0 < s2 /\ s1 < s2 /\ s0 - h1 < s1 /\ s2 < s0 + h1 /\
                s0 - h1 / &2 <= s1 /\ s2 <= s0 + h1 / &2`
  STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < s0 pow 2 /\ s0 pow 2 < s2 pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 pow 2 < b` ASSUME_TAC THENL
   [USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `!r. s1 <= r /\ r <= s2
                    ==> dist((phi:A->real^N)((gamma:real->A)(r pow 2)),phi(gamma(s0 pow 2))) <
                        rho0 / &4`
  (LABEL_TAC "YB") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "DY" (MP_TAC o SPEC `lift r`) THEN
    REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!r. s1 <= r /\ r <= s2
                    ==> (phi:A->real^N)((gamma:real->A)(r pow 2)) IN
                        cball(phi(gamma(s0 pow 2)),rho0)`
  (LABEL_TAC "YC") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    USE_THEN "YB" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!r A. s1 <= r /\ r <= s2
          ==> c * norm A pow 2 <=
              A dot (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)
                       (tt - r pow 2) (phi((gamma:real->A)(r pow 2))) ** A)`
  (LABEL_TAC "QBL") THENL
   [MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
    USE_THEN "QB" (MP_TAC o SPECL [`r:real`; `(phi:A->real^N)((gamma:real->A)(r pow 2))`;
                                   `A:real^N`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        USE_THEN "YC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!r. s1 <= r /\ r <= s2
        ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                        (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N))
                         tt r (phi((gamma:real->A)(r pow 2))) (vec 0)) <= Kp`
  (LABEL_TAC "KPL") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KP" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "YC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!u v. s1 <= u /\ u <= s2 /\ s1 <= v /\ v <= s2
          ==> abs(real_integral (real_interval[u pow 2,v pow 2])
                    (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                        (real->A->real^N^N)) tt gamma b)) < eta`
  (LABEL_TAC "INT") THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    USE_THEN "KAP" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `Kp * (s0 - s1) <= c * eps / &4 /\ Kp * (s2 - s0) <= c * eps / &4 /\
                (s2 - s1) * Kp <= e / &8` STRIP_ASSUME_TAC THENL
   [USE_THEN "KA" (MP_TAC o SPEC `k:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "KA" (MP_TAC o SPEC `&2 * k`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1 pow 2 IN B) /\ ~(s2 pow 2 IN B)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "DP" (MP_TAC o SPEC `s1 pow 2`) THEN
      USE_THEN "HP" (MP_TAC o SPEC `s1:real`) THEN
      ANTS_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "DP" (MP_TAC o SPEC `s2 pow 2`) THEN
      USE_THEN "HP" (MP_TAC o SPEC `s2:real`) THEN
      ANTS_TAC THENL [EXPAND_TAC "s2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - h1`; `s0 + h1`; `s1:real`; `s0:real`; `c:real`; `Kp:real`; `eps:real`]
                P2AXS_MID_DISP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "C1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QBL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KPL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x < y ==> x <= y`) THEN
      USE_THEN "INT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "D1")]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - h1`; `s0 + h1`; `s0:real`; `s2:real`; `c:real`; `Kp:real`; `eps:real`]
                P2AXS_START_DISP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "C1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QBL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KPL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x < y ==> x <= y`) THEN
      USE_THEN "INT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "D2")]) THEN
  (SUBGOAL_THEN
   `norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))) pow 2 <=
    &8 * eps * (s2 - s1)` (LABEL_TAC "D") THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s0 pow 2))) +
                 norm((phi:A->real^N)((gamma:real->A)(s0 pow 2)) - phi(gamma(s1 pow 2)))) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s0 pow 2))) pow 2 +
                      norm((phi:A->real^N)((gamma:real->A)(s0 pow 2)) - phi(gamma(s1 pow 2))) pow 2)` THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s0 pow 2))) -
                   norm((phi:A->real^N)((gamma:real->A)(s0 pow 2)) - phi(gamma(s1 pow 2)))`
                  REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      USE_THEN "D1" MP_TAC THEN USE_THEN "D2" MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
            (inv(s2 - s1) * (s - s1)) % (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))) IN
            cball(phi(gamma(s0 pow 2)),rho0)`
  (LABEL_TAC "ZIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(s0 pow 2))`; `rho0:real`] CONVEX_CBALL) THEN
    REWRITE_TAC[CONVEX_ALT] THEN
    DISCH_THEN(MP_TAC o SPECL [`(phi:A->real^N)((gamma:real->A)(s1 pow 2))`;
                               `(phi:A->real^N)((gamma:real->A)(s2 pow 2))`;
                               `inv(s2 - s1) * (s - s1)`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "YC" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "YC" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPECL [`s1:real`; `s2:real`; `s:real`] P2AXS_UNIT_PARAM) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MP_TAC(SPECL [`s1:real`; `s2:real`; `s:real`] P2AXS_UNIT_PARAM) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC]) THEN
  (ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N)
                       ((phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                        (inv(s2 - s1) * (sqrt tau - s1)) %
                        (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))))` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                             (inv(s2 - s1) * (drop v - s1)) %
                             (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2)))`;
                 `s1:real`; `s2:real`; `s0 - h1`; `s0 + h1`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        not(is_forall(concl th)))) THEN
      USE_THEN "ZIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `inv(s2 - s1) % ((phi:A->real^N)((gamma:real->A)(s2 pow 2)) -
                                  phi(gamma(s1 pow 2)))` THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. vector_derivative
             (\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                         (inv(s2 - s1) * (drop v - s1)) %
                         (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))))
             (at v)) =
      (\v. inv(s2 - s1) % ((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      REWRITE_TAC[CONTINUOUS_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LSEG") (LABEL_TAC "HRI"))) THEN
  (SUBGOAL_THEN `(sig:real->A) (s1 pow 2) = (gamma:real->A)(s1 pow 2) /\
                sig (s2 pow 2) = gamma(s2 pow 2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `inv(s2 - s1) * (s2 - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `y1 + &1 % (y2 - y1):real^N = y2`] THEN
    CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `sig:real->A`;
                 `b:real`; `s1 pow 2`; `s2 pow 2`] P2AXR_REPLACE_X) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ADM1") (LABEL_TAC "LEN1"))] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `sig:real->A`;
                 `b:real`; `s1 pow 2`; `s2 pow 2`; `P:real->bool`; `B:real->bool`]
                P2AXS_REPLACE_PC1B) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P1:real->bool` (LABEL_TAC "PB1"))) THEN
  (SUBGOAL_THEN
   `real_integral (real_interval[s1 pow 2,s2 pow 2])
      (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt sig (s2 pow 2)) =
    p2a_cL (p2a_rlocal V W b'' (U INTER W,phi:A->real^N)) tt
      (\v. phi((gamma:real->A)(s1 pow 2)) +
           (inv(s2 - s1) * (drop v - s1)) % (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))))
      s1 s2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN USE_THEN "HRI" ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - h1`; `s0 + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `(phi:A->real^N)((gamma:real->A)(s1 pow 2))`;
                 `(phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))`;
                 `inv(s2 - s1)`; `s1:real`; `s2:real`;
                 `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)`; `Cg:real`; `Kp:real`]
                P2A_ZPIECE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QB" (MP_TAC o SPECL [`s:real`; `y:real^N`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "KP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))`;
                 `s1:real`; `s2:real`; `Cg:real`; `Kp:real`; `eps:real`; `e / &4`; `e / &8`]
                P2AXS_ZBOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  USE_THEN "INT" (MP_TAC o SPECL [`s1:real`; `s2:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  EXISTS_TAC `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau
                    else if tau <= s2 pow 2 then (sig:real->A) tau else gamma tau` THEN
  EXISTS_TAC `P1:real->bool` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ADM1" ACCEPT_TAC;
    MATCH_MP_TAC P2AXS_PC1B_MONO THEN
    EXISTS_TAC `{s:real | s IN B /\ (s <= s1 pow 2 \/ s2 pow 2 < s)}` THEN
    ASM_REWRITE_TAC[FINITE_DELETE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b <= s1 pow 2) /\ ~(b <= s2 pow 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    USE_THEN "LEN1" SUBST1_TAC THEN ASM_REAL_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* A bad corner at the end point b is cut out by a chart segment from a      *)
(* nearby regular time to b (P2AXS_END_STEP, bookkeeping by                  *)
(* P2AXS_ENDREP_PC1B); the induction over the bad set; the smoothing of admx *)
(* curves (P2AXS_SMOOTHING_X).                                               *)
(* ------------------------------------------------------------------------- *)

let P2AXS_ENDREP_PC1B = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) sig b b1 P B.
     p2axs_pc1b V tt gamma (&0) b P B /\ p2a_lseg V tt b1 b sig /\
     ~(b1 IN B) /\ sig b1 = gamma b1
     ==> ?P'. p2axs_pc1b V tt (\tau. if tau <= b1 then gamma tau else sig tau)
                (&0) b P' {s | s IN B /\ s <= b1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_lseg]) THEN
  SUBGOAL_THEN `FINITE (B:real->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2axs_pc1b]; ALL_TAC] THEN
  ABBREV_TAC `Bl = {s:real | s IN B /\ s <= b1}` THEN
  SUBGOAL_THEN `FINITE (Bl:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Bl" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `sig:real->A`; `gamma:real->A`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else sig tau`;
                 `&0`; `b:real`; `b1:real`; `P':real->bool`; `P:real->bool`;
                 `{}:real->bool`; `Bl:real->bool`] P2AXS_GLUE_PC1B) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2AXS_PC1B_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AXS_PC1B_MONO THEN EXISTS_TAC `B:real->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2AXS_PC1B_RESTRICT THEN EXISTS_TAC `b:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Bl" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
      EXPAND_TAC "Bl" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      SIMP_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau:real = b1` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    DISCH_TAC] THEN
  EXISTS_TAC `b1 INSERT ((P':real->bool) UNION P)` THEN
  POP_ASSUM(ACCEPT_TAC o REWRITE_RULE[UNION_EMPTY]));;

let P2AXS_END_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) P B e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\
     p2axs_pc1b V tt gamma (&0) b P B /\ &0 < e
     ==> ?gamma1 P1. p2a_admx V tt x b gamma1 /\
                     p2axs_pc1b V tt gamma1 (&0) b P1 (B DELETE b) /\
                     gamma1 b = gamma b /\
                     p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (P:real->bool) /\ FINITE (B:real->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2axs_pc1b (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt gamma (&0) b P B` THEN
    REWRITE_TAC[p2axs_pc1b] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN DISCH_THEN(ACCEPT_TAC o hd o CONJUNCTS); ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* the region chart at the end point and the punctured window *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `sqrt b`] P2AXR_REGION_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `sqrt b`]
                P2AXR_MINX_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))))) THEN
  SUBGOAL_THEN `?h1. &0 < h1 /\ h1 < h /\ h1 < sqrt b` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min h (sqrt b) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sqrt b - h1 < s /\ s < sqrt b + h1
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 < b''`
  (LABEL_TAC "WIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(s = &0)` (fun th -> SIMP_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. sqrt b - h1 < s /\ s < sqrt b + h1
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  (LABEL_TAC "WINLE") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (sqrt b - h1) (sqrt b + h1)
                  (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?rho0. &0 < rho0 /\
                       cball((phi:A->real^N)((gamma:real->A) b),rho0) SUBSET
                       IMAGE phi (U INTER W)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[p2a_lsmooth] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th))) THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A) b),rho0)`;
                 `sqrt b - h1 / &2`; `sqrt b + h1 / &2`] P2A_LSMOOTH_QUAD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `Cg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QB"))))) THEN
  SUBGOAL_THEN `&0 <= Cg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A) b),rho0)`;
                 `sqrt b - h1 / &2`; `sqrt b + h1 / &2`; `&0`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB")) THEN
  ABBREV_TAC `Kp = abs Kb` THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL [EXPAND_TAC "Kp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. sqrt b - h1 / &2 <= s /\ s <= sqrt b + h1 / &2 /\
          y IN cball((phi:A->real^N)((gamma:real->A) b),rho0)
          ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b''
                 (U INTER W,phi)) tt s y (vec 0)) <= Kp`
  (LABEL_TAC "KP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Kp" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN USE_THEN "KB" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_0; REAL_LE_REFL];
    ALL_TAC]) THEN
  UNDISCH_THEN `abs Kb = Kp` (K ALL_TAC) THEN
  (SUBGOAL_THEN `?eps. &0 < eps /\ eps * (&16 * (Cg + &1)) = e`
  (X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / (&16 * (Cg + &1))` THEN
    SUBGOAL_THEN `&0 < &16 * (Cg + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN UNDISCH_TAC `&0 < &16 * (Cg + &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * Cg * eps <= e / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min (e / &8) (c * eps / &4)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= e / &8 /\ eta <= c * eps / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < c * eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  UNDISCH_THEN `min (e / &8) (c * eps / &4) = eta` (K ALL_TAC) THEN
  (SUBGOAL_THEN `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) tt gamma b
                real_integrable_on real_interval[&0,b]` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN DISCH_THEN(ACCEPT_TAC o last o CONJUNCTS); ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) tt gamma b`;
                 `&0`; `b:real`; `b:real`; `b:real`; `eta:real`]
                REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE; REAL_INTEGRAL_REFL;
               REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KAP"))) THEN
  MP_TAC(SPECL [`sqrt b`; `kap:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hk:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HK")))) THEN
  (SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(sqrt b - h1 / &2),lift(sqrt b)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `sqrt b - h1 / &2`; `sqrt b`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2AXR_ADMX_SCONT (ASSUME
      `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`); REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "H2" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      USE_THEN "WINLE" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift(sqrt b - h1 / &2),lift(sqrt b)]` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `lift(sqrt b)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rho0 / &4`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DY")))) THEN
  (MP_TAC(ISPECL [`b:real`; `(P:real->bool) UNION B`] P2A_REAL_FINITE_AVOID) THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `dP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DP"))) THEN
  MP_TAC(SPECL [`sqrt b`; `dP:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HP"))) THEN
  MP_TAC(SPECL [`min (c * eps / &4) (e / &8)`; `Kp:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &4`]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KA"))) THEN
  ABBREV_TAC `d1 = min (min (h1 / &2) (min hk hP)) (min dy ka) / &4` THEN
  SUBGOAL_THEN `&0 < d1 /\ d1 <= ka /\ d1 < h1 / &2 /\ d1 < hk /\ d1 < hP /\ d1 < dy`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "d1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `min (min (h1 / &2) (min hk hP)) (min dy ka) / &4 = d1` (K ALL_TAC) THEN
  ABBREV_TAC `s1 = sqrt b - d1` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < sqrt b /\ sqrt b - h1 < s1 /\ sqrt b - h1 / &2 <= s1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < b` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!r. s1 <= r /\ r <= sqrt b
                    ==> dist((phi:A->real^N)((gamma:real->A)(r pow 2)),phi(gamma b)) <
                        rho0 / &4`
  (LABEL_TAC "YB") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "DY" (MP_TAC o SPEC `lift r`) THEN
    REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. s1 <= r /\ r <= sqrt b
                    ==> (phi:A->real^N)((gamma:real->A)(r pow 2)) IN cball(phi(gamma b),rho0)`
  (LABEL_TAC "YC") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    USE_THEN "YB" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. s1 <= r /\ r <= sqrt b ==> (gamma:real->A)(r pow 2) IN U INTER W`
  (LABEL_TAC "MEM") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "H2" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. s1 <= r /\ r < sqrt b
        ==> (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) differentiable (at (lift r)) /\
            (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
              continuous (at (lift r))`
  (LABEL_TAC "C1") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "H3" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!r A. s1 <= r /\ r <= sqrt b
          ==> c * norm A pow 2 <=
              A dot (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)
                       (tt - r pow 2) (phi((gamma:real->A)(r pow 2))) ** A)`
  (LABEL_TAC "QBL") THENL
   [MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
    USE_THEN "QB" (MP_TAC o SPECL [`r:real`; `(phi:A->real^N)((gamma:real->A)(r pow 2))`;
                                   `A:real^N`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        USE_THEN "YC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. s1 <= r /\ r <= sqrt b
        ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                        (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N))
                         tt r (phi((gamma:real->A)(r pow 2))) (vec 0)) <= Kp`
  (LABEL_TAC "KPL") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KP" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "YC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. s1 <= u /\ u <= sqrt b /\ s1 <= v /\ v <= sqrt b
          ==> abs(real_integral (real_interval[u pow 2,v pow 2])
                    (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                        (real->A->real^N^N)) tt gamma b)) < eta`
  (LABEL_TAC "INT") THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    USE_THEN "KAP" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `Kp * (sqrt b - s1) <= c * eps / &4 /\ (sqrt b - s1) * Kp <= e / &8`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "KA" (MP_TAC o SPEC `d1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN EXPAND_TAC "s1" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1 pow 2 IN B)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "DP" (MP_TAC o SPEC `s1 pow 2`) THEN
    USE_THEN "HP" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `sqrt b - h1`; `sqrt b + h1`; `s1:real`; `c:real`; `Kp:real`; `eps:real`]
                P2AXS_END_DISP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x < y ==> x <= y`) THEN
      USE_THEN "INT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "D")]) THEN
  (SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sqrt b
        ==> (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
            (inv(sqrt b - s1) * (s - s1)) % (phi(gamma b) - phi(gamma(s1 pow 2))) IN
            cball(phi(gamma b),rho0)`
  (LABEL_TAC "ZIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A) b)`; `rho0:real`] CONVEX_CBALL) THEN
    REWRITE_TAC[CONVEX_ALT] THEN
    DISCH_THEN(MP_TAC o SPECL [`(phi:A->real^N)((gamma:real->A)(s1 pow 2))`;
                               `(phi:A->real^N)((gamma:real->A) b)`;
                               `inv(sqrt b - s1) * (s - s1)`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "YC" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPECL [`s1:real`; `sqrt b`; `s:real`] P2AXS_UNIT_PARAM) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MP_TAC(SPECL [`s1:real`; `sqrt b`; `s:real`] P2AXS_UNIT_PARAM) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b < sqrt b + h1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N)
                       ((phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                        (inv(sqrt b - s1) * (sqrt tau - s1)) %
                        (phi(gamma b) - phi(gamma(s1 pow 2))))` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                             (inv(sqrt b - s1) * (drop v - s1)) %
                             (phi(gamma b) - phi(gamma(s1 pow 2)))`;
                 `s1:real`; `sqrt b`; `sqrt b - h1`; `sqrt b + h1`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        not(is_forall(concl th)))) THEN
      USE_THEN "ZIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `inv(sqrt b - s1) % ((phi:A->real^N)((gamma:real->A) b) -
                                      phi(gamma(s1 pow 2)))` THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. vector_derivative
             (\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                         (inv(sqrt b - s1) * (drop v - s1)) %
                         (phi(gamma b) - phi(gamma(s1 pow 2))))
             (at v)) =
      (\v. inv(sqrt b - s1) % ((phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      REWRITE_TAC[CONTINUOUS_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LSEG") (LABEL_TAC "HRI"))) THEN
  (SUBGOAL_THEN `(sig:real->A) (s1 pow 2) = (gamma:real->A)(s1 pow 2) /\ sig b = gamma b`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(s1 pow 2) = s1` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `inv(sqrt b - s1) * (sqrt b - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `y1 + &1 % (y2 - y1):real^N = y2`] THEN
    CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(USE_THEN "MEM" MATCH_MP_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `real_integral (real_interval[s1 pow 2,b])
      (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt sig b) =
    p2a_cL (p2a_rlocal V W b'' (U INTER W,phi:A->real^N)) tt
      (\v. phi((gamma:real->A)(s1 pow 2)) +
           (inv(sqrt b - s1) * (drop v - s1)) % (phi(gamma b) - phi(gamma(s1 pow 2))))
      s1 (sqrt b)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN USE_THEN "HRI" ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `(phi:A->real^N)((gamma:real->A)(s1 pow 2))`;
                 `(phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))`;
                 `inv(sqrt b - s1)`; `s1:real`; `sqrt b`;
                 `cball((phi:A->real^N)((gamma:real->A) b),rho0)`; `Cg:real`; `Kp:real`]
                P2A_ZPIECE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QB" (MP_TAC o SPECL [`s:real`; `y:real^N`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "KP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `norm((phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))) pow 2 <=
                &8 * eps * (sqrt b - s1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= eps * (sqrt b - s1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "D" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))`;
                 `s1:real`; `sqrt b`; `Cg:real`; `Kp:real`; `eps:real`; `e / &4`; `e / &8`]
                P2AXS_ZBOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `abs(real_integral (real_interval[s1 pow 2,b])
                  (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                      (real->A->real^N^N)) tt gamma b)) < eta`
  ASSUME_TAC THENL
   [USE_THEN "INT" (MP_TAC o SPECL [`s1:real`; `sqrt b`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `sig:real->A`; `gamma:real->A`;
                 `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau else sig tau`;
                 `b:real`; `s1 pow 2`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AXR_ADMX_RESTRICT THEN EXISTS_TAC `b:real` THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE];
      USE_THEN "LSEG" ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      SIMP_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau = s1 pow 2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ADM1") (LABEL_TAC "LEN1"))] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`;
                 `b:real`; `s1 pow 2`] P2AXR_LENGTH_SPLIT_X) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `sig:real->A`;
                 `b:real`; `s1 pow 2`; `P:real->bool`; `B:real->bool`]
                P2AXS_ENDREP_PC1B) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P1:real->bool` (LABEL_TAC "PB1")) THEN
  EXISTS_TAC `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau else (sig:real->A) tau` THEN
  EXISTS_TAC `P1:real->bool` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ADM1" ACCEPT_TAC;
    MATCH_MP_TAC P2AXS_PC1B_MONO THEN
    EXISTS_TAC `{s:real | s IN B /\ s <= s1 pow 2}` THEN
    ASM_REWRITE_TAC[FINITE_DELETE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    USE_THEN "LEN1" SUBST1_TAC THEN ASM_REAL_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* All bad corners are removed (induction on the finite bad set), and an     *)
(* admx curve is approximated in L-length by p2a_adm1 curves with the same  *)
(* end point (P2AXS_SMOOTHING_X): first the bad corners, then the corners   *)
(* of the resulting p2a_adm curve (P2AXS_SMOOTHING).                         *)
(* ------------------------------------------------------------------------- *)

let P2AXS_REMOVE_BAD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ p2a_atlas_lc V
     ==> !B. FINITE B
             ==> !(gamma:real->A) P e.
                   p2a_admx V tt x b gamma /\ p2axs_pc1b V tt gamma (&0) b P B /\ &0 < e
                   ==> ?gamma1 P1. p2a_admx V tt x b gamma1 /\
                                   p2axs_pc1b V tt gamma1 (&0) b P1 {} /\
                                   gamma1 b = gamma b /\
                                   p2a_L_length V tt gamma1 b <=
                                   p2a_L_length V tt gamma b + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`gamma:real->A`; `P:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `B:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`gamma:real->A`; `P:real->bool`; `e:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < t /\ t <= b` THENL
   [ALL_TAC;
    USE_THEN "IH" MATCH_MP_TAC THEN EXISTS_TAC `P:real->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AXS_PC1B_MONO THEN EXISTS_TAC `(t:real) INSERT B` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `?gamma1 P1. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt x b gamma1 /\
                p2axs_pc1b V tt gamma1 (&0) b P1 B /\
                gamma1 b = (gamma:real->A) b /\
                p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e / &2`
  (X_CHOOSE_THEN `gamma1:real->A` (X_CHOOSE_THEN `P1:real->bool` STRIP_ASSUME_TAC)) THENL
   [SUBGOAL_THEN `B:real->bool = (t INSERT B) DELETE t` SUBST1_TAC THENL
     [REWRITE_TAC[DELETE_INSERT] THEN ASM_MESON_TAC[DELETE_NON_ELEMENT]; ALL_TAC] THEN
    ASM_CASES_TAC `t:real = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2AXS_END_STEP THEN
      EXISTS_TAC `P:real->bool` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2AXS_INT_STEP THEN EXISTS_TAC `P:real->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`gamma1:real->A`; `P1:real->bool`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma2:real->A` (X_CHOOSE_THEN `P2:real->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`gamma2:real->A`; `P2:real->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AXS_SMOOTHING_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\ &0 < e
     ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                  p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?P. p2a_pc1x (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma (&0) b P`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2AXS_REMOVE_BAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `P:real->bool`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p2a_pc1x]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `P:real->bool`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P2AXS_PC1X_PC1B] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2AXS_PC1B_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->A` (X_CHOOSE_THEN `P1:real->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma1:real->A`;
                 `e / &2`] P2AXS_SMOOTHING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AX_ADMX_ADM THEN EXISTS_TAC `P1:real->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

