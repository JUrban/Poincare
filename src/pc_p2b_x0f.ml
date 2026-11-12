(* ========================================================================= *)
(* pc_p2b_x0f (Part 2B): X0 at the final slice (MT p. 229 applies Cor 9.53,  *)
(* a statement for t < 0, to the final slice t = 0 of the Thm 9.64 limit).   *)
(* Main theorem:                                                             *)
(*   P2B_SPLIT_AT_INFINITY_FINAL_ROUTE                                      *)
(*     |- !w. P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT w                 *)
(* i.e. ANCIENT_COMPACT ==> X0 for the closed-end class p2b_ancflow0c at the *)
(* picking slice 0 (statements in pc_p2b_chainstmts).  The proof of          *)
(* pc_p2b_x0 (X0.6-X0.11c) for the closed-end class with a picking time      *)
(* s0 <= 0 (P2BX0F_GEN_STATEMENT, P2BX0F_SPLIT_BODY), the case s0 = 0, and   *)
(* the LIM theorems as proved theorems.  End-time lemmas replace the uses of *)
(* s0 < b in pc_p2b_x0: the scalar curvature is left-continuous and          *)
(* nondecreasing up to the end time of rfs_flow_upto.  Sections: end-time    *)
(* lemmas; curvature on balls and the hypotheses of ANCIENT_COMPACT; the     *)
(* limit section; the generalized body; the final slice and the route.       *)
(* ========================================================================= *)

needs "src/pc_p2b_x0lim.ml";;

prioritize_real();;
type_invention_error := true;;

(* X0F.E1 The scalar curvature at the end time of an rfs_flow_upto flow:    *)
(* left-continuity at b (the smooth box of RFA_UPTO_BOX and                 *)
(* LRG_LSMOOTH_LSCALAR) and monotonicity up to b from dR/dt >= 0 before b. *)

let P2BX0F_SCALAR_LEFT_CONT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) x e.
     rfs_flow_upto (top,atlas) a b g /\ x IN topspace top /\ &0 < e
     ==> ?d. &0 < d /\
             !t. b - d < t /\ t <= b
                 ==> abs(mfd_scalar atlas (g t) x - mfd_scalar atlas (g b) x) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`] RFA_UPTO_BOX) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`ball(SND (c:(A->bool)#(A->real^3)) x,d0)`; `b - d0`; `b + d0`;
                 `\s y. lscalar ((Gb:real->real^3->real^3^3) s) y`; `b:real`;
                 `SND (c:(A->bool)#(A->real^3)) x`] P2BX0_LSMOOTH_TCONT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LRG_LSMOOTH_LSCALAR; CENTRE_IN_BALL; OPEN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d0 d1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_scalar] THEN
  SUBGOAL_THEN `metric_local atlas c ((g:real->A->real^3^3) t) = Gb t /\
                metric_local atlas c (g b) = Gb b` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real = b` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2BX0F_SCALAR_MONO_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a (g:real->A->real^3^3) x s1 s2.
     rfs_flow_upto (top,atlas) a (&0) g /\ a < s1 /\ s1 <= s2 /\ s2 <= &0 /\
     x IN topspace top /\
     (!s dR. s1 <= s /\ s < &0 /\ s <= s2 /\
             ((\t. mfd_scalar atlas (g t) x) has_real_derivative dR) (atreal s)
             ==> &0 <= dR)
     ==> mfd_scalar atlas (g s1) x <= mfd_scalar atlas (g s2) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a (&0) (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  ASM_CASES_TAC `s2 < &0` THENL
   [MATCH_MP_TAC P2BX0_SCALAR_MONO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `&0`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s1 = &0` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                 `g:real->A->real^3^3`; `x:A`;
                 `mfd_scalar atlas ((g:real->A->real^3^3) s1) x -
                  mfd_scalar atlas (g(&0)) x`] P2BX0F_SCALAR_LEFT_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t = --(min d (--s1)) / &2` THEN
  SUBGOAL_THEN `s1 < t /\ t < &0 /\ &0 - d < t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->A->real^3^3) s1) x <= mfd_scalar atlas (g t) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX0_SCALAR_MONO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `&0`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
    `!t. &0 - d < t /\ t <= &0 ==> P t`) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* X0F.E2 Curvature on the picked balls for the closed-end class: abs Rm    *)
(* <= 2 Q k at all times s <= s0 <= 0 on the balls of radius A / sqrt Q k   *)
(* (R <= 4 Q k there at s0, R nondecreasing in time up to the end time,     *)
(* abs Rm <= R / 2).  P2BX0_CURV_ON_BALLS for p2b_ancflow0c.                 *)

let P2BX0F_CURV_ON_BALLS = prove
 (`!kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) A N.
     p2b_ancflow0c kappa (top,atlas) g /\ s0 <= &0 /\
     (!k. q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
     (!k y. N <= k /\
            y IN mfd_ball (top,atlas) (g s0) (q k) (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
            ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q k))
     ==> !k s y. N <= k /\ s <= s0 /\
                 y IN mfd_ball (top,atlas) (g s0) (q k)
                                (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                 ==> mfd_rm_norm atlas (g s) y <= &2 * mfd_scalar atlas (g s0) (q k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "q") (LABEL_TAC "ball")))) THEN
  REWRITE_TAC[p2b_ancflow0c] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "comp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "drds")
    (LABEL_TAC "knc"))))))))) THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) ((q:num->B) k)
                             (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_flow_upto (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                  (s - &1) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
    riemannian_metric atlas ((g:real->B->real^3^3) s)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                   (s - &1) (&0) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) y / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas ((g:real->B->real^3^3) s) y <= mfd_scalar atlas (g s0) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX0F_SCALAR_MONO_END THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `s - &1`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s':real`; `dR:real`] THEN STRIP_TAC THEN
      USE_THEN "drds" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`s':real`; `y:B`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas ((g:real->B->real^3^3) s0) y <=
    &4 * mfd_scalar atlas (g s0) ((q:num->B) k)`
  MP_TAC THENL
   [USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) y <= mfd_scalar atlas (g s0) y` THEN
  REAL_ARITH_TAC);;

(* X0F.E3 The hypotheses of ANCIENT_COMPACT for the shifted flows          *)
(* g(s0 + t) of the closed-end class, s0 <= 0 (P2BX0_ANCIENT_HYPS for       *)
(* p2b_ancflow0c; at s0 = 0 the shift is the flow itself).                  *)

let P2BX0F_ANCIENT_HYPS = prove
 (`!kappa top atlas (g:real->B->real^3^3) s0 (q:num->B).
     p2b_ancflow0c kappa (top,atlas) g /\ s0 <= &0 /\
     (!k. q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
     (!A. ?N. !k y. N <= k /\
                    y IN mfd_ball (top,atlas) (g s0) (q k)
                                  (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                    ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q k))
     ==> (!k. hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (\t. g(s0 + t))) /\
              (!t. t <= &0 ==> mfd_complete (top,atlas) (g(s0 + t))) /\
              q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
         (!A a. &0 < A /\ a < &0
                ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                                   y IN mfd_ball (top,atlas) (g(s0 + &0)) (q k)
                                          (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                                   ==> mfd_rm_norm atlas
                                         (g(s0 + s / mfd_scalar atlas (g s0) (q k))) y <=
                                       CA * mfd_scalar atlas (g s0) (q k)) /\
         (?r0 kappa' N. &0 < r0 /\ &0 < kappa' /\
            !k. N <= k
                ==> ?v. mfd_has_volume (top,atlas) (g(s0 + &0))
                          (mfd_ball (top,atlas) (g(s0 + &0)) (q k)
                             (r0 * inv(sqrt(mfd_scalar atlas (g s0) (q k))))) v /\
                        kappa' * (r0 * inv(sqrt(mfd_scalar atlas (g s0) (q k)))) pow 3 <= v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "anc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "q") (LABEL_TAC "ball")))) THEN
  USE_THEN "anc" (MP_TAC o REWRITE_RULE[p2b_ancflow0c]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "comp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "drds")
    (LABEL_TAC "knc"))))))))) THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "rf" (MP_TAC o SPEC `s0 - &1`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto; ricci_flow_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (\t. (g:real->B->real^3^3)(s0 + t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN ASM_CASES_TAC `s0 = &0` THENL
     [ASM_REWRITE_TAC[REAL_ADD_LID; ETA_AX] THEN USE_THEN "rf" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BX0_FLOW_UPTO_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`s0 + a - &1`; `&0`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "rf" (MP_TAC o SPEC `s0 + a - &1`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t <= &0 ==> mfd_complete (top,atlas) ((g:real->B->real^3^3)(s0 + t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "comp" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`A:real`; `a:real`] THEN STRIP_TAC THEN
    USE_THEN "ball" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
    MAP_EVERY EXISTS_TAC [`&2`; `N:num`] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y:B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `s0:real`; `q:num->B`; `A:real`; `N:num`]
                  P2BX0F_CURV_ON_BALLS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`
    ASSUME_TAC THENL [USE_THEN "q" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> s0 + x <= s0`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  USE_THEN "ball" (X_CHOOSE_TAC `N:num` o SPEC `&1`) THEN
  MAP_EVERY EXISTS_TAC [`&1 / &2`; `kappa:real`; `N:num`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)` THEN
  SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
   [EXPAND_TAC "Qk" THEN USE_THEN "q" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  ABBREV_TAC `r = &1 / &2 * inv(sqrt Qk)` THEN
  SUBGOAL_THEN `&0 < r /\ inv(r pow 2) = &4 * Qk /\ r <= &1 * inv(sqrt Qk)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    SUBGOAL_THEN `&0 < sqrt Qk` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `&0 < Qk` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "knc" (MP_TAC o SPEC `r:real`) THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view] THEN REWRITE_TAC[rfs_kappa_noncollapsed] THEN
  DISCH_THEN(MP_TAC o SPECL [`s0:real`; `(q:num->B) k`; `r:real`]) THEN
  REWRITE_TAC[rfs_flow_view; rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rf" (MP_TAC o SPEC `s0 - &1`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[rfs_flow_upto; ricci_flow_on]] THEN
      STRIP_TAC THEN ASM_CASES_TAC `s0 = &0` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * Qk` THEN CONJ_TAC THENL
     [EXPAND_TAC "Qk" THEN
      MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:real->B->real^3^3`; `s0:real`; `q:num->B`; `&1`; `N:num`]
                    P2BX0F_CURV_ON_BALLS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) ((q:num->B) k) r` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

(* X0F.E4 The X0 limit section for the closed-end class (adapted from       *)
(* pc_p2b_x0, X0.6-X0.11c, with p2b_ancflow0c, the views up to 0 and the    *)
(* picking time s0 <= 0).                                                    *)

(* X0.6 Limit properties in the X0 setting (views of g on s < b at the      *)
(* times s0 + s / Q k, Q k = R(s0,q k)) from the LIM statements:             *)
(* sec >= 0 and R(xl,0) = 1 (LIM_CURV).                                      *)

let p2bx0f_xlim = new_definition
 `p2bx0f_xlim kappa (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
             s0 (q:num->B) (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
             (g':real->B->real^3^3) (xl:B) (W:num->B->bool) (phi:num->B->B) <=>
    p2b_ancflow0c kappa (top,atlas) g /\ s0 <= &0 /\
    (!k. q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
    p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s <= &0} g) q (\k. s0)
                        (\k. mfd_scalar atlas (g s0) (q k)) {s | s <= &0}
                        (top',atlas') g' xl W phi /\
    (!s. s <= &0 ==> riemannian_metric atlas' (g' s))`;;

let P2BX0F_XVIEW = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) s0 Q s.
     s0 <= &0 /\ &0 < Q /\ s <= &0
     ==> rfs_vtop (rfs_flow_view (top,atlas) {s | s <= &0} g) (s0 + s / Q) = top /\
         rfs_vatlas (rfs_flow_view (top,atlas) {s | s <= &0} g) (s0 + s / Q) = atlas /\
         rfs_vmetric (rfs_flow_view (top,atlas) {s | s <= &0} g) (s0 + s / Q) = g (s0 + s / Q) /\
         s0 + s / Q <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s0 + s / Q <= &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `s / Q <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2BX0_VIEW_FACTS; IN_ELIM_THM]);;

let P2BX0F_XLIM_BASIC = prove
 (`!kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
         (!s. s <= &0 ==> riemannian_metric atlas (g s)) /\
         (!s x u v. s <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g s) x u v) /\
         hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ xl IN topspace top' /\
         (!k. (phi:num->B->B) k xl = q k) /\
         (!n:num s. ~(topspace(rfs_vtop (rfs_flow_view (top,atlas) {s | s <= &0} g) s) = {})
                ==> smooth_manifold_atlas
                      (rfs_vtop (rfs_flow_view (top,atlas) {s | s <= &0} g) s)
                      (rfs_vatlas (rfs_flow_view (top,atlas) {s | s <= &0} g) s) /\
                    riemannian_metric
                      (rfs_vatlas (rfs_flow_view (top,atlas) {s | s <= &0} g) s)
                      (rfs_vmetric (rfs_flow_view (top,atlas) {s | s <= &0} g) s)) /\
         (!k:num tau. hausdorff_space
                    (rfs_vtop (rfs_flow_view (top,atlas) {s | s <= &0} g) tau))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx0f_xlim] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_ancflow0c kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_ancflow0c; p2b_kview] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                (!s. s <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `--(&1)` o check (fun th ->
        can (term_match [] `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)`)
            (concl th))) THEN
      REWRITE_TAC[REAL_ARITH `--(&1) < &0`] THEN MESON_TAC[rfs_flow_upto; ricci_flow_on];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th ->
        can (term_match [] `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)`)
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
      ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hausdorff_space (top':B topology) /\ smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
                (xl:B) IN topspace top' /\ (!k. (phi:num->B->B) k xl = q k)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `{s:real | s <= &0}`;
                   `g:real->B->real^3^3`] P2BX0_VIEW_REGULAR) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `{s:real | s <= &0}`;
                   `g:real->B->real^3^3`] P2BX0_VIEW_HAUSDORFF) THEN
    ASM_SIMP_TAC[]]);;

(* X0.6b sec >= 0 and R(xl,0) = 1 on the X0 limit (LIM_CURV).                *)

let P2BX0F_XLIM_SEC = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi
     ==> !s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional atlas' (g' s) y u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  UNDISCH_TAC `LIM_CURV_STATEMENT (w:B->bool) w` THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`; `y:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXISTS_TAC `0` THEN MAP_EVERY X_GEN_TAC [`k:num`; `z:B`; `u':real^3`; `v':real^3`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `s0:real`;
                   `mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`; `s:real`]
                  P2BX0F_XVIEW) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:B) IN topspace (rfs_vtop (rfs_flow_view (top,atlas) {s | s <= &0}
                     (g:real->B->real^3^3)) (s0 + s / mfd_scalar atlas (g s0) ((q:num->B) k)))` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BX0F_XLIM_R1 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi
     ==> mfd_scalar atlas' (g'(&0)) xl = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th))) THEN
  UNDISCH_TAC `LIM_CURV_STATEMENT (w:B->bool) w` THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k) *
                     inv (mfd_scalar atlas (g s0) (q k))) = (\k. &1)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_CONST_EQ; TRIVIAL_LIMIT_SEQUENTIALLY] THEN MESON_TAC[]);;

(* distance to q k approaches d(xl,y) (LIM_DIST on {xl,y}).                 *)

let P2BX0F_XLIM_NEAR = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi
    s y e.
     LIM_DIST_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ s <= &0 /\ mfd_complete (top',atlas') (g' s) /\
     y IN topspace top' /\ &0 < e
     ==> ?k0. !k. k0 <= k
                  ==> (phi:num->B->B) k y IN topspace top /\
                      mfd_joinable (top,atlas) (q k) (phi k y) /\
                      abs(sqrt(mfd_scalar atlas (g s0) (q k)) *
                          mfd_dist (top,atlas) (g(s0 + s / mfd_scalar atlas (g s0) (q k)))
                                   (q k) (phi k y) -
                          mfd_dist (top',atlas') (g' s) xl y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th)) STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `LIM_DIST_STATEMENT (w:B->bool) w` THEN REWRITE_TAC[LIM_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`;
    `{xl:B,y}`; `e:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_THEN(LABEL_TAC "d") THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "d" (MP_TAC o SPECL [`k:num`; `xl:B`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `s0:real`;
                 `mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`; `s:real`]
                P2BX0F_XVIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[]);;

(* X0.6d R(0,y) <= 4 on the X0 limit: the picked balls bound R by 4 R(q k)   *)
(* on balls of radius A / sqrt(R(q k)), LIM_DIST puts phi k y in them,     *)
(* LIM_CURV passes the bound to the limit.                                  *)

let P2BX0F_XLIM_R4 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ mfd_complete (top',atlas') (g'(&0)) /\
     (!A. ?N. !k y. N <= k /\
                    y IN mfd_ball (top,atlas) (g s0) (q k)
                                  (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                    ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q k))
     ==> !y. y IN topspace top' ==> mfd_scalar atlas' (g'(&0)) y <= &4`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L5") (CONJUNCTS_THEN2 (LABEL_TAC "L1")
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "balls")))))) THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  ABBREV_TAC `A = mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl y + &1` THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `&0`; `y:B`; `&1`] P2BX0F_XLIM_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "near")) THEN
  USE_THEN "balls" (MP_TAC o SPEC `A:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  USE_THEN "L5" (MP_TAC o REWRITE_RULE[LIM_CURV_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `y:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((phi:num->B->B) k y) *
                  inv(mfd_scalar atlas (g s0) ((q:num->B) k))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `k0 + N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "near" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k) /\
                &0 < sqrt(mfd_scalar atlas (g s0) (q k))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  USE_THEN "N" (MP_TAC o SPECL [`k:num`; `(phi:num->B->B) k y`]) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    UNDISCH_TAC `abs(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)) *
                     mfd_dist (top,atlas) (g s0) (q k) ((phi:num->B->B) k y) -
                     mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl y) < &1` THEN
    EXPAND_TAC "A" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

(* X0.6e Completeness for all s <= 0 and monotonicity of R in time on the   *)
(* X0 limit.                                                                 *)

let P2BX0F_XLIM_COMPLETE = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi /\
     (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
     mfd_complete (top',atlas') (g'(&0))
     ==> !s. s <= &0 ==> mfd_complete (top',atlas') (g' s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L6")
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th))
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0F_XLIM_SEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "L6" (MP_TAC o REWRITE_RULE[LIM_FLOW_COMPLETE_BACK_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `g':real->B->real^3^3`; `s - &1`; `&0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2BX0F_XLIM_MONO = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s))
     ==> !s1 s2 y. s1 <= s2 /\ s2 <= &0 /\ y IN topspace top'
                   ==> mfd_scalar atlas' (g' s1) y <= mfd_scalar atlas' (g' s2) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L5") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th))
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "comp"))))) THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`; `y:B`] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_ancflow0c kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_ancflow0c; p2b_kview] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `s1:real`; `y:B`; `&1`] P2BX0F_XLIM_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; USE_THEN "comp" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "near")) THEN
  SUBGOAL_THEN `s1 <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (sv,lab) ->
    USE_THEN "L5" (MP_TAC o REWRITE_RULE[LIM_CURV_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`; `q:num->B`;
      `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
      `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; sv; `y:B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(LABEL_TAC lab o CONJUNCT1)])
    [`s1:real`,"lim1"; `s2:real`,"lim2"] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\k. mfd_scalar (rfs_vatlas ((\k:num. rfs_flow_view (top,atlas) {s | s <= &0}
                                              (g:real->B->real^3^3)) k)
                      ((\k:num. (s0:real)) k + s1 / (\k. mfd_scalar atlas (g s0) ((q:num->B) k)) k))
                    (rfs_vmetric ((\k:num. rfs_flow_view (top,atlas) {s | s <= &0} g) k)
                      ((\k:num. s0) k + s1 / (\k. mfd_scalar atlas (g s0) (q k)) k))
                    ((phi:num->B->B) k y) / (\k. mfd_scalar atlas (g s0) (q k)) k`;
    `\k. mfd_scalar (rfs_vatlas ((\k:num. rfs_flow_view (top,atlas) {s | s <= &0}
                                              (g:real->B->real^3^3)) k)
                      ((\k:num. (s0:real)) k + s2 / (\k. mfd_scalar atlas (g s0) ((q:num->B) k)) k))
                    (rfs_vmetric ((\k:num. rfs_flow_view (top,atlas) {s | s <= &0} g) k)
                      ((\k:num. s0) k + s2 / (\k. mfd_scalar atlas (g s0) (q k)) k))
                    ((phi:num->B->B) k y) / (\k. mfd_scalar atlas (g s0) (q k)) k`] THEN
  CONJ_TAC THENL [USE_THEN "lim1" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "lim2" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "near" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)` THEN
  SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
   [EXPAND_TAC "Qk" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `s0:real`; `Qk:real`; `s1:real`]
                P2BX0F_XVIEW) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `s0:real`; `Qk:real`; `s2:real`]
                P2BX0F_XVIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC P2BX0F_SCALAR_MONO_END THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `s0 + s1 / Qk - &1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)`)
          (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> s0 + x <= s0 + y`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    MAP_EVERY X_GEN_TAC [`s:real`; `dR:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(phi:num->B->B) k y`; `dR:real`] o
      check (fun th -> can (term_match []
        `!s x dR. s < &0 /\ x IN topspace top /\
                  ((\t. mfd_scalar atlas ((g:real->B->real^3^3) t) x) has_real_derivative dR)
                  (atreal s) ==> &0 <= dR`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC]]);;

let P2BX0F_XLIM_RM = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s)) /\
     (!y. y IN topspace top' ==> mfd_scalar atlas' (g'(&0)) y <= &4)
     ==> !s y. s <= &0 /\ y IN topspace top' ==> mfd_rm_norm atlas' (g' s) y <= &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r4")))))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0F_XLIM_SEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sec") THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0F_XLIM_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "mono") THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!s. s <= &0 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) s`; `y:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  USE_THEN "mono" (MP_TAC o SPECL [`s:real`; `&0`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  USE_THEN "r4" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BX0F_XLIM_DRDS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s))
     ==> !s y dR. s <= &0 /\ y IN topspace top' /\
                  ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                  ==> &0 <= dR`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "mono" o MATCH_MP P2BX0F_XLIM_MONO) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `dR:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. mfd_scalar atlas' ((g':real->B->real^3^3) t) (y:B)`; `s:real`; `dR:real`]
                P2BX0_MONO_DERIV_NONNEG) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`] THEN STRIP_TAC THEN
  USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BX0F_XLIM_KNC = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_KNC_STATEMENT w w /\
     p2bx0f_xlim kappa (top,atlas) g s0 q (top',atlas') g' xl W phi /\
     (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s))
     ==> !r0. rfs_kappa_noncollapsed (rfs_flow_view (top',atlas') {s | s <= &0} g') kappa r0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L3") (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th)) (LABEL_TAC "comp"))) THEN
  X_GEN_TAC `r0:real` THEN
  UNDISCH_TAC `p2b_ancflow0c kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_ancflow0c; p2b_kview] THEN STRIP_TAC THEN
  USE_THEN "L3" (MP_TAC o REWRITE_RULE[LIM_KNC_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `kappa:real`;
    `r0:real`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]);;

(* X0.11b The X0 limit exists: ANCIENT_COMPACT on the shifted flows g(s0+t) *)
(* at the points q1 k with Q k = R(s0,q1 k) (hypotheses by                  *)
(* P2BX0F_ANCIENT_HYPS), restriction of every per-Tl limit to the joinable   *)
(* class of xl (P2CO_P3_FLOW_RESTRICT, connected), one p2c_flow_limit_with  *)
(* on s <= 0 (P2BX0_FLOW_LIMIT_DIAG), and conversion to the X0 views        *)
(* rfs_flow_view of g on the times s < b, at times s0 + s/Q k               *)
(* (P2BX0_FLOW_LIMIT_WITH_CONG).                                            *)

let P2BX0F_ANC_BASIC = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_ancflow0c kappa (top,atlas) g
     ==> hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
         (!s. s <= &0 ==> riemannian_metric atlas (g s)) /\
         (!s. s <= &0 ==> mfd_complete (top,atlas) (g s)) /\
         (!s x u v. s <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g s) x u v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_ancflow0c] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--(&1)` o check (fun th ->
      can (term_match [] `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)`)
          (concl th))) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) < &0`] THEN MESON_TAC[rfs_flow_upto; ricci_flow_on];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th ->
      can (term_match [] `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)`)
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let P2BX0F_LIMIT_EXISTS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) s0 (q1:num->B).
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
     p2b_ancflow0c kappa (top,atlas) g /\ s0 <= &0 /\
     (!k. q1 k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q1 k)) /\
     (!A. ?N. !k y. N <= k /\
                    y IN mfd_ball (top,atlas) (g s0) (q1 k)
                                  (A * inv(sqrt(mfd_scalar atlas (g s0) (q1 k))))
                    ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q1 k))
     ==> ?sub (top':B topology) atlas' g' xl W phi.
            p3_subseq sub /\
            p2bx0f_xlim kappa (top,atlas) g s0 (q1 o sub) (top',atlas') g' xl W phi /\
            connected_space top' /\
            (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
            mfd_complete (top',atlas') (g'(&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "AC") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "q1") (LABEL_TAC "balls"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0F_ANC_BASIC) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `s0:real`; `q1:num->B`] P2BX0F_ANCIENT_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "hyps")] THEN
  USE_THEN "AC" (MP_TAC o REWRITE_RULE[P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. (top:B topology)`; `\k:num. (atlas:((B->bool)#(B->real^3))->bool)`;
    `\k:num t. (g:real->B->real^3^3) (s0 + t)`; `q1:num->B`;
    `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)`]) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [USE_THEN "hyps" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top1:B topology`
    (X_CHOOSE_THEN `atlas1:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g1:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim1")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem1") (LABEL_TAC "comp1"))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top1:B topology) (atlas1:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "lim1" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the shifted views are regular *)
  SUBGOAL_THEN
   `!s. ~(topspace(rfs_vtop (rfs_flow_view (top,atlas) {t | t <= &0}
                                  (\t. (g:real->B->real^3^3) (s0 + t))) s) = {})
              ==> smooth_manifold_atlas
                    (rfs_vtop (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s)
                    (rfs_vatlas (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s) /\
                  riemannian_metric
                    (rfs_vatlas (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s)
                    (rfs_vmetric (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s)`
  (LABEL_TAC "reg") THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `{t:real | t <= &0}`;
                   `\t. (g:real->B->real^3^3) (s0 + t)`] P2BX0_VIEW_REGULAR) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* restriction of every per-Tl limit to the joinable class of xl *)
  SUBGOAL_THEN
   `(!Tl. &0 < Tl
          ==> p3_flow_limit
                (\k:num. rfs_flow_view (top,atlas) {t | t <= &0}
                                       (\t. (g:real->B->real^3^3) (s0 + t)))
                ((q1:num->B) o (sub1:num->num)) (\k. &0)
                ((\k. mfd_scalar atlas (g s0) (q1 k)) o sub1)
                (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
                 restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
                (\s. restrict_metric atlas1 {y | mfd_joinable (top1,atlas1) xl y}
                                     ((g1:real->B->real^3^3) s)) xl Tl) /\
    connected_space
      (subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y})`
  (CONJUNCTS_THEN2 (LABEL_TAC "rlim") ASSUME_TAC) THENL
   [CONJ_TAC THENL [X_GEN_TAC `Tl:real` THEN DISCH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0} (\t. (g:real->B->real^3^3) (s0 + t))`;
      `(q1:num->B) o (sub1:num->num)`; `\k:num. &0`;
      `(\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)`;
      `top1:B topology`; `atlas1:((B->bool)#(B->real^3))->bool`; `g1:real->B->real^3^3`; `xl:B`]
     P2CO_P3_FLOW_RESTRICT) THENL
     [DISCH_THEN(MP_TAC o SPEC `Tl:real`); DISCH_THEN(MP_TAC o SPEC `&1`)] THEN
    REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [CONJ_TAC THENL
        [FIRST [USE_THEN "reg" ACCEPT_TAC; GEN_TAC THEN USE_THEN "reg" ACCEPT_TAC];
         USE_THEN "lim1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_01]];
       SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < &0
        ==> rfs_flow_upto
              (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
               restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y}) a (&0)
              (\s. restrict_metric atlas1
                     {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                     ((g1:real->B->real^3^3) s))`
  (LABEL_TAC "upto") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rlim" (MP_TAC o SPEC `&1 - a`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p3_flow_limit] THEN
    DISCH_THEN(MP_TAC o el 5 o CONJUNCTS) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s <= &0
        ==> riemannian_metric
              (restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
              (restrict_metric atlas1
                 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                 ((g1:real->B->real^3^3) s))`
  (LABEL_TAC "riem") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `s - &1`; `&0`;
      `\s. restrict_metric atlas1
             {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
             ((g1:real->B->real^3^3) s)`;
      `s:real`] P2AP_UPTO_RIEM) THEN
    REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_complete (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
                  restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
                 (restrict_metric atlas1
                    {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                    ((g1:real->B->real^3^3) (&0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CO_CLASS_COMPLETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* one limit on s <= 0 *)
  MP_TAC(ISPECL
   [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0} (\t. (g:real->B->real^3^3) (s0 + t))`;
    `(q1:num->B) o (sub1:num->num)`; `\k:num. &0`;
    `(\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)`;
    `subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`] P2BX0_FLOW_LIMIT_DIAG) THEN
  ANTS_TAC THENL [USE_THEN "rlim" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `W:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->B` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "with"))))) THEN
  (* to the X0 views *)
  MP_TAC(ISPECL
   [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0} (\t. (g:real->B->real^3^3) (s0 + t))`;
    `\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`;
    `((q1:num->B) o (sub1:num->num)) o (sub2:num->num)`;
    `(\k:num. &0) o (sub2:num->num)`; `\k:num. (s0:real)`;
    `((\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)) o
     (sub2:num->num)`;
    `{s:real | s <= &0}`;
    `subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`] P2BX0_FLOW_LIMIT_WITH_CONG) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "with" ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN DISCH_TAC THEN
    ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) s0)
                                ((q1:num->B) ((sub1:num->num) ((sub2:num->num) k)))` THEN
    SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
     [EXPAND_TAC "Qk" THEN USE_THEN "q1" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `s0:real`; `Qk:real`; `s:real`]
                  P2BX0F_XVIEW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2BX0_VIEW_FACTS; IN_ELIM_THM; REAL_ADD_LID] THEN
    SUBGOAL_THEN `s / Qk <= &0` (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)) o
    (sub2:num->num) =
    (\k. mfd_scalar atlas (g s0) (q1 (sub1 (sub2 k))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(sub1:num->num) o (sub2:num->num)` THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p2bx0f_xlim; o_ASSOC] THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "upto" ACCEPT_TAC;
    ASM_REWRITE_TAC[]]);;

(* X0.11c Assembly: MT Prop 9.11 split at infinity (P2B_SPLIT_AT_INFINITY) *)
(* from the LIM statements and ANCIENT_COMPACT.  Picked points q0 at time   *)
(* s0 (P2BX0_PICKED_POINTS), almost-line pairs along them                   *)
(* (P2BX0_ALMOST_PAIRS), the X0 limit (P2BX0F_LIMIT_EXISTS), its properties  *)
(* (X0.6), a line at time 0 (P2BX0_LIMIT_PAIRS, P2BX0_LINE_FROM_PAIRS), the *)
(* splitting field (CMP_R3_SPLIT) and its time invariance                   *)
(* (P2BX0_TIME_INVARIANCE).                                                 *)


(* X0F.E4b The generalized closed-end X0 and its proof (P2BX0_SPLIT_BODY with *)
(* the closed-end setup lemmas).                                             *)

(* The generalized statement: X0 for the closed-end class at a picking time *)
(* s0 <= 0 (X0_FINAL is the case s0 = 0).                                   *)

let P2BX0F_GEN_STATEMENT = new_definition
 `P2BX0F_GEN_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) s0 p pp.
       p2b_ancflow0c kappa (top,atlas) g /\ s0 <= &0 /\ p IN topspace top /\
       (!k. pp k IN topspace top) /\
       (!M. ?N. !k. N <= k
                    ==> M < mfd_scalar atlas (g s0) (pp k) *
                            mfd_dist (top,atlas) (g s0) p (pp k) pow 2)
       ==> ?sub q (top':B topology) atlas' g' xl W phi X.
              p3_subseq sub /\
              (!k. q k IN topspace top /\
                   mfd_scalar atlas (g s0) (pp (sub k)) <= mfd_scalar atlas (g s0) (q k)) /\
              (!M. ?N. !k. N <= k
                           ==> M < mfd_scalar atlas (g s0) (q k) *
                                   mfd_dist (top,atlas) (g s0) p (q k) pow 2) /\
              p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s <= &0} g) q (\k. s0)
                                  (\k. mfd_scalar atlas (g s0) (q k)) {s | s <= &0}
                                  (top',atlas') g' xl W phi /\
              connected_space top' /\
              (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
              (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s)) /\
              (!s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                         ==> &0 <= mfd_sectional atlas' (g' s) y u v) /\
              mfd_scalar atlas' (g'(&0)) xl = &1 /\
              (?K. !s y. s <= &0 /\ y IN topspace top' ==> mfd_rm_norm atlas' (g' s) y <= K) /\
              (!r0. rfs_kappa_noncollapsed (rfs_flow_view (top',atlas') {s | s <= &0} g')
                                           kappa r0) /\
              (!s y dR. s <= &0 /\ y IN topspace top' /\
                        ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                        ==> &0 <= dR) /\
              p2b_gsplit (top',atlas') g' {s | s <= &0} X`;;

let p2bx0f_xargs =
  [`w:B->bool`; `kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
   `g:real->B->real^3^3`; `s0:real`;
   `((q0:num->B) o (suba:num->num)) o (subb:num->num)`;
   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
   `xl:B`; `W:num->B->bool`; `phi:num->B->B`];;

let P2BX0F_SPLIT_BODY = prove
 (`!w:B->bool.
     LIM_DIST_STATEMENT w w /\ LIM_BALL_STATEMENT w w /\ LIM_KNC_STATEMENT w w /\
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
     ==> P2BX0F_GEN_STATEMENT w`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "L2")
    (CONJUNCTS_THEN2 (LABEL_TAC "L3") (CONJUNCTS_THEN2 (LABEL_TAC "L5")
    (CONJUNCTS_THEN2 (LABEL_TAC "L6") (LABEL_TAC "AC")))))) THEN
  REWRITE_TAC[P2BX0F_GEN_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `s0:real`; `p:B`; `pp:num->B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ppin") (LABEL_TAC "ppdiv"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0F_ANC_BASIC) THEN
  (* facts at time s0 *)
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0) /\
                mfd_complete (top,atlas) (g s0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) s0) y u v`
  (LABEL_TAC "sec0") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN topspace top ==> &0 <= mfd_scalar atlas ((g:real->B->real^3^3) s0) y`
  (LABEL_TAC "Rnn") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s0`; `y:B`;
                   `mfd_rm_norm atlas ((g:real->B->real^3^3) s0) y`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN USE_THEN "sec0" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal)
                  (mfd_scalar atlas ((g:real->B->real^3^3) s0))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x. x IN topspace top /\ &0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) x`
  ASSUME_TAC THENL
   [USE_THEN "ppdiv" (MP_TAC o SPEC `&0`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN EXISTS_TAC `(pp:num->B) N` THEN
    USE_THEN "ppin" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= r /\ ~(r = &0) ==> &0 < r`) THEN CONJ_TAC THENL
     [USE_THEN "Rnn" MATCH_MP_TAC THEN USE_THEN "ppin" (fun th -> REWRITE_TAC[th]);
      DISCH_TAC THEN
      UNDISCH_TAC `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) ((pp:num->B) N) *
                        mfd_dist (top,atlas) (g s0) p (pp N) pow 2` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL]];
    ALL_TAC] THEN
  (* picked points *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `pp:num->B`] P2BX0_PICKED_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:num->B` (CONJUNCTS_THEN2 (LABEL_TAC "q0")
    (CONJUNCTS_THEN2 (LABEL_TAC "q0div") (LABEL_TAC "q0balls")))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `q0:num->B`] P2BX0_DIST_DIVERGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "q0" (fun th -> REWRITE_TAC[th]);
    DISCH_THEN(LABEL_TAC "q0far")] THEN
  (* almost-line pairs along q0 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `q0:num->B`;
                 `\n. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q0:num->B) n)`]
                P2BX0_ALMOST_PAIRS) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `suba:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pairs"))) THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) k` (LABEL_TAC "subage") THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the X0 limit along q0 o suba *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `s0:real`; `(q0:num->B) o (suba:num->num)`] P2BX0F_LIMIT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "q0balls" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "subage" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subb:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xlim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "comp0")))))))))))) THEN
  USE_THEN "xlim" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2BX0F_XLIM_BASIC th) THEN
                             STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0f_xlim] th)) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!s. s <= &0 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) ((subb:num->num) k)` (LABEL_TAC "subge") THENL
   [MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    USE_THEN "subage" (MP_TAC o SPEC `(subb:num->num) k`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. ?N. !k y. N <= k /\
                  y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0)
                         ((((q0:num->B) o (suba:num->num)) o (subb:num->num)) k)
                         (A * inv(sqrt(mfd_scalar atlas (g s0) (((q0 o suba) o subb) k))))
                  ==> mfd_scalar atlas (g s0) y <=
                      &4 * mfd_scalar atlas (g s0) (((q0 o suba) o subb) k)`
  (LABEL_TAC "qballs") THENL
   [REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "q0balls" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "subge" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* X0.6: the limit properties *)
  MP_TAC(ISPECL p2bx0f_xargs P2BX0F_XLIM_COMPLETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "compall")] THEN
  MP_TAC(ISPECL p2bx0f_xargs P2BX0F_XLIM_SEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "secl")] THEN
  MP_TAC(ISPECL p2bx0f_xargs P2BX0F_XLIM_R1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "r1")] THEN
  MP_TAC(ISPECL p2bx0f_xargs P2BX0F_XLIM_R4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "r4")] THEN
  MP_TAC(ISPECL p2bx0f_xargs P2BX0F_XLIM_RM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "rm")] THEN
  MP_TAC(ISPECL p2bx0f_xargs P2BX0F_XLIM_DRDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "drds")] THEN
  MP_TAC(ISPECL p2bx0f_xargs P2BX0F_XLIM_KNC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "knc")] THEN
  (* X0.8: exact pairs at time 0, then a line *)
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?a b. a IN topspace top' /\ b IN topspace top' /\
                  mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl a = A /\
                  mfd_dist (top',atlas') (g' (&0)) xl b = A /\
                  mfd_dist (top',atlas') (g' (&0)) a b = &2 * A`
  (LABEL_TAC "lpairs") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`w:B->bool`; `w:B->bool`;
      `\k:num. rfs_flow_view (top,atlas) {s | s <= &0} (g:real->B->real^3^3)`;
      `((q0:num->B) o (suba:num->num)) o (subb:num->num)`; `\k:num. (s0:real)`;
      `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0)
                      ((((q0:num->B) o (suba:num->num)) o (subb:num->num)) k)`;
      `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `A:real`]
     P2BX0_LIMIT_PAIRS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS; IN_ELIM_THM; o_THM] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pairs" (MP_TAC o SPECL [`A:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPEC `(subb:num->num) k`) THEN
    ANTS_TAC THENL
     [MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `xl:B`] P2BX0_LINE_FROM_PAIRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real->B` (LABEL_TAC "line")) THEN
  (* X0.9: the splitting field at time 0 *)
  MP_TAC(SPEC `w:B->bool` CMP_R3_SPLIT) THEN REWRITE_TAC[CMP_R3_SPLIT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `(g':real->B->real^3^3) (&0)`; `lam:real->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "secl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC)) THEN
  (* X0.10: time invariance *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `X:B->real^3`; `xl:B`; `&2`] P2BX0_TIME_INVARIANCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the conclusion *)
  MAP_EVERY EXISTS_TAC
   [`(suba:num->num) o (subb:num->num)`; `((q0:num->B) o (suba:num->num)) o (subb:num->num)`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `X:B->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN GEN_TAC THEN USE_THEN "q0" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `M:real` THEN
    USE_THEN "q0div" (MP_TAC o SPEC `M:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "subge" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    EXISTS_TAC `&2` THEN USE_THEN "rm" ACCEPT_TAC]);;

(* X0F.E5 X0_FINAL: the generalized closed-end X0 at s0 = 0, and the route   *)
(* (ANCIENT_COMPACT ==> X0_FINAL; the LIM statements are proved theorems).   *)

let P2BX0F_SPLIT_FINAL = prove
 (`!w:B->bool.
     LIM_DIST_STATEMENT w w /\ LIM_BALL_STATEMENT w w /\ LIM_KNC_STATEMENT w w /\
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
     ==> P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT w`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BX0F_SPLIT_BODY) THEN
  REWRITE_TAC[P2BX0F_GEN_STATEMENT; P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT; p2b_kview] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`; `pp:num->B`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `&0`; `p:B`; `pp:num->B`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let P2B_SPLIT_AT_INFINITY_FINAL_ROUTE = prove
 (`!w:B->bool. P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BX0F_SPLIT_FINAL THEN
  ASM_REWRITE_TAC[LIM_DIST; LIM_BALL; LIM_KNC; LIM_CURV; LIM_FLOW_COMPLETE_BACK]);;

