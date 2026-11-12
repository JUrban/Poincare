(* ========================================================================= *)
(* Unit pc_p2c_bugq (Part 2C): general-Q lemmas on blow-up limits, shared by *)
(* pc_p2c_blowup2, pc_p2c_horns2 and the Ch 17 units (pc_p3_c171c,           *)
(* pc_rfa_171u): view metrics at two times on a persisting set               *)
(* (P2BU_VIEW_QF_CMP), earlier balls inside later balls and back             *)
(* (P2BU_VIEW_BALL_IN / _OUT), the rescaled scalar curvature at a time s0 of *)
(* a flow limit (P2BU_SCALAR_AT_S0), sec >= 0 and bounded curvature of slice *)
(* limits (P2BU_SLICE_SEC, P2BU_SLICE_CURV_BOUND, P2BU_SLICE_DBOUND), the    *)
(* interval versions of P2BU_UNIF_SCALAR and P2BU_SCALAR_AT_S0 (s in [a,b]   *)
(* instead of s0), and P2HN_FLOW_LIMIT_ON.                                   *)
(* ========================================================================= *)

needs "src/pc_p2c_blowup.ml";;
needs "src/pc_rf_mequiv.ml";;
needs "src/pc_lim_back.ml";;
needs "src/pc_p2b_rmhalf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The view metrics at two times on a persisting set with bounded curvature, *)
(* earlier balls inside later balls and back.                                *)
(* ------------------------------------------------------------------------- *)

(* Two-sided comparison of the view metrics at times s < b on a set W       *)
(* persisting over (a,b] with |Rm| <= K (MT Claim 8.8, P2AP_METRIC_COMPARE), *)
(* unrestricted through the chart Jacobian of the restriction               *)
(* (SNGL_RESTRICT_QF): G(b) <= exp(4K(b-s)) G(s) and back, the metric of s   *)
(* read in the atlas of b by the identity.                                   *)

let P2BU_VIEW_QF_CMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K s y w.
     p2c_regular_view V /\ rfs_persists V W a b /\ &0 <= K /\
     (!t z. a < t /\ t <= b /\ z IN W ==> p3_vrm V t z <= K) /\
     a < s /\ s < b /\ y IN W
     ==> w dot (rfs_vmetric V b y ** w) <=
         exp(&4 * K * (b - s)) *
         (w dot (mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V s) (\x. x)
                   (rfs_vmetric V s) y ** w)) /\
         w dot (mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V s) (\x. x)
                  (rfs_vmetric V s) y ** w) <=
         exp(&4 * K * (b - s)) * (w dot (rfs_vmetric V b y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
                open_in (rfs_vtop V b) (W:A->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) a b` THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `W:A->bool`; `y:A`] SNGL_RESTRICT_QF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^3->real^3` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "J"))) THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^3` o SPEC `w:real^3`) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `K:real`;
                 `s:real`; `y:A`; `v:real^3`] P2AP_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2CV_RV_SVS; REAL_LT_IMP_LE] THEN MATCH_MP_TAC P2CV_RV_REGION THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[P2AP_RMETRIC_VFAM; p2c_vfam] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NE] THEN REWRITE_TAC[ETA_AX]);;

(* Earlier balls inside later balls on a persisting set with |Rm| <= K:     *)
(* the exit argument LIM_PB_BALL_PREIMAGE for the identity from the slice at *)
(* b to the slice at s < b, with the comparison P2BU_VIEW_QF_CMP and a       *)
(* compact closure at b.                                                     *)

let P2BU_SQRT_EXP4 = prove
 (`!c. sqrt(exp(&4 * c)) = exp(&2 * c)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  REWRITE_TAC[REAL_EXP_POS_LE; REAL_POW_2; GSYM REAL_EXP_ADD] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P2BU_VIEW_BALL_IN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K s x z R R0 rho.
     p2c_regular_view V /\ rfs_persists V W a b /\ &0 <= K /\
     (!t y. a < t /\ t <= b /\ y IN W ==> p3_vrm V t y <= K) /\ a < s /\ s < b /\
     compact_in (rfs_vtop V b) (rfs_vtop V b closure_of rfs_vball V b x R) /\
     rfs_vtop V b closure_of rfs_vball V b x R SUBSET W /\
     z IN rfs_vball V b x R0 /\ &0 < rho /\ exp(&2 * K * (b - s)) * rho <= R - R0
     ==> rfs_vball V s z rho SUBSET rfs_vball V b x R /\
         rfs_vball V s z rho SUBSET rfs_vball V b z (exp(&2 * K * (b - s)) * rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < exp(&2 * K * (b - s))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `R0 < R` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < exp(&2 * K * (b - s)) * rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball V b (x:A) R SUBSET topspace(rfs_vtop V b)` ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL; mfd_ball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_vball V b (x:A) R0 SUBSET rfs_vball V b x R` MP_TAC THENL
     [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                   `rfs_vball V b (x:A) R`] CLOSURE_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop V b) (W:A->bool) /\ open_in (rfs_vtop V s) W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) a b` THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `b:real` th) THEN MP_TAC(SPEC `s:real` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop V b) (rfs_vatlas V b) W (rfs_vtop V s) (rfs_vatlas V s) W
               (\y:A. y) (\y. y)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2CV_SLICE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN
  SUBGOAL_THEN
   `!q. q IN rfs_vball V s (z:A) rho
        ==> q IN rfs_vball V b x R /\ q IN rfs_vball V b z (exp(&2 * K * (b - s)) * rho)`
  (fun th -> MESON_TAC[th]) THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
    `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) s`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
    `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`; `x:A`; `z:A`; `R:real`; `R0:real`;
    `exp(&4 * K * (b - s))`; `&0`; `rho:real`; `q:A`] LIM_PB_BALL_PREIMAGE) THEN
  REWRITE_TAC[REAL_SUB_RZERO; SQRT_1; REAL_MUL_LID; REAL_DIV_1; P2BU_SQRT_EXP4] THEN
  REWRITE_TAC[GSYM P2CO_VBALL; IMAGE_ID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_LE_REFL; REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `K:real`;
                   `s:real`; `y:A`; `v:real^3`] P2BU_VIEW_QF_CMP) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    SIMP_TAC[]]);;

(* Later balls inside earlier balls on a persisting set with |Rm| <= K      *)
(* (LIM_PB_BALL_IMAGE for the identity from the slice at b to the slice at  *)
(* s < b, with the comparison P2BU_VIEW_QF_CMP).                             *)

let P2BU_VIEW_BALL_OUT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K s x rho.
     p2c_regular_view V /\ rfs_persists V W a b /\ &0 <= K /\
     (!t y. a < t /\ t <= b /\ y IN W ==> p3_vrm V t y <= K) /\ a < s /\ s < b /\
     x IN W /\ rfs_vball V b x rho SUBSET W
     ==> rfs_vball V b x rho SUBSET rfs_vball V s x (exp(&2 * K * (b - s)) * rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (rfs_vtop V b) (W:A->bool) /\ open_in (rfs_vtop V s) W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) a b` THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `b:real` th) THEN MP_TAC(SPEC `s:real` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop V b) (rfs_vatlas V b) W (rfs_vtop V s) (rfs_vatlas V s) W
               (\y:A. y) (\y. y)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2CV_SLICE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(&4 * K * (b - s))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `&4 * K * (b - s)`] REAL_EXP_MONO_LE) THEN
    REWRITE_TAC[REAL_EXP_0] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) b`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
    `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) b`;
    `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) s`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) s`;
    `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
    `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`; `x:A`; `rho:real`; `&1`;
    `exp(&4 * K * (b - s)) - &1`; `q:A`] LIM_PB_BALL_IMAGE) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (e - &1) = e`; REAL_DIV_1; P2BU_SQRT_EXP4; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM P2CO_VBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `K:real`;
                 `s:real`; `y:A`; `v:real^3`] P2BU_VIEW_QF_CMP) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The rescaled scalar curvature at a time s0 of a flow limit; sec >= 0 and  *)
(* bounded curvature of slice limits.                                        *)
(* ------------------------------------------------------------------------- *)

(* The rescaled scalar curvature at the time s0 of a flow limit is bounded  *)
(* on the rescaled balls at t n by the bound of the limit on the time-0     *)
(* ball of radius A + 1, plus 1, eventually: LIM_BALL_IN at time 0 and the  *)
(* uniform convergence P2BU_UNIF_SCALAR at s0.                               *)

let P2BU_SCALAR_AT_S0 = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t J (top:B topology) atlas g xl W (phi:num->B->A) s0 A Kl Kr.
     (!n. p2c_regular_view (V n)) /\
     p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) J (top,atlas) g xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\ mfd_complete (top,atlas) (g (&0)) /\
     s0 IN J /\ &0 < A /\ &0 <= Kr /\
     (!y. y IN topspace top ==> mfd_rm_norm atlas (g s0) y <= Kr) /\
     (!y. y IN mfd_ball (top,atlas) (g (&0)) xl (A + &1) ==> mfd_scalar atlas (g s0) y <= Kl)
     ==> ?N. !n z. N <= n /\
                   z IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                   ==> z IN topspace(rfs_vtop (V n) (t n + s0 / rfs_vscalar (V n) (t n) (x n))) /\
                       rfs_vscalar (V n) (t n + s0 / rfs_vscalar (V n) (t n) (x n)) z <=
                       (Kl + &1) * rfs_vscalar (V n) (t n) (x n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `!n tau. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau)` (LABEL_TAC "haus") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(MATCH_MP P2CV_RV_SVS (SPEC `n:num`
      (ASSUME `!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)`))) THEN
    REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `xl:B`; `A:real`; `A + &1`] LIM_BALL_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `a < a + &1`] THEN
    MATCH_MP_TAC P2CO_REGULAR_SLICES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "bin")) THEN
  ABBREV_TAC `Kc = (top:B topology) closure_of
                   mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                            ((g:real->B->real^3^3) (&0)) xl (A + &1)` THEN
  SUBGOAL_THEN `compact_in (top:B topology) Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `xl:B`;
                   `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                             ((g:real->B->real^3^3) (&0)) xl (A + &1)`;
                   `A + &1`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                   ((g:real->B->real^3^3) (&0)) xl (A + &1) SUBSET Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s0:real`; `Kc:B->bool`; `Kr:real`; `&1`] P2BU_UNIF_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm atlas ((g:real->B->real^3^3) s0) y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "us")) THEN
  EXISTS_TAC `k0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:A`] THEN STRIP_TAC THEN
  USE_THEN "bin" (MP_TAC o SPECL [`n:num`; `z:A`]) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + N1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(z:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)
                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))` THEN
    ASM_REWRITE_TAC[P2CO_VBALL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  USE_THEN "us" (MP_TAC o SPECL [`n:num`; `w:B`]) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + N1 <= n:num` THEN ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) s0) w <= Kl` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s0 / rfs_vscalar (V n) (t n) (x n))
                  ((phi:num->B->A) n w) / rfs_vscalar (V n) (t n) ((x:num->A) n) <= Kl + &1`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]]);;

(* Slice limits of pinched views with scales Q n -> inf have sec >= 0 (Thm  *)
(* 5.33 on J = {0}); the general form of P2BU_TIME0_SEC.                    *)

let P2BU_SLICE_SEC = prove
 (`!(u:A->bool) (w:B->bool) V x t Q (top:B topology) atlas g0 xl W phi.
     P2C_THM_5_33_STATEMENT u w /\
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) /\
          rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {})) /\
     (!B. ?N. !n. N <= n ==> B < Q n) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi
     ==> !y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g0 y u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `P2C_THM_5_33_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2C_THM_5_33_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`;
    `{&0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `\s:real. (g0:B->real^3^3)`; `xl:B`]) THEN
  REWRITE_TAC[IN_SING] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
      MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN
      MATCH_MP_TAC P2B11_SLICE_TO_FLOW0 THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with"
                                 with _ -> false)) (concl th))) THEN
      REWRITE_TAC[p2c_slice_limit_with] THEN SIMP_TAC[]];
    MESON_TAC[]]);;

(* MT Claim 11.7 in general form (any times t n, scales Q n -> inf): a      *)
(* connected complete slice limit with canonical neighbourhoods for R > 4   *)
(* has bounded curvature (an instance of the slice form of A4), hence      *)
(* R <= D Q n on the rescaled balls of every radius (P2BU_UNIF_D).          *)

let P2BU_SLICE_CURV_BOUND = prove
 (`!(u:A->bool) (w:B->bool) C' eps' V x t Q (top:B topology) atlas g0 xl W (phi:num->B->A).
     P2C_THM_5_33_STATEMENT u w /\
     (!top1 atlas1 g1.
        hausdorff_space (top1:B topology) /\ smooth_manifold_atlas top1 atlas1 /\
        riemannian_metric atlas1 (g1:B->real^3^3) /\ connected_space top1 /\
        mfd_complete (top1,atlas1) g1 /\ apx_sphere_sep top1 atlas1 /\
        (!y u v. y IN topspace top1 /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas1 g1 y u v) /\
        (!y. y IN topspace top1 /\ &4 < mfd_scalar atlas1 g1 y
             ==> ?U. rfs_canonical_nbhd (top1,atlas1) g1 C' eps' y U)
        ==> ?K. !y. y IN topspace top1 ==> mfd_rm_norm atlas1 g1 y <= K) /\
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) /\
          rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {}) /\
          apx_sphere_sep (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))) /\
     (!B. ?N. !n. N <= n ==> B < Q n) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     connected_space top /\ mfd_complete (top,atlas) g0 /\
     (!y. y IN topspace top /\ &4 < mfd_scalar atlas g0 y
          ==> ?U. rfs_canonical_nbhd (top,atlas) g0 C' eps' y U)
     ==> ?D. &0 < D /\
             !A. &0 < A
                 ==> ?N. !n y. N <= n /\
                               y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                               ==> rfs_vscalar (V n) (t n) y <= D * Q n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "a4")
    (CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "canon")))))))) THEN
  SUBGOAL_THEN `!n. p2c_regular_view ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) /\
                    hausdorff_space (rfs_vtop (V n) (t n)) /\
                    smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))`
  (LABEL_TAC "vs") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) n`; `(t:num->real) n`; `(x:num->A) n`]
                  P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC P2BU_SLICE_BASE_IN THEN
    MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
      `phi:num->B->A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`] P2BU_SLICE_SEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
    DISCH_THEN(LABEL_TAC "sec")] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`] P2BU_SEP_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> USE_THEN "vs" (fun th' ->
      MESON_TAC[th; th']));
    DISCH_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas (g0:B->real^3^3)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with" with _ -> false))
          (concl th))) THEN
    REWRITE_TAC[p2c_slice_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "a4" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                 `g0:B->real^3^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "sec" ACCEPT_TAC; USE_THEN "canon" ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_TAC `K:real`)] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `max (&0) K`] P2BU_UNIF_D) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&0 <= max (&0) K`] THEN
    MAP_EVERY X_GEN_TAC [`y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_rm_norm atlas (g0:B->real^3^3) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `a <= K ==> a <= max (&0) K`) THEN ASM_SIMP_TAC[]];
    DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  EXISTS_TAC `&6 * max (&0) K + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bounded curvature of slice limits along a subsequence.                    *)
(* ------------------------------------------------------------------------- *)

(* Slices of views at times tt n with scales Q n -> inf, with compact       *)
(* closures, Shi bounds and a volume bound at the base points: along a      *)
(* subsequence they converge (P2C_CG_COMPACT); the limit, restricted to the *)
(* component of its base point, has canonical neighbourhoods (Claim 11.6,   *)
(* P2BU_CLAIM_11_6_GEN) and hence bounded curvature (the slice form of A4), *)
(* so R <= D Q on the rescaled balls of every radius (P2BU_SLICE_CURV_BOUND). *)

let P2BU_SLICE_DBOUND = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_CG_COMPACT_STATEMENT u w /\ P2C_THM_5_33_STATEMENT u w /\
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps V x tt Q.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) /\
                   rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {}) /\
                   x n IN topspace(rfs_vtop (V n) (tt n)) /\ &0 < Q n) /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!B. ?N. !n. N <= n ==> B < Q n) /\
              (!n y. y IN topspace(rfs_vtop (V n) (tt n)) /\
                     &4 * Q n <= rfs_vscalar (V n) (tt n) y
                     ==> p3_canon_at (V n) C eps y (tt n)) /\
              (!A. &0 < A
                   ==> ?N. !n. N <= n
                               ==> compact_in (rfs_vtop (V n) (tt n))
                                     (rfs_vtop (V n) (tt n) closure_of
                                      rfs_vball (V n) (tt n) (x n) (A * inv(sqrt(Q n))))) /\
              (!A l. &0 < A
                     ==> ?CAl N. !n y. N <= n /\
                                       y IN rfs_vball (V n) (tt n) (x n) (A * inv(sqrt(Q n)))
                                       ==> p3_vderiv2 (V n) l (tt n) y <= CAl * Q n pow (l + 2)) /\
              (?r1 kap N. &0 < r1 /\ &0 < kap /\
                 !n. N <= n
                     ==> ?v. mfd_has_volume (rfs_vtop (V n) (tt n),rfs_vatlas (V n) (tt n))
                               (rfs_vmetric (V n) (tt n))
                               (rfs_vball (V n) (tt n) (x n) (r1 * inv(sqrt(Q n)))) v /\
                             kap * (r1 * inv(sqrt(Q n))) pow 3 <= v)
              ==> ?sub D. p3_subseq sub /\ &0 < D /\
                    !A. &0 < A
                        ==> ?N. !n y. N <= n /\
                                      y IN rfs_vball (V (sub n)) (tt (sub n)) (x (sub n))
                                             (A * inv(sqrt(Q (sub n))))
                                      ==> rfs_vscalar (V (sub n)) (tt (sub n)) y <=
                                          D * Q (sub n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_CLAIM_11_6_GEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen"))))) THEN
  UNDISCH_TAC `P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a4"))) THEN
  EXISTS_TAC `min e1 (e4 / K1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `tt:num->real`; `Q:num->real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "sep") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "canon") (CONJUNCTS_THEN2 (LABEL_TAC "cc")
    (CONJUNCTS_THEN2 (LABEL_TAC "shi") (LABEL_TAC "vol")))))))))) THEN
  SUBGOAL_THEN `K1 * eps <= e4 /\ &1 < &2 * C /\ &0 < K1 * eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `eps <= e4 / K1` THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= k ==> &0 < k`] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n s. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s) = {})
                      ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                          riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)`
  (LABEL_TAC "slices") THENL
   [MATCH_MP_TAC P2CO_REGULAR_SLICES THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  (* compactness (Cor 5.10) *)
  UNDISCH_TAC `P2C_CG_COMPACT_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2C_CG_COMPACT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `tt:num->real`; `Q:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `(tt:num->real) n`; `(x:num->A) n`] P2C_REGULAR_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top0:B topology`
    (X_CHOOSE_THEN `atlas0:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g00:B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl0"))))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub n` (LABEL_TAC "ge") THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* restriction to the component of xl *)
  MP_TAC(ISPECL [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`; `(x:num->A) o (sub:num->num)`;
                 `(tt:num->real) o (sub:num->num)`; `(Q:num->real) o (sub:num->num)`;
                 `top0:B topology`; `atlas0:((B->bool)#(B->real^3))->bool`;
                 `g00:B->real^3^3`; `xl:B`] P2CO_P3_SLICE_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    USE_THEN "slices" (MP_TAC o SPECL [`(sub:num->num) n`; `s:real`]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `top:B topology =
    subtopology top0 {y | mfd_joinable (top0,atlas0:((B->bool)#(B->real^3))->bool) xl y}` THEN
  ABBREV_TAC `atlas = restrict_atlas (atlas0:((B->bool)#(B->real^3))->bool)
                        {y | mfd_joinable (top0:B topology,atlas0) xl y}` THEN
  ABBREV_TAC `g0 = restrict_metric (atlas0:((B->bool)#(B->real^3))->bool)
                     {y | mfd_joinable (top0:B topology,atlas0) xl y} (g00:B->real^3^3)` THEN
  REWRITE_TAC[P2C_SLICE_LIMIT_WITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A` (LABEL_TAC "sl"))))
    ASSUME_TAC) THEN
  (* Claim 11.6 on the limit *)
  USE_THEN "gen" (MP_TAC o SPECL [`C:real`; `eps:real`; `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
    `(x:num->A) o (sub:num->num)`; `(tt:num->real) o (sub:num->num)`;
    `(Q:num->real) o (sub:num->num)`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
    `phi:num->B->A`]) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
      USE_THEN "shi" (MP_TAC o C MP (ASSUME `&0 < A`) o SPECL [`A:real`; `l:num`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `CAl:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "N"))) THEN
      MAP_EVERY EXISTS_TAC [`CAl:real`; `N:num`] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      USE_THEN "views" (fun th -> MESON_TAC[th])];
    DISCH_THEN(LABEL_TAC "c116")] THEN
  (* Claim 11.7 *)
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`; `&2 * C`; `K1 * eps`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
    `(x:num->A) o (sub:num->num)`; `(tt:num->real) o (sub:num->num)`;
    `(Q:num->real) o (sub:num->num)`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
    `phi:num->B->A`] P2BU_SLICE_CURV_BOUND) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [MAP_EVERY X_GEN_TAC [`top1:B topology`; `atlas1:((B->bool)#(B->real^3))->bool`;
                           `g1:B->real^3^3`] THEN STRIP_TAC THEN
      USE_THEN "a4" (MP_TAC o SPECL [`&2 * C`; `K1 * eps`; `top1:B topology`;
        `atlas1:((B->bool)#(B->real^3))->bool`; `g1:B->real^3^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN NO_TAC;
      MP_TAC(ISPECL [`Q:num->real`; `sub:num->num`] P2BU_QINF_SUBSEQ) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC;
      USE_THEN "views" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `D:real`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interval versions of P2BU_UNIF_SCALAR (pc_p2c_blowup) and                 *)
(* P2BU_SCALAR_AT_S0: the time s ranges over [a,b] (a subinterval of J)      *)
(* instead of the single time s0, uniformly (the convergence clause of       *)
(* p2c_flow_limit_with is used on [a,b] instead of [s0,s0]).                 *)
(* ------------------------------------------------------------------------- *)

(* The rescaled scalar curvatures converge uniformly on K x [a,b]. *)

let P2BU_UNIF_SCALAR_INT = prove
 (`!V x t Q J (top:B topology) atlas g xl W (phi:num->B->A) a b K Kl e.
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3))) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 <= Kl /\
     (!s y u v. a <= s /\ s <= b /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                ==> abs(mfd_sectional atlas (g s) y u v) <= Kl) /\ &0 < e
     ==> ?N. !k s y. N <= k /\ a <= s /\ s <= b /\ y IN K
                   ==> phi k y IN topspace(rfs_vtop (V k) (t k + s / Q k)) /\
                       abs(mfd_scalar atlas (g s) y -
                           mfd_scalar (rfs_vatlas (V k) (t k + s / Q k))
                                      (rfs_vmetric (V k) (t k + s / Q k)) (phi k y) / Q k) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "kl") ASSUME_TAC))))))) THEN
  REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv"))))))))) THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K0 = sqrt(Cr * Kl pow 2)` THEN
  SUBGOAL_THEN `&0 <= K0 /\ Cr * Kl pow 2 = K0 pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    SUBGOAL_THEN `&0 <= Cr * Kl pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `delta = min (&1 / &10) (e / (&73 * (&1 + abs K0)))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &10 /\ &8 * &9 * (&1 + abs K0) * delta < e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 + abs K0` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e / (&73 * (&1 + abs K0))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
     [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `delta * &73 * (&1 + abs K0) <= e` ASSUME_TAC THENL
     [SUBGOAL_THEN `delta <= e / (&73 * (&1 + abs K0))` MP_TAC THENL
       [EXPAND_TAC "delta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &73`];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      EXPAND_TAC "delta" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < (&1 + abs K0) * delta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `delta * &73 * (&1 + abs K0) <= e` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `2`; `delta pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y0:B`] THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o C MP (ASSUME `k0 <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `psi:A->B` o
     C MP (CONJ (ASSUME `a <= s:real`) (ASSUME `s <= b:real`)) o SPEC `s:real`)
    (MP_TAC o SPECL [`s:real`; `y0:B`]))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [USE_THEN "riem" MATCH_MP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; IN_REAL_INTERVAL] o
      check (fun th -> concl th = `real_interval[a,b] SUBSET (J:real->bool)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:B) IN (W:num->B->bool) k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:B) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `(W:num->B->bool) k` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S0 = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                         (FST(chart_at atlas y0))` THEN
  ABBREV_TAC `G0 = metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas (y0:B))
                     ((g:real->B->real^3^3) s)` THEN
  ABBREV_TAC `yc = SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)) y0` THEN
  SUBGOAL_THEN `metric_field (S0:real^3->bool) (G0:real^3->real^3^3) /\ (yc:real^3) IN S0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "G0"; "yc"] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->B->real^3^3) s)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc <= K0 pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `Cr * Kl pow 2 = K0 pow 2`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "lrm_deriv_norm2" with _ -> false))
          (concl th) && is_forall(concl th))) THEN
    EXISTS_TAC `S0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "kl" (MP_TAC o C MP (CONJ (ASSUME `a <= s:real`) (CONJ (ASSUME `s <= b:real`)
                                   (CONJ (ASSUME `(y0:B) IN topspace top`)
                                         (ASSUME `~collinear {vec 0,u:real^3,v}`)))) o
                   SPECL [`s:real`; `y0:B`; `u:real^3`; `v:real^3`]) THEN
    REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:num->B->A) k y0 IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) k`;
                   `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k)`;
                   `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k)`;
                   `(phi:num->B->A) k`; `psi:A->B`; `y0:B`] P2B_DIFFEO_IMAGE_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `t (k:num) + s / Q k`; `(phi:num->B->A) k y0`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k)`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k)`;
                 `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`; `(Q:num->real) k`;
                 `y0:B`] P2CP_APPROX_CURV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Gk = \z. (Q:num->real) k %%
                   rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k))
                     ((phi:num->B->A) k o chart_inv (chart_at (atlas:((B->bool)#(B->real^3))->bool)
                                                         (y0:B)))
                     (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k)) z` THEN
  ABBREV_TAC `S = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                        (FST(chart_at atlas y0) INTER (W:num->B->bool) k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "scal") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `metric_field (S:real^3->bool) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `S0:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["S"; "S0"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) < delta /\
                &0 <= sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `S:real^3->bool`; `G0:real^3->real^3^3`; `Gk:real^3->real^3^3`;
                 `yc:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  USE_THEN "scal" (fun th -> REWRITE_TAC[SYM th]) THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) s) y0 = lscalar (G0:real^3->real^3^3) yc`
  SUBST1_TAC THENL [MAP_EVERY EXPAND_TAC ["G0"; "yc"] THEN REWRITE_TAC[mfd_scalar]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 * &9 * (&1 + abs K0) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) <=
                &8 * &9 * (&1 + abs K0) * delta` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* For every A, eventually R <= (Kl + 1) Q on the rescaled A-ball at t n at  *)
(* the times t n + s / Q n for all s in [a,b].                               *)

let P2BU_SCALAR_ON_INT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t J (top:B topology) atlas g xl W (phi:num->B->A) a b A Kl Kr.
     (!n. p2c_regular_view (V n)) /\
     p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) J (top,atlas) g xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\ mfd_complete (top,atlas) (g (&0)) /\
     real_interval[a,b] SUBSET J /\ &0 < A /\ &0 <= Kr /\
     (!s y. a <= s /\ s <= b /\ y IN topspace top ==> mfd_rm_norm atlas (g s) y <= Kr) /\
     (!s y. a <= s /\ s <= b /\ y IN mfd_ball (top,atlas) (g (&0)) xl (A + &1)
            ==> mfd_scalar atlas (g s) y <= Kl)
     ==> ?N. !n s z. N <= n /\ a <= s /\ s <= b /\
                   z IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                   ==> z IN topspace(rfs_vtop (V n) (t n + s / rfs_vscalar (V n) (t n) (x n))) /\
                       rfs_vscalar (V n) (t n + s / rfs_vscalar (V n) (t n) (x n)) z <=
                       (Kl + &1) * rfs_vscalar (V n) (t n) (x n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> s IN (J:real->bool)` (LABEL_TAC "inJ") THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET (J:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `!n tau. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau)` (LABEL_TAC "haus") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(MATCH_MP P2CV_RV_SVS (SPEC `n:num`
      (ASSUME `!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)`))) THEN
    REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `xl:B`; `A:real`; `A + &1`] LIM_BALL_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `a < a + &1`] THEN
    MATCH_MP_TAC P2CO_REGULAR_SLICES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "bin")) THEN
  ABBREV_TAC `Kc = (top:B topology) closure_of
                   mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                            ((g:real->B->real^3^3) (&0)) xl (A + &1)` THEN
  SUBGOAL_THEN `compact_in (top:B topology) Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `xl:B`;
                   `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                             ((g:real->B->real^3^3) (&0)) xl (A + &1)`;
                   `A + &1`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                   ((g:real->B->real^3^3) (&0)) xl (A + &1) SUBSET Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `a:real`; `b:real`; `Kc:B->bool`; `Kr:real`; `&1`] P2BU_UNIF_SCALAR_INT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm atlas ((g:real->B->real^3^3) s) y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "us")) THEN
  EXISTS_TAC `k0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `z:A`] THEN
  STRIP_TAC THEN
  USE_THEN "bin" (MP_TAC o SPECL [`n:num`; `z:A`]) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + N1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(z:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)
                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))` THEN
    ASM_REWRITE_TAC[P2CO_VBALL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  USE_THEN "us" (MP_TAC o SPECL [`n:num`; `s:real`; `w:B`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [UNDISCH_TAC `k0 + N1 <= n:num` THEN ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) s) w <= Kl` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / rfs_vscalar (V n) (t n) (x n))
                  ((phi:num->B->A) n w) / rfs_vscalar (V n) (t n) ((x:num->A) n) <= Kl + &1`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* p3_flow_limit gives p3_flow_limit_on on the time set (-Tl,0].             *)
(* ------------------------------------------------------------------------- *)

(* p3_flow_limit gives p3_flow_limit_on on the time set (-Tl,0].              *)

let P2HN_FLOW_LIMIT_ON = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl Tl.
     p3_flow_limit V x t Q (top,atlas) g xl Tl
     ==> p3_flow_limit_on V x t Q {s | --Tl < s /\ s <= &0} (top,atlas) g xl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit; p3_flow_limit_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `ts:num->real`
    (X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "cl")))))))))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `a <= b` THENL
   [SUBGOAL_THEN `--Tl < a /\ b <= &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `real_interval[a,b] SUBSET {s | --Tl < s /\ s <= &0}` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `a:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "cl" (MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`; `a:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
    EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk"))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "dif" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN USE_THEN "lk" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    USE_THEN "cl" (MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
    EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

