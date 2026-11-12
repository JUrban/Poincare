(* ========================================================================= *)
(* pc_p2b_tubelim2: evolving 2eps-necks of normalized length 1/2 in the      *)
(* limit view at the points of large scalar curvature (MT Claim 10.8 in      *)
(* corrected form): P2BTL_LIM_ENECK.  The strong eps-neck of phi k (y),      *)
(* restricted to the 19/10 eps domain and to the normalized times (-3/4,0],  *)
(* lies in the image of a fixed W m and over a box of pc_p2b_tubelim; the    *)
(* closeness of the views there is converted to the approximant side, and    *)
(* P2B9_ENECK_CORE (pc_p2b_979) transfers it to the limit view.              *)
(* ========================================================================= *)

needs "src/pc_p2b_tubelim.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Restricting an evolving neck to a shorter normalized length.             *)
(* ------------------------------------------------------------------------- *)

let P2BTL_EVNECK_LEN_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t len len' (e:real^3->A).
     rfs_evolving_neck V eps x t len e /\ &0 < len' /\ len' <= len
     ==> rfs_evolving_neck V eps x t len' e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BN_EVOLVING_NECK_ALT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  SUBGOAL_THEN `&0 < rfs_vscalar (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[P2BN_RFS_VSCALAR]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t - len' / rfs_vscalar (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x` THEN
    ASM_REWRITE_TAC[REAL_ARITH `t - a <= t - b <=> b <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    UNDISCH_TAC `rfs_close_fam (rfs_kreg eps) eps {s | --len < s /\ s <= &0}
                   (rfs_neck_dom eps) cylinder_flow
                   (\s y. rfs_vscalar (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x %%
                      rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) (e:real^3->A)
                                   (rfs_vmetric V (t + s / rfs_vscalar V t x)) y)` THEN
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* General lemmas.  Restricting an evolving neck of a regular view to       *)
(* a larger eps and a shorter length; monotonicity of an exhaustion; the    *)
(* closeness on one slice converted from the limit side (rfs_pullback       *)
(* through the limit charts) to the approximant side at the scale Q; the    *)
(* resulting p3_view_close over a box (time-s diffeos of P2BTL_TIME_DIFFEO).*)
(* ------------------------------------------------------------------------- *)

let P2BTL_EVNECK_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps eps' x t len len' (e:real^3->A).
     p2c_regular_view V /\ rfs_evolving_neck V eps x t len e /\
     eps <= eps' /\ &0 < len' /\ len' <= len
     ==> rfs_evolving_neck V eps' x t len' e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rfs_evolving_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) eps x t len' (e:real^3->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BTL_EVNECK_LEN_MONO THEN EXISTS_TAC `len:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFS_EVOLVING_NECK_EPS_MONO THEN EXISTS_TAC `eps:real` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `len':real`;
                 `e:real^3->A`; `s:real`] P2B9_REGULAR_NECK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2BTL_W_MONO = prove
 (`!(top:B topology) (W:num->B->bool) m k.
     (!k. open_in top (W k) /\ top closure_of W k SUBSET W (SUC k)) /\ m <= k
     ==> W m SUBSET W k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\m n. (W:num->B->bool) m SUBSET W n` TRANSITIVE_STEPWISE_LE) THEN
  BETA_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MESON_TAC[SUBSET_TRANS];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) n` THEN
      ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BTL_RENORM_ARITH = prove
 (`!Q delta m. &1 <= Q /\ &0 < delta
     ==> &0 < delta / &2 pow m /\
         (&1 + &1 / Q) pow m * (delta / &2 pow m) pow 2 <= delta pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow m /\ &1 <= &2 pow m /\ &0 < Q` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &1 / Q) pow m <= &2 pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN
    SUBGOAL_THEN `&0 <= &1 / Q /\ &1 / Q <= &1` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow m * (delta / &2 pow m) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. &0 < p ==> p * (delta / p) pow 2 = delta pow 2 / p` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN `~(p = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let P2BTL_ETA_ARITH = prove
 (`!M D. &0 <= M /\ &0 < D ==> ?eta. &0 < eta /\ eta <= &1 / &4 /\ M * eta < D`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min (&1 / &4) (D / (M + &1))` THEN
  SUBGOAL_THEN `&0 < D / (M + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M * (D / (M + &1)) < D` ASSUME_TAC THENL
   [SUBGOAL_THEN `M * (D / (M + &1)) = (M * D) / (M + &1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < M + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `M * (D / (M + &1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let P2BTL_SLICE_CLOSE = prove
 (`!m. ?M. &0 <= M /\
     !top atlas (g:B->real^3^3) top' atlas' (g':A->real^3^3) X (phi:B->A) psi S Q delta d.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
        mfd_diffeo top atlas X top' atlas' (IMAGE phi X) phi psi /\
        open_in top' S /\ S SUBSET IMAGE phi X /\ &1 <= Q /\ &0 < delta /\
        d <= &1 / &4 /\ M * d < delta pow 2 /\
        (!y. y IN IMAGE psi S
             ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g)
                             (rfs_pullback atlas' (phi o chart_inv (chart_at atlas y)) g')
                             (SND(chart_at atlas y) y) <= d)
        ==> (?psi'. mfd_diffeo top' atlas' S top atlas (IMAGE psi S) psi psi') /\
            rfs_mclose m delta atlas' S (\y. Q %% g' y)
                       (\y. Q %% mfd_pullback_metric atlas' atlas psi g y)`,
  GEN_TAC THEN
  X_CHOOSE_THEN `M0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "flip"))
    (SPEC `m:num` P2BT_LCK_FLIP) THEN
  EXISTS_TAC `(&2 pow m) pow 2 * M0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "sm smp rm rmp df so ss q1 dp d4 md hd" THEN
  USE_THEN "df" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `mfd_diffeo top' (atlas':((A->bool)#(A->real^3))->bool) S top
                  (atlas:((B->bool)#(B->real^3))->bool) (IMAGE (psi:A->B) S) psi (phi:B->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:B->A) X`; `X:B->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `phi:B->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`Q:real`; `delta:real`; `m:num`] P2BTL_RENORM_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC P2BC_MCLOSE_RENORM THEN
  MAP_EVERY EXISTS_TAC [`top':A topology`; `top:B topology`; `S:A->bool`;
                        `IMAGE (psi:A->B) S`; `phi:B->A`; `m:num`;
                        `delta / &2 pow m`; `&1`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL; LE_REFL; REAL_LT_01] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CMUL_LID; ETA_AX; rfs_mclose] THEN
  EXISTS_TAC `M0 * d` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `&0 < (&2 pow m) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "flip" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `top':A topology`; `X:B->bool`; `phi:B->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:A) IN S` THEN UNDISCH_TAC `S SUBSET IMAGE (phi:B->A) X` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                 `X:B->bool`; `phi:B->A`; `psi:A->B`; `(psi:A->B) x`; `m:num`]
                P2BT_LIM_CLOSE_CONVERT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN S` THEN UNDISCH_TAC `S SUBSET IMAGE (phi:B->A) X` THEN
    UNDISCH_TAC `IMAGE (psi:A->B) (IMAGE (phi:B->A) X) SUBSET X` THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "hd" MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

let P2BTL_VIEW_CLOSE_BOX = prove
 (`!delta. &0 < delta
     ==> ?eta. &0 < eta /\
           !(Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))
            (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            X a (phi:B->A) psi S Q J.
              p2c_regular_view Vl /\ p2c_regular_view V' /\
              rfs_persists Vl X a (&0) /\ rfs_persists V' (IMAGE phi X) a (&0) /\
              mfd_diffeo (rfs_vtop Vl (&0)) (rfs_vatlas Vl (&0)) X
                         (rfs_vtop V' (&0)) (rfs_vatlas V' (&0)) (IMAGE phi X) phi psi /\
              &1 <= Q /\ S SUBSET IMAGE phi X /\ ~(S = {}) /\
              (!s. s IN J
                   ==> a < s / Q /\ s / Q <= &0 /\ open_in (rfs_vtop V' (s / Q)) S /\
                       !y. y IN IMAGE psi S
                           ==> lck_dist2 (rfs_kreg delta)
                                 (metric_local (rfs_vatlas Vl (s / Q))
                                    (chart_at (rfs_vatlas Vl (s / Q)) y) (rfs_vmetric Vl (s / Q)))
                                 (rfs_pullback (rfs_vatlas V' (s / Q))
                                    (phi o chart_inv (chart_at (rfs_vatlas Vl (s / Q)) y))
                                    (rfs_vmetric V' (s / Q)))
                                 (SND(chart_at (rfs_vatlas Vl (s / Q)) y) y) < eta)
              ==> p3_view_close V' (&0) Q S Vl (&0) Q psi J delta`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))
    (SPEC `rfs_kreg delta` P2BTL_SLICE_CLOSE) THEN
  MP_TAC(SPECL [`M:real`; `delta pow 2`] P2BTL_ETA_ARITH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "rl rv pl pv df q1 ss sne hj" THEN
  REWRITE_TAC[p3_view_close; REAL_ADD_LID] THEN
  SUBGOAL_THEN `&0 < Q` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  USE_THEN "hj" (MP_TAC o C MATCH_MP (ASSUME `(s:real) IN J`)) THEN
  ABBREV_TAC `tau = s / Q` THEN INTRO_TAC "at t0 so hb" THEN
  USE_THEN "df" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `?x0:A. x0 IN S` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) x0 IN X` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:A) IN S` THEN UNDISCH_TAC `S SUBSET IMAGE (phi:B->A) X` THEN
    UNDISCH_TAC `IMAGE (psi:A->B) (IMAGE (phi:B->A) X) SUBSET X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop Vl tau) (rfs_vatlas Vl tau) X
               (rfs_vtop V' tau) (rfs_vatlas V' tau) (IMAGE (phi:B->A) X) phi psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BTL_TIME_DIFFEO THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop Vl tau) (rfs_vatlas Vl tau) /\
    open_in (rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                         (real->B->real^3^3)) tau) X`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "pl" (MP_TAC o REWRITE_RULE[P2BN_PERSISTS_ALT]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop V' tau)
      (rfs_vatlas (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) tau)`
  ASSUME_TAC THENL
   [USE_THEN "pv" (MP_TAC o REWRITE_RULE[P2BN_PERSISTS_ALT]) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas Vl tau)
      (rfs_vmetric (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                       (real->B->real^3^3)) tau)`
  ASSUME_TAC THENL
   [USE_THEN "rl" (MP_TAC o SPEC `tau:real` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                  (real->B->real^3^3)) tau`; `X:B->bool`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(psi:A->B) x0 IN X` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas V' tau)
      (rfs_vmetric (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) tau)`
  ASSUME_TAC THENL
   [USE_THEN "rv" (MP_TAC o SPEC `tau:real` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tau`; `S:A->bool`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x0:A) IN S` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sc" (MP_TAC o SPECL
    [`rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                   (real->B->real^3^3)) tau`;
     `rfs_vatlas (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                     (real->B->real^3^3)) tau`;
     `rfs_vmetric (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                      (real->B->real^3^3)) tau`;
     `rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) tau`;
     `rfs_vatlas (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) tau`;
     `rfs_vmetric (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) tau`;
     `X:B->bool`; `phi:B->A`; `psi:A->B`; `S:A->bool`; `Q:real`; `delta:real`;
     `eta:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "hb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The neck transfer with a uniform delta (P2B9_ENECK_CORE with the         *)
(* source a 19/10 eps-neck of normalized length 3/4, the target eps1 =      *)
(* 2 eps and L = 1/2; d0 = (19/10 eps)^2, M from P2B_REQ_LRG_BASE and K0    *)
(* from P2B9_NECK_CENTRE_UNIFORM).                                           *)
(* ------------------------------------------------------------------------- *)

let P2BTL_NECK_FIX_HALF = prove
 (`!eps. &0 < eps /\ eps <= &1 / &100
     ==> ?delta. &0 < delta /\
           !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t (e:real^3->A)
            (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))
            t' Q' (psi:A->B).
              p2c_regular_view V /\
              rfs_evolving_neck V (&19 / &10 * eps) x t (&3 / &4) e /\
              (!s. --(&3 / &4) < s /\ s <= &0
                   ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                             (rfs_vatlas V' (t' + s / Q')) /\
                       riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                         (rfs_vmetric V' (t' + s / Q'))) /\
              p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom (&19 / &10 * eps)))
                V' t' Q' psi {s | --(&3 / &4) < s /\ s <= &0} delta
              ==> rfs_evolving_neck V' (&2 * eps) (psi x) t' (&1 / &2) (psi o e)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP P2B9_NECK_CENTRE_UNIFORM P2B_REQ_LRG_RM_NEAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "cu" o INST_TYPE [`:A`,`:A`])) THEN
  MP_TAC(SPEC `rfs_kreg (&2 * eps)`
    (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(SPECL [`&19 / &10 * eps`; `&2 * eps`; `M:real`; `K0:real`; `&1 / &2`; `&3 / &4`;
                `rfs_kreg (&2 * eps) + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "rv nk tg vc" THEN
  SUBGOAL_THEN `&0 <= &19 / &10 * eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `&19 / &10 * eps`; `x:A`; `t:real`; `&3 / &4`;
                 `e:real^3->A`] P2B9_NECK_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sup")))) THEN
  MATCH_MP_TAC P2B9_ENECK_CORE THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg (&2 * eps)`; `M:real`; `K0:real`; `&19 / &10 * eps`;
                        `&3 / &4`; `delta:real`; `(&19 / &10 * eps) pow 2`;
                        `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `t:real`; `Q':real`] THEN
  CONJ_TAC THENL [USE_THEN "base" ACCEPT_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    SUBGOAL_THEN `(&19 / &10 * eps) pow 2 <= (&1 / &2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d1:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN USE_THEN "sup" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "cu" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`&19 / &10 * eps`; `&3 / &4`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One approximant.  A point of the cutset lies on a window neck EN sig     *)
(* below A1 + 9/10 h / eps (P2BTL_WINDOW_POS); scalar curvature at least    *)
(* 65 C^2 there puts sig at arc length at least 6/5 h / eps beyond the      *)
(* level s0 (P2BTL_BEYOND_LEVEL, P2BT_PROFILE_NEAR_R with K = 36 C^2); the  *)
(* 19/10 eps-domain of an eps-neck lies in the ball of radius 3/5 h / eps   *)
(* about its centre (P2BTL_NECK_IN_BALL).                                    *)
(* ------------------------------------------------------------------------- *)

let P2BTL_DIST_ARITH = prove
 (`!h eps sv d1 d2 D A1.
     &0 < h /\ &0 < eps /\ eps <= &1 / &1000 /\ abs sv < inv(&2 * eps) /\
     D <= d1 + d2 /\ d1 < A1 /\
     d2 <= (&1 + &1 / &100) * h * (abs sv + sqrt(&2) * pi)
     ==> D < A1 + &9 / &10 * h * inv eps`,
  REPEAT STRIP_TAC THEN MP_TAC P2BT_SQRT2_PI THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1000 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1000`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * (abs sv + sqrt(&2) * pi) <= h * (inv eps / &2 + &24 / &5) /\
                h * &1000 <= h * inv eps` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BTL_BALL_ARITH = prove
 (`!h eps sv d.
     &0 < h /\ &0 < eps /\ eps <= &1 / &1000 /\ abs sv < &10 / &19 * inv eps /\
     d <= (&1 + &1 / &100) * h * (abs sv + sqrt(&2) * pi)
     ==> d < &3 / &5 * h * inv eps`,
  REPEAT STRIP_TAC THEN MP_TAC P2BT_SQRT2_PI THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1000 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1000`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * (abs sv + sqrt(&2) * pi) <= h * (&10 / &19 * inv eps + &24 / &5) /\
                h * &1000 <= h * inv eps` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BTL_WINDOW_POS = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      gamma s0 s1 EN A1 w.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        w IN p2bt_cutset eps V gamma EN s0 s1 A1
        ==> ?sig y. s0 <= sig /\ sig <= s1 /\
                    y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\ w = EN sig y /\
                    &99 / &100 * mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig) <=
                    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) w /\
                    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) w <=
                    &101 / &100 * mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig) /\
                    (sig - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                          (gamma(&0)) (gamma(&1)) <
                    A1 + &9 / &10 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                                        (gamma sig))) * inv eps`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  EXISTS_TAC `min e1 (min e2 (&1 / &1000))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm c1 one wc" THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= &1 / &1000` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)) /\
    smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
    riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\ &0 < s0 /\ s1 < &1`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "nk")
    (CONJUNCTS_THEN2 (LABEL_TAC "tb") (K ALL_TAC)))) THEN
  SUBGOAL_THEN
   `(w:A) IN p2bt_tube eps EN s0 s1 /\
    (w:A) IN mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&0),rfs_vatlas V (&0))
                      (rfs_vmetric V (&0)) ((gamma:real->A) s0) A1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:A) IN p2bt_cutset eps (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma EN s0 s1 A1` THEN
    REWRITE_TAC[p2bt_cutset; IN_INTER];
    ALL_TAC] THEN
  USE_THEN "tb" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN p2bt_tube eps EN s0 s1`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `sig:real` (X_CHOOSE_THEN `y:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))))) THEN
  MAP_EVERY EXISTS_TAC [`sig:real`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "nk" (MP_TAC o SPEC `sig:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ abs(apx_sval y) < inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      UNDISCH_TAC `apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) SUBSET rfs_neck_dom eps` THEN
      SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "nh" (MP_TAC o SPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ctx" (MP_TAC o SPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  UNDISCH_TAC `(gamma:real->A) sig IN IMAGE ((EN:real->real^3->A) sig) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  UNDISCH_TAC `apx_eng_n2 (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0)) (rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                 eps (&1 / &100)` THEN
  REWRITE_TAC[apx_eng_n2] THEN
  DISCH_THEN(MP_TAC o SPECL [`(gamma:real->A) sig`; `(EN:real->real^3->A) sig`;
                             `y0:real^3`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_ONE_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  USE_THEN "dist" (MP_TAC o SPECL [`s0:real`; `sig:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `(w:A) IN mfd_ball (rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),rfs_vatlas V (&0))
                   (rfs_vmetric V (&0)) ((gamma:real->A) s0) A1` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `(gamma:real->A) s0`; `w:A`; `(gamma:real->A) sig`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `w:A`; `(gamma:real->A) sig`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 < inv(sqrt(mfd_scalar (rfs_vatlas (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (rfs_vmetric V (&0))
      ((gamma:real->A) sig)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    UNDISCH_TAC `rfs_neck (rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),rfs_vatlas V (&0))
                   (rfs_vmetric V (&0)) eps ((gamma:real->A) sig) ((EN:real->real^3->A) sig)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BTL_DIST_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`apx_sval(y:real^3)`;
    `mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
              ((gamma:real->A) s0) w`;
    `mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
              ((gamma:real->A) sig) w`] THEN
  ASM_REWRITE_TAC[]);;

let P2BTL_BEYOND_LEVEL = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      gamma s0 s1 EN sig y.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= sig /\ sig <= s1 /\ y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
        &65 * C pow 2 <= mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN sig y)
        ==> &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) *
            inv eps <=
            (sig - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                  (gamma(&0)) (gamma(&1))`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pn"))
    (INST_TYPE [`:A`,`:A`] P2BT_PROFILE_NEAR_R) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min e0 e1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm c1 one sg0 sg1 ys r65" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C /\ &0 < C pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) /\
    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) s0) = &32 * C pow 2 /\
    &0 < s0 /\ s1 < &1`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "nh" (MP_TAC o SPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&64 * C pow 2 <=
                mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) sig)`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&36 * C pow 2) = &6 * C /\ sqrt(&64 * C pow 2) = &8 * C`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(MESON[POW_2_SQRT] `!x y. &0 <= x /\ y = x pow 2 ==> sqrt y = x`) THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RING]);
    ALL_TAC] THEN
  (* the level argument: within 99/100 inv(6 C) / eps of s0 the curvature is <= 54 C^2 *)
  SUBGOAL_THEN
   `&99 / &100 * inv(&6 * C) * inv eps <=
    (sig - s0) * mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                          ((gamma:real->A)(&0)) (gamma(&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(b < a ==> F) ==> a <= b`) THEN DISCH_TAC THEN
    USE_THEN "pn" (MP_TAC o SPECL
      [`eps:real`; `C:real`; `A:real`; `n:num`;
       `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `t:real`; `Q:real`;
       `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `s0:real`; `sig:real`;
       `&36 * C pow 2`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN `abs(sig - s0) = sig - s0` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(sqrt(mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
       (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) sig))) <= inv(&8 * C)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&8 * C = sqrt(&64 * C pow 2)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 <= inv C * inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&6 / &5 * inv(&8 * C) * inv eps` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&99 / &100 * inv(&6 * C) * inv eps` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC);;

let P2BTL_NECK_IN_BALL = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps w (e:real^3->A).
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps w e
        ==> IMAGE e (rfs_neck_dom (&19 / &10 * eps)) SUBSET
            mfd_ball (top,atlas) g w (&3 / &5 * inv(sqrt(mfd_scalar atlas g w)) * inv eps)`,
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  EXISTS_TAC `min e2 (&1 / &1000)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm hs sm rm nk" THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  USE_THEN "nk" (fun th -> MP_TAC th THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC) THEN
  UNDISCH_TAC `(w:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps /\ apx_sval y1 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps /\ abs(apx_sval z) < &10 / &19 * inv eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&19 / &10 * eps`] APX_NECK_DOM_MONO) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^3) IN rfs_neck_dom (&19 / &10 * eps)` THEN SET_TAC[];
      UNDISCH_TAC `(z:real^3) IN rfs_neck_dom (&19 / &10 * eps)` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `inv(&19 / &10 * eps) = &10 / &19 * inv eps` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `apx_eng_n2 top atlas (g:A->real^3^3) eps (&1 / &100)` THEN
  REWRITE_TAC[apx_eng_n2] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:A`; `e:real^3->A`; `y1:real^3`; `z:real^3`]) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BTL_BALL_ARITH THEN EXISTS_TAC `apx_sval(z:real^3)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The covering.  P2BTL_WINDOW_LIFT: for K > 0 there are m and N such       *)
(* that for k >= N, every point within 3/5 h_w / eps (time-0 approximant    *)
(* metric) of a window point EN sig y beyond the level, below              *)
(* A1 + 9/10 h / eps and with R(gamma sig) <= K, is phi k of a point of    *)
(* W m (margins by P2BT_WINDOW_FAR, a deep curve from the base point by     *)
(* P2BT_REACH_ONE, the lifting clause of p2bt_lim).  P2BTL_NECK_COVER: the  *)
(* same for the ball about phi k P when 65 C^2 <= R(phi k P) <= K           *)
(* (P2BTL_WINDOW_POS, P2BTL_BEYOND_LEVEL).                                  *)
(* ------------------------------------------------------------------------- *)

let P2BTL_WINDOW_LIFT = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
              ==> !K. &0 < K
                      ==> ?m N. !k sig y q.
                            N <= k /\ s0 (sub k) <= sig /\ sig <= s1 (sub k) /\
                            y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
                            &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas (V (sub k)) (&0))
                                         (rfs_vmetric (V (sub k)) (&0)) (gamma (sub k) sig))) *
                            inv eps <=
                            (sig - s0 (sub k)) *
                            mfd_dist (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0))
                                     (rfs_vmetric (V (sub k)) (&0))
                                     (gamma (sub k) (&0)) (gamma (sub k) (&1)) /\
                            (sig - s0 (sub k)) *
                            mfd_dist (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0))
                                     (rfs_vmetric (V (sub k)) (&0))
                                     (gamma (sub k) (&0)) (gamma (sub k) (&1)) <
                            A1 + &9 / &10 * inv(sqrt(mfd_scalar (rfs_vatlas (V (sub k)) (&0))
                                         (rfs_vmetric (V (sub k)) (&0)) (gamma (sub k) sig))) *
                                 inv eps /\
                            mfd_scalar (rfs_vatlas (V (sub k)) (&0)) (rfs_vmetric (V (sub k)) (&0))
                                       (gamma (sub k) sig) <= K /\
                            q IN mfd_ball (rfs_vtop (V (sub k)) (&0),
                                           rfs_vatlas (V (sub k)) (&0))
                                          (rfs_vmetric (V (sub k)) (&0)) (EN (sub k) sig y)
                                 (&3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas (V (sub k)) (&0))
                                              (rfs_vmetric (V (sub k)) (&0)) (EN (sub k) sig y))) *
                                  inv eps)
                            ==> ?y'. y' IN W m /\ phi k y' = q`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "reach")) o
    MATCH_MP P2BT_REACH_ONE) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wfar"))
    (INST_TYPE [`:A`,`:A`] P2BT_WINDOW_FAR) THEN
  EXISTS_TAC `min (min e0 e1) (&1 / &1000)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx" THEN X_GEN_TAC `K:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= &1 / &1000` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "lctx" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bt_lctx]) THEN
  SUBGOAL_THEN `&0 < C pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* margins of the window necks with R <= K *)
  USE_THEN "wfar" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `K:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")))) THEN
  ABBREV_TAC `hK = inv(sqrt K)` THEN
  SUBGOAL_THEN `&0 < hK /\ &0 < inv eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hK" THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the curvature bound short of the end of the cut *)
  FIRST_ASSUM(MP_TAC o SPEC `A1 - &2 / &5 * hK * inv eps` o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2 o GEN_REWRITE_RULE I [p2bt_cut]) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `&0 < hK * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kp0:real` (LABEL_TAC "kp")) THEN
  ABBREV_TAC `Kp = max (&1) Kp0` THEN
  SUBGOAL_THEN `&0 < Kp /\ Kp0 <= Kp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `delta = min (hK / &4) (inv(sqrt Kp) / &4)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= hK / &4 /\ delta <= inv(sqrt Kp) / &4`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN
    SUBGOAL_THEN `&0 < inv(sqrt Kp)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV) o
    GEN_REWRITE_RULE I [p2bt_lim] o check (fun th -> is_comb(concl th) &&
      (let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_lim"))) THEN
  (* the lifting of deep curves of length <= A1 + 1 *)
  FIRST_ASSUM(MP_TAC o SPECL [`delta:real`; `A1 + &1`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_length")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_lc_deep")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bt_cut eps C A (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 A1` THEN
    REWRITE_TAC[p2bt_cut] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&0 <= &4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL; REAL_LE_POW_2; REAL_POS] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `k0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lift")))) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `N1 + k0:num`] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `sig:real`; `y:real^3`; `q:A`] THEN
  INTRO_TAC "kn sg0 sg1 ys bl pos rk qb" THEN
  SUBGOAL_THEN `N1 <= (sub:num->num) k /\ k0 <= k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MONOTONE_BIGGER o REWRITE_RULE[p3_subseq] o check (fun th ->
      is_comb(concl th) && (let c,_ = strip_comb(concl th) in
        is_const c && fst(dest_const c) = "p3_subseq"))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bt_one eps C A ((sub:num->num) k)
      ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k))
      ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k))
      ((s1:num->real) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `(sub:num->num) k`);
    ALL_TAC] THEN
  (* scales *)
  SUBGOAL_THEN
   `&0 < mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
          (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((gamma:num->real->A) ((sub:num->num) k) sig)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
      `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
      `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
      `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
      `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
      `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`]
      P2BT_TUBE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[rfs_neck] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < inv(sqrt(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
           (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((gamma:num->real->A) ((sub:num->num) k) sig))) /\
    hK <= inv(sqrt(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
           (rfs_vmetric (V ((sub:num->num) k)) (&0)) (gamma ((sub:num->num) k) sig)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hK" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < inv(sqrt(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
           (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((gamma:num->real->A) ((sub:num->num) k) sig))) *
         inv eps /\
    hK * inv eps <= inv(sqrt(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
           (rfs_vmetric (V ((sub:num->num) k)) (&0)) (gamma ((sub:num->num) k) sig))) * inv eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
                    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the margins *)
  USE_THEN "far" (MP_TAC o SPECL [`(sub:num->num) k`; `sig:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the deep curve to q and its lift *)
  UNDISCH_TAC `(q:A) IN mfd_ball (rfs_vtop ((V:num->(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),
                 rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))
                 ((EN:num->real->real^3->A) ((sub:num->num) k) sig y)
                 (&3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
                    (rfs_vmetric (V ((sub:num->num) k)) (&0)) (EN ((sub:num->num) k) sig y))) * inv eps)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "reach" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `A1:real`; `sig:real`; `y:real^3`; `q:A`; `delta:real`; `Kp:real`;
     `A1 - &2 / &5 * hK * inv eps`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&17 / &10`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `p2bt_cut eps C A (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 A1` THEN
      REWRITE_TAC[p2bt_cut] THEN SIMP_TAC[];
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kp0:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "kp" (MP_TAC o SPECL [`(sub:num->num) k`; `s':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real->A` STRIP_ASSUME_TAC) THEN
  USE_THEN "lift" (MP_TAC o SPECL [`k:num`; `cc:real->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2bt_zbase] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS]]);;

let P2BTL_NECK_COVER = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
              ==> !K. &0 < K
                      ==> ?m N. !k P.
                            N <= k /\ P IN W k /\
                            &65 * C pow 2 <=
                            mfd_scalar (rfs_vatlas (V (sub k)) (&0)) (rfs_vmetric (V (sub k)) (&0))
                                       (phi k P) /\
                            mfd_scalar (rfs_vatlas (V (sub k)) (&0)) (rfs_vmetric (V (sub k)) (&0))
                                       (phi k P) <= K
                            ==> !q. q IN mfd_ball (rfs_vtop (V (sub k)) (&0),
                                                   rfs_vatlas (V (sub k)) (&0))
                                                  (rfs_vmetric (V (sub k)) (&0)) (phi k P)
                                       (&3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas (V (sub k)) (&0))
                                                    (rfs_vmetric (V (sub k)) (&0)) (phi k P))) *
                                        inv eps)
                                    ==> ?y'. y' IN W m /\ phi k y' = q`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wl")) o
    MATCH_MP P2BTL_WINDOW_LIFT) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wpos"))
    (INST_TYPE [`:A`,`:A`] P2BTL_WINDOW_POS) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "blev"))
    (INST_TYPE [`:A`,`:A`] P2BTL_BEYOND_LEVEL) THEN
  EXISTS_TAC `min e0 (min e2 e3)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx" THEN X_GEN_TAC `K:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e2 /\ eps <= e3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "wl" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * K`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `N:num` (LABEL_TAC "wlk"))) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `N:num`] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `P:B`] THEN INTRO_TAC "kn pw r65 rk" THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  USE_THEN "lctx" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bt_lctx]) THEN
  SUBGOAL_THEN `&0 < C pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bt_one eps C A ((sub:num->num) k)
      ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k))
      ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k))
      ((s1:num->real) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `(sub:num->num) k`);
    ALL_TAC] THEN
  (* phi k P lies in the cutset, on a window neck *)
  SUBGOAL_THEN
   `(phi:num->B->A) k P IN
    p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))
      ((s0:num->real) ((sub:num->num) k)) ((s1:num->real) ((sub:num->num) k)) A1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_lim (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                   (\n. p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1)
                   (p2bt_zbase eps C V gamma s0) sub (top:B topology) atlas g zl W phi Vl` THEN
    REWRITE_TAC[p2bt_lim] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `k:num` o el 8 o CONJUNCTS) THEN
    BETA_TAC THEN UNDISCH_TAC `(P:B) IN (W:num->B->bool) k` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "wpos" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `A1:real`; `(phi:num->B->A) k P`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sig:real` (X_CHOOSE_THEN `y:real^3`
    (DESTRUCT_TAC "sg0 sg1 ys we r99 r101 pos"))) THEN
  REMOVE_THEN "we" (ASSUME_TAC o SYM) THEN
  USE_THEN "blev" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `sig:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "wlk" (MP_TAC o SPECL [`k:num`; `sig:real`; `y:real^3`; `q:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The neck at one approximant index.  Given an approximant view V'         *)
(* with the strong eps-neck at phi y, the covering of its 3/5 h / eps ball  *)
(* by phi of a set Wm whose curvatures are uniformly close, a box X over    *)
(* the compact Kc of points with 9/10 R(y) <= R <= 11/10 R(y), persistence  *)
(* on (a,0] with a < -3/4 / R'(phi y), and the closeness on Kc below eta,   *)
(* the limit view has an evolving 2 eps-neck of length 1/2 at y.            *)
(* ------------------------------------------------------------------------- *)

let P2BTL_ENECK_K = prove
 (`?eps0. &0 < eps0 /\
     !eps. &0 < eps /\ eps <= eps0
       ==> ?m eta. &0 < eta /\
             !(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
              (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))
              (phi:B->A) psi Wk Wm X Kc a y Ry.
                p2c_regular_view V' /\ p2c_regular_view Vl /\
                hausdorff_space (rfs_vtop V' (&0)) /\
                smooth_manifold_atlas (rfs_vtop V' (&0)) (rfs_vatlas V' (&0)) /\
                riemannian_metric (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) /\
                mfd_diffeo (rfs_vtop Vl (&0)) (rfs_vatlas Vl (&0)) Wk
                           (rfs_vtop V' (&0)) (rfs_vatlas V' (&0)) (IMAGE phi Wk) phi psi /\
                y IN Wk /\ (?e. rfs_strong_neck V' eps (phi y) (&0) e) /\
                &1 <= mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y) /\
                &0 < Ry /\
                abs(mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y) - Ry)
                <= Ry / &100 /\
                (!q. q IN mfd_ball (rfs_vtop V' (&0),rfs_vatlas V' (&0)) (rfs_vmetric V' (&0))
                                   (phi y)
                            (&3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V' (&0))
                                                 (rfs_vmetric V' (&0)) (phi y))) * inv eps)
                     ==> ?y'. y' IN Wm /\ phi y' = q) /\
                (!z. z IN Wm
                     ==> abs(mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi z) -
                             mfd_scalar (rfs_vatlas Vl (&0)) (rfs_vmetric Vl (&0)) z)
                         <= Ry / &100) /\
                (!z. z IN Wm /\
                     &9 / &10 * Ry <= mfd_scalar (rfs_vatlas Vl (&0)) (rfs_vmetric Vl (&0)) z /\
                     mfd_scalar (rfs_vatlas Vl (&0)) (rfs_vmetric Vl (&0)) z <= &11 / &10 * Ry
                     ==> z IN Kc) /\
                Kc SUBSET X /\ X SUBSET Wk /\ open_in (rfs_vtop Vl (&0)) X /\
                rfs_persists Vl X a (&0) /\ rfs_persists V' (IMAGE phi X) a (&0) /\
                a < --(&3 / &4) / mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y) /\
                (!s z. a < s /\ s <= &0 /\ z IN Kc
                       ==> lck_dist2 m
                             (metric_local (rfs_vatlas Vl s) (chart_at (rfs_vatlas Vl s) z)
                                           (rfs_vmetric Vl s))
                             (rfs_pullback (rfs_vatlas V' s)
                                (phi o chart_inv (chart_at (rfs_vatlas Vl s) z))
                                (rfs_vmetric V' s))
                             (SND(chart_at (rfs_vatlas Vl s) z) z) < eta)
                ==> ?e. rfs_evolving_neck Vl (&2 * eps) y (&0) (&1 / &2) e`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inb"))
    (INST_TYPE [`:A`,`:A`] P2BTL_NECK_IN_BALL) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min e1 (min e2 (&1 / &100))` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= &1 / &100` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:A`,`:A`; `:B`,`:B`] (SPEC `eps:real` P2BTL_NECK_FIX_HALF)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`; `:B`,`:B`] (SPEC `delta:real` P2BTL_VIEW_CLOSE_BOX)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vcb"))) THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg delta`; `eta:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  INTRO_TAC "rv rl hs sm rm df yw (@e0. sn) q1 ry ryk cov rcl kcd kx xw xo pl pv at cl" THEN
  USE_THEN "df" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `&0 < mfd_scalar (rfs_vatlas (V':(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                  (rfs_vmetric V' (&0)) ((phi:B->A) y)`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the source neck: 19/10 eps, normalized length 3/4 *)
  SUBGOAL_THEN `rfs_evolving_neck (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&19 / &10 * eps) ((phi:B->A) y) (&0) (&3 / &4)
                  (e0:real^3->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BTL_EVNECK_MONO THEN MAP_EVERY EXISTS_TAC [`eps:real`; `&1`] THEN
    REWRITE_TAC[GSYM rfs_strong_neck] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&0),rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) eps
                  ((phi:B->A) y) (e0:real^3->A)`
  ASSUME_TAC THENL
   [USE_THEN "sn" (MP_TAC o REWRITE_RULE[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* its points are phi of points of Kc *)
  SUBGOAL_THEN
   `IMAGE (e0:real^3->A) (rfs_neck_dom (&19 / &10 * eps)) SUBSET
    mfd_ball (rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) (&0),rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) ((phi:B->A) y)
      (&3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y))) *
       inv eps)`
  ASSUME_TAC THENL [USE_THEN "inb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN IMAGE (e0:real^3->A) (rfs_neck_dom (&19 / &10 * eps))
        ==> ?y'. y' IN Kc /\ (phi:B->A) y' = q`
  (LABEL_TAC "sk") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "cov" (MP_TAC o SPEC `(e0:real^3->A) z`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN rfs_neck_dom (&19 / &10 * eps)` THEN
      UNDISCH_TAC
       `IMAGE (e0:real^3->A) (rfs_neck_dom (&19 / &10 * eps)) SUBSET
        mfd_ball (rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) (&0),rfs_vatlas V' (&0)) (rfs_vmetric V' (&0))
                 ((phi:B->A) y)
          (&3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y))) *
           inv eps)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y':B` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "kcd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&19 / &10 * eps`] APX_NECK_DOM_MONO) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^3) IN rfs_neck_dom (&19 / &10 * eps)` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "nh" (MP_TAC o SPECL
      [`rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) (&0)`;
       `rfs_vatlas (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) (&0)`;
       `rfs_vmetric (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) (&0)`;
       `eps:real`; `(phi:B->A) y`; `e0:real^3->A`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "rcl" (MP_TAC o C MATCH_MP (ASSUME `(y':B) IN Wm`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* phi y is in the neck, so y is in Kc and in X *)
  SUBGOAL_THEN `((phi:B->A) y) IN IMAGE (e0:real^3->A) (rfs_neck_dom (&19 / &10 * eps))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (rfs_vtop (V':(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                   rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) eps ((phi:B->A) y) (e0:real^3->A)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(SPEC `&19 / &10 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `((phi:B->A) y) IN IMAGE (e0:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN X` ASSUME_TAC THENL
   [USE_THEN "sk" (MP_TAC o C MATCH_MP (ASSUME
      `((phi:B->A) y) IN IMAGE (e0:real^3->A) (rfs_neck_dom (&19 / &10 * eps))`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y'':B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y'':B) IN Wk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y'':B) = y` SUBST_ALL_TAC THENL
     [MP_TAC(ASSUME `!x:B. x IN Wk ==> (psi:A->B) ((phi:B->A) x) = x`) THEN
      DISCH_THEN(fun th -> MP_TAC(MATCH_MP th (ASSUME `(y'':B) IN Wk`)) THEN
                           MP_TAC(MATCH_MP th (ASSUME `(y:B) IN Wk`))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (rfs_neck_dom (&19 / &10 * eps)) SUBSET IMAGE (phi:B->A) X /\
                IMAGE (psi:A->B) (IMAGE e0 (rfs_neck_dom (&19 / &10 * eps))) SUBSET Kc`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN USE_THEN "sk" (MP_TAC o SPEC `(e0:real^3->A) z`) THEN
    (ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `y':B` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y':B` THEN ASM SET_TAC[];
      SUBGOAL_THEN `(y':B) IN Wk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the time-0 diffeo on X *)
  SUBGOAL_THEN `mfd_diffeo (rfs_vtop Vl (&0)) (rfs_vatlas Vl (&0)) X
                  (rfs_vtop V' (&0)) (rfs_vatlas V' (&0)) (IMAGE (phi:B->A) X) phi psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`Wk:B->bool`; `IMAGE (phi:B->A) Wk`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the rescaled times *)
  SUBGOAL_THEN
   `!s. --(&3 / &4) < s /\ s <= &0
        ==> a < s / mfd_scalar (rfs_vatlas (V':(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                  (rfs_vmetric V' (&0)) ((phi:B->A) y) /\
            s / mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y) <= &0 /\
            --(&3 / &4) / mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y) <
            s / mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y)`
  (LABEL_TAC "tm") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `--(&3 / &4) / mfd_scalar (rfs_vatlas (V':(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                    (rfs_vmetric V' (&0)) ((phi:B->A) y) <
                  s / mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "fix" (MP_TAC o SPECL
    [`V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `(phi:B->A) y`; `&0`; `e0:real^3->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `&0`;
     `mfd_scalar (rfs_vatlas (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (&0)) (rfs_vmetric V' (&0)) ((phi:B->A) y)`;
     `psi:A->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2BN_RFS_VSCALAR; REAL_ADD_LID] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "tm" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `--(&3 / &4) < s /\ s <= &0`)) THEN
      SUBGOAL_THEN
       `smooth_manifold_atlas
          (rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                        (real->B->real^3^3))
             (s / mfd_scalar (rfs_vatlas (V':(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                    (rfs_vmetric V' (&0)) ((phi:B->A) y)))
          (rfs_vatlas Vl (s / mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0)) (phi y))) /\
        open_in (rfs_vtop Vl (s / mfd_scalar (rfs_vatlas V' (&0)) (rfs_vmetric V' (&0))
                                              (phi y))) X`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "pl" (MP_TAC o REWRITE_RULE[P2BN_PERSISTS_ALT]) THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "rl" (MP_TAC o SPEC `s / mfd_scalar (rfs_vatlas (V':(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                    (rfs_vmetric V' (&0)) ((phi:B->A) y)` o CONJUNCT1 o
                    REWRITE_RULE[p2c_regular_view]) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                          (real->B->real^3^3))
                          (s / mfd_scalar (rfs_vatlas (V':(real->A topology)#
                            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                            (rfs_vmetric V' (&0)) ((phi:B->A) y))`; `X:B->bool`]
                      OPEN_IN_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:B) IN X` THEN SET_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "vcb" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`X:B->bool`; `a:real`; `phi:B->A`] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `((phi:B->A) y) IN IMAGE (e0:real^3->A) (rfs_neck_dom (&19 / &10 * eps))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "tm" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `--(&3 / &4) < s /\ s <= &0`)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_evolving_neck (V':(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                    (&19 / &10 * eps) ((phi:B->A) y) (&0) (&3 / &4) (e0:real^3->A)` THEN
      REWRITE_TAC[P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR; REAL_SUB_LZERO] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s / mfd_scalar (rfs_vatlas (V':(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                    (rfs_vmetric V' (&0)) ((phi:B->A) y)` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `y1:B` THEN DISCH_TAC THEN USE_THEN "cl" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) ((phi:B->A) y) = y` SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:B. x IN Wk ==> (psi:A->B) ((phi:B->A) x) = x`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(psi:A->B) o (e0:real^3->A)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.  For y with R(y) >= 70 C^2: the covering index m       *)
(* (P2BTL_NECK_COVER with K = 2 R(y)) enlarged so that y is in W m; the     *)
(* compact Kc of points of the closure of W m with 9/10 R(y) <= R <=        *)
(* 11/10 R(y); a box over Kc (P2BTL_BOX_COMPACT with s1' = -4/5 / R(y)) and *)
(* its convergence from b = -79/100 / R(y); one large index k and           *)
(* P2BTL_ENECK_K.                                                            *)
(* ------------------------------------------------------------------------- *)

let P2BTL_TIME_ARITH = prove
 (`!Ry Rk. &0 < Ry /\ abs(Rk - Ry) <= Ry / &100
           ==> --(&79 / &100 * inv Ry) < --(&3 / &4) / Rk`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Rk /\ &99 / &100 * Ry <= Rk` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv Rk <= inv(&99 / &100 * Ry)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv Ry` MP_TAC THENL [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_MUL; real_div] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let P2BTL_KC_COMPACT = prove
 (`!top atlas (g:B->real^3^3) K lo hi.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K
     ==> compact_in top {z | z IN K /\ mfd_scalar atlas g z IN real_interval[lo,hi]}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `K:B->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE_GEN THEN
  EXISTS_TAC `euclideanreal` THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS; COMPACT_IN_IMP_CLOSED_IN] THEN
  REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL]);;

let P2BTL_ENECK_AT = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl y.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl /\
              y IN topspace top /\ &70 * C pow 2 <= mfd_scalar atlas g y
              ==> ?e. rfs_evolving_neck Vl (&2 * eps) y (&0) (&1 / &2) e`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cov")) o
    MATCH_MP P2BTL_NECK_COVER) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ek"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_ENECK_K) THEN
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "box"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_BOX_COMPACT) THEN
  EXISTS_TAC `min (min e0 e1) (&1 / &4)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx yt r70" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  USE_THEN "lim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bt_lim]) THEN
  SUBGOAL_THEN `&1 <= C pow 2 /\ &0 < mfd_scalar atlas (g:B->real^3^3) y /\
                &0 < inv(mfd_scalar atlas (g:B->real^3^3) y)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= C pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) y` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  (* the constants of P2BTL_ENECK_K *)
  USE_THEN "ek" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mk:num` (X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ekp")))) THEN
  (* the covering index for K = 2 R(y) *)
  USE_THEN "cov" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * mfd_scalar atlas (g:B->real^3^3) y`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mc:num` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "cv"))) THEN
  (* y lies in some W j; the index mm *)
  SUBGOAL_THEN `?j. (y:B) IN (W:num->B->bool) j` (X_CHOOSE_TAC `j:num`) THENL
   [UNDISCH_TAC `(y:B) IN topspace top` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "UNIONS")) (concl th))) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. open_in top ((W:num->B->bool) k) /\ top closure_of W k SUBSET W (SUC k)`
  (LABEL_TAC "wmon") THENL
   [FIRST_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `!k:num. open_in (top:B topology) ((W:num->B->bool) k) /\ P k`)
          (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "closure_of")) (concl th))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `mm = MAX mc j` THEN
  SUBGOAL_THEN `(W:num->B->bool) mc SUBSET W mm /\ W j SUBSET W mm` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BTL_W_MONO THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "mm" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of (W:num->B->bool) mm) /\
                (W:num->B->bool) mm SUBSET top closure_of W mm /\
                (y:B) IN W mm /\ (y:B) IN top closure_of W mm`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in top (top closure_of (W:num->B->bool) mm) /\
                  (W:num->B->bool) mm SUBSET top closure_of W mm`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `mm:num` o check (fun th ->
          can (term_match [] `!k:num. open_in (top:B topology) ((W:num->B->bool) k) /\ P k`)
              (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
        SIMP_TAC[];
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
        USE_THEN "wmon" (ACCEPT_TAC o CONJUNCT1 o SPEC `mm:num`)];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(W:num->B->bool) j SUBSET W mm` THEN
    UNDISCH_TAC `(W:num->B->bool) mm SUBSET top closure_of W mm` THEN
    UNDISCH_TAC `(y:B) IN (W:num->B->bool) j` THEN SET_TAC[];
    ALL_TAC] THEN
  (* uniform closeness of the curvature on the closure of W mm *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                        ((s1:num->real) n) A1`;
                 `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
                 `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `top closure_of (W:num->B->bool) mm`;
                 `mfd_scalar atlas (g:B->real^3^3) y / &100`] P2BTL_R_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` (LABEL_TAC "ru")) THEN
  (* the compact Kc *)
  ABBREV_TAC `Kc = {z | z IN top closure_of (W:num->B->bool) mm /\
                        mfd_scalar atlas (g:B->real^3^3) z IN
                        real_interval[&9 / &10 * mfd_scalar atlas g y,
                                      &11 / &10 * mfd_scalar atlas g y]}` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC P2BTL_KC_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the box over Kc *)
  USE_THEN "box" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `Kc:B->bool`; `--(&4 / &5 * inv(mfd_scalar atlas (g:B->real^3^3) y))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:B) IN Kc` THEN SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:B` THEN EXPAND_TAC "Kc" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `inv(&11 / &10 * mfd_scalar atlas (g:B->real^3^3) y) <= inv(mfd_scalar atlas g z)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:B->bool` (X_CHOOSE_THEN `a:real`
    (DESTRUCT_TAC "xo xc kx as an rx (@N0. bx)"))) THEN
  (* the box clause of the limit *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`X:B->bool`; `a:real`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_vflow")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`K1 * --inv a`; `N0:num`] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "bx" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (X:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vf") (LABEL_TAC "bconv")) THEN
  SUBGOAL_THEN `a < --(&79 / &100 * inv(mfd_scalar atlas (g:B->real^3^3) y))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "bconv" (MP_TAC o SPECL
    [`Kc:B->bool`; `mk:num`; `eta:real`;
     `--(&79 / &100 * inv(mfd_scalar atlas (g:B->real^3^3) y))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:num` (LABEL_TAC "kc")) THEN
  (* one large index *)
  ABBREV_TAC `k = (N1:num) + k2 + N0 + k3 + mm` THEN
  SUBGOAL_THEN `(N1:num) <= k /\ (k2:num) <= k /\ (N0:num) <= k /\ (k3:num) <= k /\ (mm:num) <= k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ru" (MP_TAC o C MATCH_MP (ASSUME `(k2:num) <= k`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ruk")) THEN
  USE_THEN "bx" (MP_TAC o C MATCH_MP (ASSUME `(N0:num) <= k`)) THEN
  DISCH_THEN(DESTRUCT_TAC "clw pk rmk") THEN
  USE_THEN "diffs" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  SUBGOAL_THEN `(y:B) IN (W:num->B->bool) k` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN top closure_of (W:num->B->bool) mm` THEN
    UNDISCH_TAC `top closure_of (W:num->B->bool) mm SUBSET W k` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "ruk" (ASSUME_TAC o C MATCH_MP (ASSUME `(y:B) IN top closure_of (W:num->B->bool) mm`)) THEN
  (* the covering at k *)
  USE_THEN "cv" (MP_TAC o SPECL [`k:num`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "cvk")] THEN
  (* the hypotheses of P2BTL_ENECK_K at k *)
  SUBGOAL_THEN `hausdorff_space (rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))`
  ASSUME_TAC THENL
   [USE_THEN "approx" (MP_TAC o SPEC `(sub:num->num) k` o REWRITE_RULE[p2bt_approx]) THEN
    REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. rfs_strong_neck ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
                  eps ((phi:num->B->A) k y) (&0) e`
  ASSUME_TAC THENL
   [USE_THEN "necks" MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
                  (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((phi:num->B->A) k y)`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN mfd_ball (rfs_vtop ((V:num->(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),
                 rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))
                 ((phi:num->B->A) k y)
                 (&3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
                    (rfs_vmetric (V ((sub:num->num) k)) (&0)) (phi k y))) * inv eps)
        ==> ?y'. y' IN (W:num->B->bool) mm /\ phi k y' = q`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(fun th -> USE_THEN "cvk" (MP_TAC o C MATCH_MP th)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(W:num->B->bool) mc SUBSET W mm` THEN
    UNDISCH_TAC `(y':B) IN (W:num->B->bool) mc` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN (W:num->B->bool) mm
        ==> abs(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
                  (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((phi:num->B->A) k z) -
                mfd_scalar atlas (g:B->real^3^3) z) <= mfd_scalar atlas g y / &100`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN USE_THEN "ruk" MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:B) IN (W:num->B->bool) mm` THEN
    UNDISCH_TAC `(W:num->B->bool) mm SUBSET top closure_of W mm` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN (W:num->B->bool) mm /\
        &9 / &10 * mfd_scalar atlas (g:B->real^3^3) y <= mfd_scalar atlas g z /\
        mfd_scalar atlas g z <= &11 / &10 * mfd_scalar atlas g y
        ==> z IN Kc`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:B` THEN STRIP_TAC THEN EXPAND_TAC "Kc" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:B) IN (W:num->B->bool) mm` THEN
    UNDISCH_TAC `(W:num->B->bool) mm SUBSET top closure_of W mm` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET (W:num->B->bool) k` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (X:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_persists (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                     (real->B->real^3^3)) X
      (--(&79 / &100 * inv(mfd_scalar atlas (g:B->real^3^3) y))) (&0) /\
    rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) ((sub:num->num) k)) (IMAGE ((phi:num->B->A) k) X)
      (--(&79 / &100 * inv(mfd_scalar atlas g y))) (&0)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "vf" (MP_TAC o CONJUNCT1 o REWRITE_RULE[p2c_vflow]) THEN
    UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) ((sub:num->num) k)) (IMAGE ((phi:num->B->A) k) X) a (&0)` THEN
    REWRITE_TAC[P2BN_PERSISTS_ALT] THEN
    UNDISCH_TAC `a < --(&79 / &100 * inv(mfd_scalar atlas (g:B->real^3^3) y))` THEN
    MESON_TAC[REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--(&79 / &100 * inv(mfd_scalar atlas (g:B->real^3^3) y)) <
    --(&3 / &4) / mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
                  (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((phi:num->B->A) k y)`
  ASSUME_TAC THENL [MATCH_MP_TAC P2BTL_TIME_ARITH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s z. --(&79 / &100 * inv(mfd_scalar atlas (g:B->real^3^3) y)) < s /\ s <= &0 /\ z IN Kc
          ==> lck_dist2 mk
                (metric_local (rfs_vatlas (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                              (real->B->real^3^3)) s)
                   (chart_at (rfs_vatlas Vl s) z) (rfs_vmetric Vl s))
                (rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s)
                   ((phi:num->B->A) k o chart_inv (chart_at (rfs_vatlas Vl s) z))
                   (rfs_vmetric (V ((sub:num->num) k)) s))
                (SND(chart_at (rfs_vatlas Vl s) z) z) < eta`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "kc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ekp" (MP_TAC o SPECL
    [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
        ((sub:num->num) k)`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `(phi:num->B->A) k`; `psi:A->B`; `(W:num->B->bool) k`; `(W:num->B->bool) mm`;
     `X:B->bool`; `Kc:B->bool`; `--(&79 / &100 * inv(mfd_scalar atlas (g:B->real^3^3) y))`;
     `y:B`; `mfd_scalar atlas (g:B->real^3^3) y`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

let P2BTL_LIM_ENECK = prove
 (`!(u:A->bool) (w:B->bool). P2BT_LIM_ENECK_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BT_LIM_ENECK_STATEMENT] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "at")) o
    MATCH_MP (INST_TYPE [`:B`,`:B`] P2BTL_ENECK_AT)) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `&70 * C pow 2` THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  USE_THEN "at" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

