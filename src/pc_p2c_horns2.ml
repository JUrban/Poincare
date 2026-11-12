(* ========================================================================= *)
(* Unit pc_p2c_horns2 (Part 2C): MT Thm 11.31 (strong delta-necks deep in a  *)
(* 2 eps-horn), the route P2HN_THM_11_31_ROUTE of                            *)
(* P2C_THM_11_31_ROUTE_STATEMENT.  The sides of neck spheres and the two     *)
(* ends are in the unit pc_p2c_nsides, loaded below.                         *)
(* ========================================================================= *)

needs "src/pc_p2c_horns.ml";;
needs "src/pc_p2c_nsides.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_p2c_lrestrict.ml";;
needs "src/pc_lck_swap.ml";;
needs "src/pc_canon_diam.ml";;
needs "src/pc_vshi.ml";;
needs "src/pc_p2c_bugq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Flow-limit closeness read in the                                         *)
(* coordinates of a parametrization of the limit (naturality of the C^k     *)
(* distance), the input for transferring necks from the approximants to the *)
(* limit.                                                                    *)
(* ========================================================================= *)

let P2HN_RFS_PULLBACK_CONG = prove
 (`!atlas (e1:real^N->A) e2 (g:A->real^N^N) N y.
     open N /\ y IN N /\ (!z. z IN N ==> e1 z = e2 z)
     ==> rfs_pullback atlas e1 g y = rfs_pullback atlas e2 g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback; o_THM] THEN
  SUBGOAL_THEN `(e1:real^N->A) y = e2 y` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) y)) o e1)
                       (at y) =
    frechet_derivative (SND(chart_at atlas (e2 y)) o e2) (at y)`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN ABS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) y)) o
                (e1:real^N->A)`;
    EXISTS_TAC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) y)) o
                (e2:real^N->A)`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[o_THM] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[DIST_SYM]);;

let P2HN_MPULLBACK_CMUL = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) c y.
     mpullback h (\z. c %% G z) y = c %% mpullback h G y`,
  REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

(* Naturality: the C^k distance between the pullbacks of g0 and of the      *)
(* rescaled pullback of gA (through phi) along a parametrization p of the   *)
(* limit equals the distance read in the preferred chart at p v, the form   *)
(* of the closeness clause of p3_flow_limit.                                 *)

let P2HN_FLOW_CLOSE_PARAM = prove
 (`!top atlas (g0:B->real^3^3) (topA:A topology) atlasA gA W (phi:B->A) psi s p Q k v.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topA atlasA /\
     riemannian_metric atlas g0 /\ riemannian_metric atlasA gA /\
     mfd_diffeo top atlas W topA atlasA (IMAGE phi W) phi psi /\
     mfd_param top atlas s p /\ IMAGE p s SUBSET W /\ v IN s /\ &0 < Q
     ==> lck_dist2 k (rfs_pullback atlas p g0)
                     (\z. Q %% rfs_pullback atlasA (phi o p) gA z) v =
         lck_dist2 k (metric_local atlas (chart_at atlas (p v)) g0)
                     (\z. Q %% rfs_pullback atlasA
                                 (phi o chart_inv (chart_at atlas (p v))) gA z)
                     (SND(chart_at atlas (p v)) (p v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3->B) v IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `s:real^3->bool`; `p:real^3->B`; `s:real^3->bool`] MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(p:real^3->B) v`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) v)`,
           `c:(B->bool)#(B->real^3)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:B->bool`; `ch:B->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `s:real^3->bool`;
                 `p:real^3->B`; `V:B->bool`; `ch:B->real^3`] APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p':B->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `N = {z | z IN s /\ (p:real^3->B) z IN V}` THEN
  ABBREV_TAC `N' = IMAGE (ch:B->real^3) (V INTER IMAGE (p:real^3->B) s)` THEN
  SUBGOAL_THEN `open (N:real^3->bool) /\ open (N':real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `N SUBSET (s:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN SET_TAC[]; ALL_TAC] THEN
  (* the chart inverse composed with phi is a parametrization of A on N' *)
  SUBGOAL_THEN `N' SUBSET IMAGE (ch:B->real^3) V /\
                IMAGE (chart_inv (V:B->bool,ch:B->real^3)) N' SUBSET (W:B->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `V:B->bool`; `ch:B->real^3`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "N'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `q:B` THEN STRIP_TAC THEN
      SUBGOAL_THEN `chart_inv (V:B->bool,ch:B->real^3) (ch q) = q` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(q:B) IN IMAGE (p:real^3->B) s` THEN
      UNDISCH_TAC `IMAGE (p:real^3->B) s SUBSET W` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param topA atlasA N' ((phi:B->A) o chart_inv (V:B->bool,ch:B->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `W:B->bool`; `IMAGE (phi:B->A) W`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (ch:B->real^3) V` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* both pullbacks along p are pullbacks along the chart representative *)
  SUBGOAL_THEN
   `!z. z IN N
        ==> rfs_pullback atlas (p:real^3->B) g0 z =
            mpullback ((ch:B->real^3) o p) (metric_local atlas (V,ch) g0) z /\
            (\z. Q %% rfs_pullback atlasA ((phi:B->A) o p) (gA:A->real^3^3) z) z =
            mpullback (ch o p)
              (\w. Q %% rfs_pullback atlasA (phi o chart_inv (V:B->bool,ch:B->real^3)) gA w) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN s /\ (p:real^3->B) z IN V` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN N` THEN EXPAND_TAC "N" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC APX_RFS_PULLBACK_CHART THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `s:real^3->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[P2HN_MPULLBACK_CMUL] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                   `gA:A->real^3^3`; `N':real^3->bool`;
                   `(phi:B->A) o chart_inv (V:B->bool,ch:B->real^3)`; `N:real^3->bool`;
                   `(ch:B->real^3) o (p:real^3->B)`; `(p':B->real^3) o chart_inv (V:B->bool,ch:B->real^3)`;
                   `z:real^3`] APX_RFS_PULLBACK_PRECOMP) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC P2HN_RFS_PULLBACK_CONG THEN EXISTS_TAC `N:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `V:B->bool`; `ch:B->real^3`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `(w:real^3) IN N` THEN EXPAND_TAC "N" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lck_dist2 k (mpullback ((ch:B->real^3) o (p:real^3->B)) (metric_local atlas (V,ch) g0))
                (mpullback (ch o p)
                   (\w. Q %% rfs_pullback atlasA ((phi:B->A) o chart_inv (V:B->bool,ch:B->real^3))
                                          (gA:A->real^3^3) w)) v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `N:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((ch:B->real^3) o (p:real^3->B)) v = ch(p v)` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `ch((p:real^3->B) v) = ((ch:B->real^3) o p) v` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`N':real^3->bool`; `N:real^3->bool`;
                        `(p':B->real^3) o chart_inv (V:B->bool,ch:B->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (ch:B->real^3) V` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) g0` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `(V:B->bool,ch:B->real^3)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `topA:A topology` THEN
    ASM_REWRITE_TAC[]]);;

(* The chain of C^k estimates: A close to G0 (base G0), B close to A (base   *)
(* B) give B close to A (base A, LCK_CK_BASE_REV) and B close to G0 (base   *)
(* G0, LRG_CK_BASE_CHANGE and the triangle inequality).                      *)

let P2HN_CLOSE_CHAIN = prove
 (`!k. ?M. &0 <= M /\
     !s (G0:real^3->real^3^3) A B y d th.
       metric_field s G0 /\ metric_field s A /\ metric_field s B /\ y IN s /\
       lck_dist2 k G0 A y <= d /\ d <= &1 / &4 /\
       lck_dist2 k B A y <= th /\ th <= &1 / &4
       ==> lck_dist2 k A B y <= M * th /\
           sqrt(lck_dist2 k G0 B y) <= sqrt d + sqrt(M * th)`,
  GEN_TAC THEN
  X_CHOOSE_THEN `M1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rev"))
    (INST_TYPE [`:3`,`:N`] (SPEC `k:num` LCK_CK_BASE_REV)) THEN
  X_CHOOSE_THEN `M2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "chg"))
    (SPEC `k:num` LRG_CK_BASE_CHANGE) THEN
  EXISTS_TAC `M1 * (M2 + &1)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= th /\ &0 <= d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `lck_dist2 k (B:real^3->real^3^3) A y`;
      EXISTS_TAC `lck_dist2 k (G0:real^3->real^3^3) A y`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k (A:real^3->real^3^3) B y <= M1 * th` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M1 * lck_dist2 k (B:real^3->real^3^3) (\z. B z + B z - A z) y` THEN
    CONJ_TAC THENL
     [USE_THEN "rev" (MATCH_MP_TAC o SPECL [`s:real^3->bool`; `B:real^3->real^3^3`;
        `A:real^3->real^3^3`; `B:real^3->real^3^3`; `y:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`k:num`; `s:real^3->bool`; `B:real^3->real^3^3`; `A:real^3->real^3^3`;
                     `y:real^3`] LCK_DIST2_REFLECT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M1 * th /\ &0 <= M1 * M2 * th` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]); ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `lck_dist2 k (A:real^3->real^3^3) B y <= M1 * th` THEN
    UNDISCH_TAC `&0 <= M1 * M2 * th` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 k (G0:real^3->real^3^3) A y) +
              sqrt(lck_dist2 k G0 (\z. G0 z + B z - A z) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_TRIANGLE THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M2 * lck_dist2 k (A:real^3->real^3^3) B y` THEN
  CONJ_TAC THENL
   [USE_THEN "chg" (MATCH_MP_TAC o SPECL [`s:real^3->bool`; `G0:real^3->real^3^3`;
      `A:real^3->real^3^3`; `B:real^3->real^3^3`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M2 * M1 * th` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= M1 * th` THEN REAL_ARITH_TAC);;

(* Arithmetic of the transferred neck bound.                                *)

let P2HN_SQRT_LE_IMP = prove
 (`!x b. &0 <= x /\ sqrt x <= b ==> x <= b pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = sqrt x pow 2` SUBST1_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]);;

let P2HN_NECK_ARITH = prove
 (`!eps eps' d a.
     &0 <= d /\ d < eps pow 2 /\ &0 < eps /\ eps < eps' /\ eps' <= &1 /\ &0 <= a /\
     a * (&1 + sqrt(&3)) <= (eps' - eps) / &4
     ==> (&1 + a) * (sqrt d + (eps' - eps) / &4) + a * sqrt(&3) < eps'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt d < eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt d` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `q = (eps' - eps) / &4` THEN
  SUBGOAL_THEN `a * sqrt d <= a * eps /\ a * (eps + q) <= a * &1 /\ &0 < q`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps + &2 * q < eps'` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `a * (&1 + sqrt(&3)) <= q` THEN
  UNDISCH_TAC `a * sqrt d <= a * eps` THEN UNDISCH_TAC `a * (eps + q) <= a * &1` THEN
  UNDISCH_TAC `sqrt d < eps` THEN UNDISCH_TAC `eps + &2 * q < eps'` THEN
  REAL_ARITH_TAC);;

(* The instance step of the neck transfer, with the constants as             *)
(* hypotheses.                                                               *)

let P2HN_NECK_TO_LIMIT_INST = prove
 (`!eps eps' c1 M K0 K1 a eta th
    top atlas (g0:B->real^3^3) (topA:A topology) atlasA gA W phi psi Q x e.
     &0 < eps /\ eps < eps' /\ eps' <= &1 / &4 /\ &0 < c1 /\ &0 <= M /\
     (!s (G0:real^3->real^3^3) A B y d th.
        metric_field s G0 /\ metric_field s A /\ metric_field s B /\ y IN s /\
        lck_dist2 (rfs_kreg eps) G0 A y <= d /\ d <= &1 / &4 /\
        lck_dist2 (rfs_kreg eps) B A y <= th /\ th <= &1 / &4
        ==> lck_dist2 (rfs_kreg eps) A B y <= M * th /\
            sqrt(lck_dist2 (rfs_kreg eps) G0 B y) <= sqrt d + sqrt(M * th)) /\
     (!y:real^3. ~(y = vec 0) ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2) /\
     (!s (G0:real^3->real^3^3) G y.
        metric_field s G0 /\ metric_field s G /\ y IN s /\
        lrm_deriv_norm2 0 G0 y <= K0 pow 2 /\ lck_dist2 2 G0 G y <= &1 / &4
        ==> lrm_deriv_norm2 0 G y <= K1) /\
     (!s (G0:real^3->real^3^3) G y.
        metric_field s G0 /\ metric_field s G /\ y IN s /\
        lrm_deriv_norm2 0 G0 y <= (abs K1 + &1) pow 2 /\ lck_dist2 2 G0 G y < eta pow 2
        ==> abs(lscalar G y - lscalar G0 y) <= a) /\
     &0 < a /\ a <= &1 / &2 /\ a * (&1 + sqrt(&3)) <= (eps' - eps) / &4 /\ &0 <= th /\
     (&1 + inv c1) pow (rfs_kreg eps) * th <= &1 / &4 /\
     M * ((&1 + inv c1) pow (rfs_kreg eps) * th) < eta pow 2 /\
     M * ((&1 + inv c1) pow (rfs_kreg eps) * th) <= ((eps' - eps) / &4) pow 2 /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     riemannian_metric atlasA gA /\
     mfd_diffeo top atlas W topA atlasA (IMAGE phi W) phi psi /\
     rfs_neck (topA,atlasA) gA eps x e /\
     IMAGE e (rfs_neck_dom eps) SUBSET IMAGE phi W /\
     &0 < Q /\ c1 * Q <= mfd_scalar atlasA gA x /\
     (!y. y IN IMAGE (psi o e) (rfs_neck_dom eps)
          ==> lck_dist2 (rfs_kreg eps)
                (metric_local atlas (chart_at atlas y) g0)
                (\z. Q %% rfs_pullback atlasA (phi o chart_inv (chart_at atlas y)) gA z)
                (SND(chart_at atlas y) y) <= th)
     ==> rfs_neck (top,atlas) g0 eps' (psi x) (psi o e)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN ABBREV_TAC `D = rfs_neck_dom eps` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `2 <= k /\ rfs_kreg eps' <= k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_KREG_TWO; MATCH_MP_TAC APX_KREG_MONO] THEN
    UNDISCH_TAC `&0 < eps` THEN UNDISCH_TAC `eps < eps'` THEN
    UNDISCH_TAC `eps' <= &1 / &4` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_close_on; ASSUME `rfs_kreg eps = k`;
                                    ASSUME `rfs_neck_dom eps = D`] o
              GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
    not (is_imp (concl th)) && not (is_forall (concl th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)))))) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ABBREV_TAC `RA = mfd_scalar atlasA (gA:A->real^3^3) x` THEN
  ABBREV_TAC `p = (psi:A->B) o (e:real^3->A)` THEN
  ABBREV_TAC `HB = rfs_pullback atlas (p:real^3->B) (g0:B->real^3^3)` THEN
  ABBREV_TAC `HA = rfs_pullback atlasA (e:real^3->A) (gA:A->real^3^3)` THEN
  ABBREV_TAC `c = RA / Q` THEN
  (* basic facts *)
  SUBGOAL_THEN `open (D:real^3->bool) /\ D SUBSET ((:real^3) DELETE vec 0) /\
                (y0:real^3) IN D /\ ~(y0 = vec 0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[APX_NECK_DOM_OPEN; P2BL_NECK_DOM_NZ] THEN
    CONJ_TAC THENL [MATCH_MP_TAC P2BN_SPHERE_IN_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c1 <= c /\ &0 < c /\ c * Q = RA` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_DIV_RMUL;
                                     REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  SUBGOAL_THEN `mfd_param top atlas D (p:real^3->B) /\ IMAGE p D SUBSET (W:B->bool) /\
                (!z. z IN D ==> (phi:B->A) (p z) = (e:real^3->A) z)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                            `IMAGE (phi:B->A) W`; `W:B->bool`; `phi:B->A`] THEN
      ASM_SIMP_TAC[MFD_DIFFEO_SYM];
      REWRITE_TAC[IMAGE_o] THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) D SUBSET IMAGE (phi:B->A) W` THEN
      UNDISCH_TAC `IMAGE (psi:A->B) (IMAGE (phi:B->A) W) SUBSET W` THEN SET_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) D SUBSET IMAGE (phi:B->A) W` THEN
      UNDISCH_TAC `(z:real^3) IN D` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* metric fields on D *)
  SUBGOAL_THEN
   `metric_field D (cylinder_flow (&0)) /\ metric_field D (HB:real^3->real^3^3) /\
    metric_field D (HA:real^3->real^3^3) /\
    metric_field D (\z. RA %% (HA:real^3->real^3^3) z) /\
    metric_field D (\z. c %% (HB:real^3->real^3^3) z) /\
    metric_field D (\z. Q %% (HA:real^3->real^3^3) z)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field D (HB:real^3->real^3^3) /\ metric_field D (HA:real^3->real^3^3)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "HB" THEN EXPAND_TAC "HA" THEN CONJ_TAC THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THENL
       [EXISTS_TAC `top:B topology`; EXISTS_TAC `topA:A topology`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RFB_METRIC_FIELD_CMUL; ETA_AX] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  (* closeness in neck coordinates, scaled *)
  SUBGOAL_THEN
   `!y. y IN D
        ==> lck_dist2 k (\z. c %% (HB:real^3->real^3^3) z) (\z. RA %% (HA:real^3->real^3^3) z) y
            <= (&1 + inv c1) pow k * th`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `lck_dist2 k (HB:real^3->real^3^3) (\z. Q %% (HA:real^3->real^3^3) z) y <= th`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                     `topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                     `gA:A->real^3^3`; `W:B->bool`; `phi:B->A`; `psi:A->B`; `D:real^3->bool`;
                     `p:real^3->B`; `Q:real`; `k:num`; `y:real^3`] P2HN_FLOW_CLOSE_PARAM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `lck_dist2 k (rfs_pullback atlas (p:real^3->B) (g0:B->real^3^3))
          (\z. Q %% rfs_pullback atlasA ((phi:B->A) o p) (gA:A->real^3^3) z) y =
        lck_dist2 k HB (\z. Q %% (HA:real^3->real^3^3) z) y`
      SUBST1_TAC THENL
       [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `D:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        EXPAND_TAC "HB" THEN EXPAND_TAC "HA" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC P2HN_RFS_PULLBACK_CONG THEN EXISTS_TAC `D:real^3->bool` THEN
        ASM_SIMP_TAC[o_THM];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. RA %% (HA:real^3->real^3^3) z) = (\z. c %% (\w. Q %% HA w) z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv c) pow k *
                lck_dist2 k (HB:real^3->real^3^3) (\z. Q %% (HA:real^3->real^3^3) z) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2B9S_LCK_SCALE_LE THEN EXISTS_TAC `D:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `D:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `th1 = (&1 + inv c1) pow k * th` THEN
  ABBREV_TAC `q = (eps' - eps) / &4` THEN
  SUBGOAL_THEN `&0 <= d /\ d <= &1 / &4 /\ &0 < q` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) (\z. RA %% (HA:real^3->real^3^3) z) y0` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d:real`)) (concl th))) THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps pow 2` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &4) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the chain of estimates on D *)
  SUBGOAL_THEN
   `!y. y IN D
        ==> lck_dist2 k (\z. RA %% (HA:real^3->real^3^3) z) (\z. c %% (HB:real^3->real^3^3) z) y
            <= M * th1 /\
            sqrt(lck_dist2 k (cylinder_flow (&0)) (\z. c %% HB z) y) <= sqrt d + q`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`D:real^3->bool`; `cylinder_flow (&0)`; `\z. RA %% (HA:real^3->real^3^3) z`;
       `\z. c %% (HB:real^3->real^3^3) z`; `y:real^3`; `d:real`; `th1:real`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "sqrt" with Failure _ -> false))
            (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "th1" THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt d + sqrt(M * th1)` THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    EXPAND_TAC "th1" THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the scalar curvatures at the centre *)
  SUBGOAL_THEN `lscalar (\z. RA %% (HA:real^3->real^3^3) z) y0 = &1 /\
                mfd_scalar atlas (g0:B->real^3^3) (psi(x:A)) =
                c * lscalar (\z. c %% (HB:real^3->real^3^3) z) y0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `lscalar (\z. RA %% (HA:real^3->real^3^3) z) y0 = lscalar HA y0 / RA /\
      lscalar (\z. c %% (HB:real^3->real^3^3) z) y0 = lscalar HB y0 / c`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC LSCALAR_SCALE THEN EXISTS_TAC `D:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                     `gA:A->real^3^3`; `D:real^3->bool`; `e:real^3->A`; `y0:real^3`]
        (REWRITE_RULE[APX_PULLBACK_SCALAR_STATEMENT] (ISPEC `(:A)` APX_PULLBACK_SCALAR))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `x:A = e(y0:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g0:B->real^3^3`; `D:real^3->bool`; `p:real^3->B`; `y0:real^3`]
        (REWRITE_RULE[APX_PULLBACK_SCALAR_STATEMENT] (ISPEC `(:B)` APX_PULLBACK_SCALAR))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p:real^3->B) y0 = psi((e:real^3->A) y0)` SUBST1_TAC THENL
       [EXPAND_TAC "p" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  ABBREV_TAC `lam = lscalar (\z. c %% (HB:real^3->real^3^3) z) y0` THEN
  SUBGOAL_THEN `abs(lam - &1) <= a` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term ((=) `lscalar (\z. RA %% (HA:real^3->real^3^3) z) y0`)) (concl th) &&
      is_eq (concl th))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a:real`)) (concl th) &&
      can (find_term ((=) `eta:real`)) (concl th))) THEN
    EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `K1:real`)) (concl th) &&
          not (can (find_term ((=) `a:real`)) (concl th)))) THEN
        EXISTS_TAC `D:real^3->bool` THEN EXISTS_TAC `cylinder_flow (&0)` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) (\z. RA %% (HA:real^3->real^3^3) z) y0` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `D:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `d:real`)) (concl th) &&
            not (can (find_term ((=) `th1:real`)) (concl th)))) THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[REAL_POW_2] THEN MP_TAC(SPEC `abs K1` REAL_LE_SQUARE) THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `lck_dist2 k (\z. RA %% (HA:real^3->real^3^3) z) (\z. c %% HB z) y0` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `M * th1` THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[]; EXPAND_TAC "th1" THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  (* the target neck *)
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < eps' /\ rfs_neck_dom eps' SUBSET D /\ open(rfs_neck_dom eps')`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[APX_NECK_DOM_OPEN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "p" THEN ASM_REWRITE_TAC[o_THM];
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `((&1 + a) * (sqrt d + q) + a * sqrt(&3)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_POS; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "q" THEN MATCH_MP_TAC P2HN_NECK_ARITH THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. (c * lam) %% (HB:real^3->real^3^3) y) =
                (\z. lam %% (\w. c %% (HB:real^3->real^3^3) w) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC P2HN_SQRT_LE_IMP THEN CONJ_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `D:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam * sqrt(lck_dist2 (rfs_kreg eps') (cylinder_flow (&0))
                                   (\w. c %% (HB:real^3->real^3^3) w) y) +
              abs(lam - &1) * sqrt(&(dimindex(:3)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_RESCALE THEN EXISTS_TAC `D:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  ABBREV_TAC `S = sqrt(lck_dist2 (rfs_kreg eps') (cylinder_flow (&0))
                                 (\w. c %% (HB:real^3->real^3^3) w) y)` THEN
  SUBGOAL_THEN `&0 <= S /\ S <= sqrt d + q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 k (cylinder_flow (&0)) (\w. c %% (HB:real^3->real^3^3) w) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN
      MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `D:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt d + q /\ &0 <= sqrt(&3)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;


(* Transfer of a slice eps-neck of an approximant to an eps'-neck of the     *)
(* limit (eps < eps'), uniform: the limit-side closeness th of the          *)
(* rescaled pullback depends only on eps, eps' and a lower bound c1 of the  *)
(* scale ratio R(x) / Q.                                                     *)

let P2HN_NECK_TO_LIMIT = prove
 (`!eps eps' c1.
     &0 < eps /\ eps < eps' /\ eps' <= &1 / &4 /\ &0 < c1
     ==> ?th. &0 < th /\
           !top atlas (g0:B->real^3^3) (topA:A topology) atlasA gA W phi psi Q x e.
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
              riemannian_metric atlasA gA /\
              mfd_diffeo top atlas W topA atlasA (IMAGE phi W) phi psi /\
              rfs_neck (topA,atlasA) gA eps x e /\
              IMAGE e (rfs_neck_dom eps) SUBSET IMAGE phi W /\
              &0 < Q /\ c1 * Q <= mfd_scalar atlasA gA x /\
              (!y. y IN IMAGE (psi o e) (rfs_neck_dom eps)
                   ==> lck_dist2 (rfs_kreg eps)
                         (metric_local atlas (chart_at atlas y) g0)
                         (\z. Q %% rfs_pullback atlasA (phi o chart_inv (chart_at atlas y)) gA z)
                         (SND(chart_at atlas y) y) <= th)
              ==> rfs_neck (top,atlas) g0 eps' (psi x) (psi o e)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  ABBREV_TAC `q = (eps' - eps) / &4` THEN
  SUBGOAL_THEN `&0 < q /\ 2 <= k /\ rfs_kreg eps' <= k` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "k" THEN MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "k" THEN MATCH_MP_TAC APX_KREG_MONO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "chain"))
    (SPEC `k:num` P2HN_CLOSE_CHAIN) THEN
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  X_CHOOSE_TAC `K1:real` (SPEC `K0 pow 2` LRG_RM_NEAR_BOUND) THEN
  ABBREV_TAC `a = min (&1 / &2) (q / (&1 + sqrt(&3)))` THEN
  SUBGOAL_THEN `&0 < a /\ a <= &1 / &2 /\ a * (&1 + sqrt(&3)) <= q` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 + sqrt(&3)` ASSUME_TAC THENL
     [MP_TAC(SPEC `&3` SQRT_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "a" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q / (&1 + sqrt(&3)) * (&1 + sqrt(&3))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`abs K1 + &1`; `a:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))) THEN
  ABBREV_TAC `m3 = min (&1 / &4) (min (eta pow 2 / &2) (q pow 2))` THEN
  ABBREV_TAC `C1 = (&1 + inv c1) pow k` THEN
  SUBGOAL_THEN `&0 < m3 /\ m3 <= &1 / &4 /\ m3 < eta pow 2 /\ m3 <= q pow 2 /\ &1 <= C1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m3" THEN EXPAND_TAC "C1" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < e ==> min a (min (e / &2) b) < e`) THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  EXISTS_TAC `m3 / (C1 * (M + &1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `th = m3 / (C1 * (M + &1))` THEN
  SUBGOAL_THEN `C1 * th <= &1 / &4 /\ M * (C1 * th) < eta pow 2 /\ M * (C1 * th) <= q pow 2 /\
                &0 <= C1 * th`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `t = m3 / (M + &1)` THEN
    SUBGOAL_THEN `C1 * th = t` SUBST1_TAC THENL
     [EXPAND_TAC "th" THEN EXPAND_TAC "t" THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
      SUBGOAL_THEN `~(C1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t /\ t * (M + &1) = m3` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= M * t` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M * t = m3 - t` ASSUME_TAC THENL
     [UNDISCH_TAC `t * (M + &1) = m3` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the instance *)
  MAP_EVERY X_GEN_TAC
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
    `topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`; `gA:A->real^3^3`;
    `W:B->bool`; `phi:B->A`; `psi:A->B`; `Q:real`; `x:A`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s (G0:real^3->real^3^3) G y.
      metric_field s G0 /\ metric_field s G /\ y IN s /\
      lrm_deriv_norm2 0 G0 y <= (abs K1 + &1) pow 2 /\ lck_dist2 2 G0 G y < eta pow 2
      ==> abs(lscalar G y - lscalar G0 y) <= a`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "stab" (MP_TAC o SPECL [`s:real^3->bool`; `G0:real^3->real^3^3`;
                                     `G:real^3->real^3^3`; `y:real^3`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= th` ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P2HN_NECK_TO_LIMIT_INST THEN
  MAP_EVERY EXISTS_TAC
   [`eps:real`; `c1:real`; `M:real`; `K0:real`; `K1:real`; `a:real`; `eta:real`; `th:real`;
    `topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`; `gA:A->real^3^3`;
    `W:B->bool`; `phi:B->A`; `Q:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The flow-limit closeness in the charts of an approximant, with the        *)
(* approximant metric as base (the closeness clause of the statements        *)
(* P2C_REQ_CAP_FIX and P2C_REQ_SLICE_FIX), by the naturality of the C^k      *)
(* distance in the parametrization psi o chart_inv and the reverse base      *)
(* change.                                                                   *)
(* ========================================================================= *)

let P2HN_MPULLBACK_CONG = prove
 (`!(h1:real^N->real^N) h2 (G:real^N->real^N^N) N y.
     open N /\ y IN N /\ (!z. z IN N ==> h1 z = h2 z)
     ==> mpullback h1 G y = mpullback h2 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `(h1:real^N->real^N) y = h2 y` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (h1:real^N->real^N) (at y) = frechet_derivative h2 (at y)`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN ABS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `h1:real^N->real^N`; EXISTS_TAC `h2:real^N->real^N`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

(* The pullback by the inverse of a chart is the chart representative.      *)

let P2HN_CHART_INV_PULLBACK = prove
 (`!top atlas (V:A->bool) (ch:A->real^N) (g:A->real^N^N) w.
     smooth_manifold_atlas top atlas /\ (V,ch) IN atlas /\ w IN IMAGE ch V
     ==> rfs_pullback atlas (chart_inv (V,ch)) g w = metric_local atlas (V,ch) g w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (IMAGE ch V) (chart_inv (V:A->bool,ch:A->real^N))`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `ch:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `mpullback ((ch:A->real^N) o chart_inv (V,ch)) (metric_local atlas (V,ch) (g:A->real^N^N)) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `IMAGE (ch:A->real^N) V`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `mpullback (\x:real^N. x) (metric_local atlas (V,ch) (g:A->real^N^N)) w` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[P2B9_MPULLBACK_ID]] THEN
  MATCH_MP_TAC P2HN_MPULLBACK_CONG THEN EXISTS_TAC `IMAGE (ch:A->real^N) V` THEN
  ASM_SIMP_TAC[o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `IMAGE (ch:A->real^N) V`; `chart_inv (V:A->bool,ch:A->real^N)`]
    MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The flow-limit closeness (limit chart, limit metric as base) gives the   *)
(* closeness in the preferred chart of the approximant at y, with the       *)
(* rescaled approximant metric R gA as base and the rescaled pullback of    *)
(* inv Q g0 by psi as the other metric (the form of P2C_REQ_CAP_FIX).       *)

let P2HN_LCK_SOURCE_FROM_LIMIT = prove
 (`!k. ?M. &0 <= M /\
     !top atlas (g0:B->real^3^3) (topA:A topology) atlasA gA W phi psi Q R y th.
       smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topA atlasA /\
       riemannian_metric atlas g0 /\ riemannian_metric atlasA gA /\
       mfd_diffeo top atlas W topA atlasA (IMAGE phi W) phi psi /\
       y IN IMAGE phi W /\ &0 < Q /\ &0 < R /\
       lck_dist2 k (metric_local atlas (chart_at atlas (psi y)) g0)
                   (\z. Q %% rfs_pullback atlasA (phi o chart_inv (chart_at atlas (psi y))) gA z)
                   (SND(chart_at atlas (psi y)) (psi y)) <= th /\
       th <= &1 / &4
       ==> lck_dist2 k (metric_local atlasA (chart_at atlasA y) (\w. R %% gA w))
                       (metric_local atlasA (chart_at atlasA y)
                          (\w. R %% mfd_pullback_metric atlasA atlas psi (\v. inv Q %% g0 v) w))
                       (SND(chart_at atlasA y) y)
           <= (&1 + Q / R) pow k * M * th`,
  GEN_TAC THEN
  X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rev"))
    (INST_TYPE [`:3`,`:N`] (SPEC `k:num` LCK_CK_BASE_REV)) THEN
  EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in topA (IMAGE (phi:B->A) W) /\ (y:A) IN topspace topA` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo top (atlas:((B->bool)#(B->real^3))->bool) W topA
                 (atlasA:((A->bool)#(A->real^3))->bool) (IMAGE (phi:B->A) W) phi psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlasA:((A->bool)#(A->real^3))->bool) (y:A)`,
           `c:(A->bool)#(A->real^3)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `ch:A->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                 `V:A->bool`; `ch:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param topA atlasA (IMAGE ch V) (chart_inv (V:A->bool,ch:A->real^3))`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `N = {z | z IN IMAGE (ch:A->real^3) V /\
                       chart_inv (V:A->bool,ch:A->real^3) z IN IMAGE (phi:B->A) W}` THEN
  SUBGOAL_THEN `open (N:real^3->bool) /\ N SUBSET IMAGE (ch:A->real^3) V /\
                (ch:A->real^3) y IN N /\
                IMAGE (chart_inv (V:A->bool,ch:A->real^3)) N SUBSET IMAGE (phi:B->A) W`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
        check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "chart_inv"
                                                  with Failure _ -> false)) (concl th) &&
                         can (find_term (fun t -> try fst(dest_const t) = "mfd_param"
                                                  with Failure _ -> false)) (concl th))) THEN
      MP_TAC(ISPECL [`chart_inv (V:A->bool,ch:A->real^3)`;
                     `subtopology euclidean (IMAGE (ch:A->real^3) V)`; `topA:A topology`;
                     `IMAGE (phi:B->A) W`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
      SUBGOAL_THEN `{x | x IN IMAGE (ch:A->real^3) V /\
                         chart_inv (V:A->bool,ch:A->real^3) x IN IMAGE (phi:B->A) W} = N`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
      EXISTS_TAC `IMAGE (ch:A->real^3) V` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "N" THEN SET_TAC[];
      EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
      EXPAND_TAC "N" THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `q = (psi:A->B) o chart_inv (V:A->bool,ch:A->real^3)` THEN
  SUBGOAL_THEN `mfd_param top atlas N (q:real^3->B) /\ IMAGE q N SUBSET (W:B->bool) /\
                q((ch:A->real^3) y) = psi y /\
                (!z. z IN N ==> (phi:B->A) (q z) = chart_inv (V:A->bool,ch:A->real^3) z)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                            `IMAGE (phi:B->A) W`; `W:B->bool`; `phi:B->A`] THEN
      ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `IMAGE (ch:A->real^3) V` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_o] THEN
      UNDISCH_TAC `IMAGE (chart_inv (V:A->bool,ch:A->real^3)) N SUBSET IMAGE (phi:B->A) W` THEN
      UNDISCH_TAC `IMAGE (psi:A->B) (IMAGE (phi:B->A) W) SUBSET W` THEN SET_TAC[];
      AP_TERM_TAC THEN ASM_SIMP_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `IMAGE (chart_inv (V:A->bool,ch:A->real^3)) N SUBSET IMAGE (phi:B->A) W` THEN
      UNDISCH_TAC `(z:real^3) IN N` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `G0 = rfs_pullback atlas (q:real^3->B) (g0:B->real^3^3)` THEN
  ABBREV_TAC `G1 = \z. Q %% metric_local atlasA (V:A->bool,ch:A->real^3) (gA:A->real^3^3) z` THEN
  SUBGOAL_THEN `metric_field N (G0:real^3->real^3^3) /\ metric_field N (G1:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G0" THEN EXPAND_TAC "G1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (ch:A->real^3) V` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `riemannian_metric (atlasA:((A->bool)#(A->real^3))->bool) gA` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,ch:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  (* the limit-side closeness read in the parametrization q *)
  SUBGOAL_THEN `lck_dist2 k (G0:real^3->real^3^3) G1 ((ch:A->real^3) y) <= th` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                   `gA:A->real^3^3`; `W:B->bool`; `phi:B->A`; `psi:A->B`; `N:real^3->bool`;
                   `q:real^3->B`; `Q:real`; `k:num`; `(ch:A->real^3) y`]
      P2HN_FLOW_CLOSE_PARAM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `lck_dist2 k (G0:real^3->real^3^3)
        (\z. Q %% rfs_pullback atlasA ((phi:B->A) o q) (gA:A->real^3^3) z) ((ch:A->real^3) y) =
      lck_dist2 k G0 G1 (ch y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `N:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      EXPAND_TAC "G1" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      TRANS_TAC EQ_TRANS
       `rfs_pullback atlasA (chart_inv (V:A->bool,ch:A->real^3)) (gA:A->real^3^3) z` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2HN_RFS_PULLBACK_CONG THEN EXISTS_TAC `N:real^3->bool` THEN
        ASM_SIMP_TAC[o_THM];
        MATCH_MP_TAC P2HN_CHART_INV_PULLBACK THEN EXISTS_TAC `topA:A topology` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* base swap and rescaling *)
  SUBGOAL_THEN `lck_dist2 k (G1:real^3->real^3^3) G0 ((ch:A->real^3) y) <= M * th`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * lck_dist2 k (G0:real^3->real^3^3) (\z. G0 z + G0 z - G1 z)
                              ((ch:A->real^3) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "rev" (MATCH_MP_TAC o SPECL [`N:real^3->bool`; `G0:real^3->real^3^3`;
        `G1:real^3->real^3^3`; `G0:real^3->real^3^3`; `(ch:A->real^3) y`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`k:num`; `N:real^3->bool`; `G0:real^3->real^3^3`; `G1:real^3->real^3^3`;
                     `(ch:A->real^3) y`] LCK_DIST2_REFLECT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 k (metric_local atlasA (V,ch) (\w. R %% (gA:A->real^3^3) w))
       (metric_local atlasA (V,ch)
          (\w. R %% mfd_pullback_metric atlasA atlas (psi:A->B) (\v. inv Q %% g0 v) w))
       ((ch:A->real^3) y) =
    lck_dist2 k (\z. (R / Q) %% (G1:real^3->real^3^3) z) (\z. (R / Q) %% G0 z) (ch y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `N:real^3->bool` THEN
    ASM_REWRITE_TAC[METRIC_LOCAL_CMUL] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXPAND_TAC "G0" THEN EXPAND_TAC "G1" THEN REWRITE_TAC[MATRIX_CMUL_ASSOC; ETA_AX] THEN
    CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `metric_local atlasA (V,ch) (mfd_pullback_metric atlasA atlas (psi:A->B)
                                    (\v. inv Q %% (g0:B->real^3^3) v)) z =
      rfs_pullback atlas (psi o chart_inv (V:A->bool,ch:A->real^3)) (\v. inv Q %% g0 v) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P2BL_PB_CHART THEN
      MAP_EVERY EXISTS_TAC [`topA:A topology`; `top:B topology`; `IMAGE (phi:B->A) W`;
                            `W:B->bool`; `phi:B->A`] THEN
      ASM_SIMP_TAC[MFD_DIFFEO_SYM; FST; SND] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (V:A->bool,ch:A->real^3) z` THEN
      UNDISCH_TAC `IMAGE (chart_inv (V:A->bool,ch:A->real^3)) N SUBSET IMAGE (phi:B->A) W` THEN
      UNDISCH_TAC `(z:real^3) IN N` THEN UNDISCH_TAC `N SUBSET IMAGE (ch:A->real^3) V` THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[P2B9_RFS_PULLBACK_CMUL; MATRIX_CMUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv(R / Q)) pow k * lck_dist2 k (G1:real^3->real^3^3) G0 ((ch:A->real^3) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2B9S_LCK_SCALE_LE THEN EXISTS_TAC `N:real^3->bool` THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_DIV; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Connected balls; scalar curvature is                                     *)
(* bounded below near a point of large curvature (THM_10_2_VIEW at an       *)
(* intermediate point of the ball, MT p. 287).                             *)
(* ========================================================================= *)

let P2HN_MFD_BALL_CONNECTED = prove
 (`!top atlas (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> connected_in top (mfd_ball (top,atlas) g x r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) (g:A->real^N^N) x r =
    UNIONS {IMAGE gamma (real_interval[&0,&1]) | gamma |
            mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\
            mfd_length atlas g gamma (&0) (&1) < r}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `y:A`;
                     `r - mfd_dist (top,atlas) (g:A->real^N^N) x y`] P2BC_DIST_APPROX) THEN
      ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (gamma:real->A) (real_interval[&0,&1])` THEN CONJ_TAC THENL
       [EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `&1` THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `gamma:real->A` THEN
      STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      MATCH_MP_TAC LIM_CURVE_IN_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_IN_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
    ASM_MESON_TAC[mfd_c1_curve];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERS; FORALL_IN_GSPEC] THEN
    EXISTS_TAC `x:A` THEN X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]);;

let P2HN_VBALL_EQ = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x r.
     rfs_vball V t x r = mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* MT p. 287 (scalar curvature near a point of large curvature cannot be    *)
(* much smaller): if w in B(x,t,D R(x)^(-1/2)) had R(w) < R(x)/D1, the      *)
(* connected ball would contain w' with R(w') = R(x)/D1, and THM_10_2_VIEW  *)
(* at w' with radius D would give R(x) <= D2 R(w') < R(x).                  *)

let P2HN_R_LOWER_NEAR = prove
 (`!u:A->bool.
     P2C_REQ_THM_10_2_VIEW_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C D. &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < D
             ==> ?D1 Q1. &1 <= D1 /\
                   !V x t Lc.
                     p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) /\
                     rfs_pinched V /\ (!s. s < &0 ==> rfs_vtop V s = discrete_topology {}) /\
                     (!s. apx_sphere_sep (rfs_vtop V s) (rfs_vatlas V s)) /\
                     x IN topspace(rfs_vtop V t) /\
                     (!y s. s <= t /\ y IN topspace(rfs_vtop V s) /\ Lc <= rfs_vscalar V s y
                            ==> p3_canon_at V C eps y s) /\
                     Q1 <= rfs_vscalar V t x /\ D1 * Lc <= rfs_vscalar V t x
                     ==> !w. w IN rfs_vball V t x (D * inv(sqrt(rfs_vscalar V t x)))
                             ==> rfs_vscalar V t x <= D1 * rfs_vscalar V t w`,
  GEN_TAC THEN REWRITE_TAC[P2C_REQ_THM_10_2_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T102"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `D:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "T102" (MP_TAC o SPECL [`eps:real`; `C:real`; `D:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))))) THEN
  MAP_EVERY EXISTS_TAC [`D2 + &1`; `D0 * (D2 + &1)`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `t:real`; `Lc:real`] THEN
  STRIP_TAC THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t x` THEN
  ABBREV_TAC `L = Q / (D2 + &1)` THEN
  SUBGOAL_THEN `&0 < Q /\ D0 <= L /\ Lc <= L /\ L <= Q /\ D2 * L < Q` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < D0 * (D2 + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `L * (D2 + &1) = Q` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `D0 * (D2 + &1) <= L * (D2 + &1)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `(a <= b <=> c <= d) ==> a <= b ==> c <= d`) THEN
        MATCH_MP_TAC REAL_LE_RMUL_EQ THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `Lc * (D2 + &1) <= L * (D2 + &1)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `(a <= b <=> c <= d) ==> a <= b ==> c <= d`) THEN
        MATCH_MP_TAC REAL_LE_RMUL_EQ THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= L * D2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `L * (D2 + &1) = Q` THEN UNDISCH_TAC `&0 < L` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `L * (D2 + &1) = Q` THEN UNDISCH_TAC `&0 < L` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(D1 * a < Q) ==> Q <= D1 * a`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) t w < L` ASSUME_TAC THENL
   [SUBGOAL_THEN `L * (D2 + &1) = Q` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(D2 + &1) * rfs_vscalar (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t w <
                  (D2 + &1) * L` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `(a < b <=> c < d) ==> a < b ==> c < d`) THEN
      MATCH_MP_TAC REAL_LT_LMUL_EQ THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the slice at t *)
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t) /\
    smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
    riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* an intermediate point with R = L *)
  SUBGOAL_THEN
   `?w'. w' IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) t x (D * inv(sqrt Q)) /\
         rfs_vscalar V t w' = L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `is_realinterval (IMAGE (rfs_vscalar (V:(real->A topology)#
                                          (real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) t)
                             (rfs_vball V t x (D * inv(sqrt Q))))`
    MP_TAC THENL
     [REWRITE_TAC[GSYM CONNECTED_IN_EUCLIDEANREAL] THEN
      MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) t` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN
        MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t`;
                       `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) t`;
                       `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) t`] MFD_SCALAR_CONTINUOUS) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) t =
                      mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t)`
        (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[FUN_EQ_THM] THEN
        SPEC_TAC(`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`,
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`) THEN
        REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric];
        SUBGOAL_THEN `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) t x (D * inv(sqrt Q)) =
                      mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x (D * inv(sqrt Q))`
        SUBST1_TAC THENL
         [SPEC_TAC(`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`,
                   `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`) THEN
          REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric];
          MATCH_MP_TAC P2HN_MFD_BALL_CONNECTED THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) t w`; `Q:real`; `L:real`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[P2HN_VBALL_EQ; mfd_ball; IN_ELIM_THM] THEN
        ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  (* THM_10_2_VIEW at w' with radius D *)
  SUBGOAL_THEN `(w':A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) /\
                mfd_joinable (rfs_vtop V t,rfs_vatlas V t) x w' /\
                mfd_dist (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x w' < D * inv(sqrt Q)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w':A) IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x (D * inv(sqrt Q))` THEN
    REWRITE_TAC[P2HN_VBALL_EQ; mfd_ball; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  USE_THEN "bd" (MP_TAC o SPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `w':A`; `t:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Lc:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[P2HN_VBALL_EQ; mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`;
                   `x:A`; `w':A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `D * inv(sqrt Q)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Horn sets: closed (properness), inner part open, frontier in the inner   *)
(* sphere; a connected set through a horn point that misses the inner      *)
(* sphere stays in the horn set.                                             *)
(* ------------------------------------------------------------------------- *)

let P2HN_MFD_COMPACT_NBHD = prove
 (`!top atlas (z:A).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ z IN topspace top
     ==> ?N K. open_in top N /\ z IN N /\ N SUBSET K /\ compact_in top K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `ch:A->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (IMAGE ch V) (chart_inv (V:A->bool,ch:A->real^N))`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `ch:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(ch:A->real^N) z IN IMAGE ch V` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o check (fun th ->
    concl th = `open (IMAGE (ch:A->real^N) V)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `(ch:A->real^N) z`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (chart_inv (V:A->bool,ch:A->real^N)) (ball((ch:A->real^N) z,rho))`;
    `IMAGE (chart_inv (V:A->bool,ch:A->real^N)) (cball((ch:A->real^N) z,rho))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `IMAGE (ch:A->real^N) V`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(ch:A->real^N) z` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `IMAGE (ch:A->real^N) V`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL]]);;

(* Images of closed subsets of the horn domain are closed (properness).      *)

let P2HN_HORN_CLOSED_IMAGE = prove
 (`!top atlas (H:real^3->A) C.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
     closed C /\ C SUBSET {y | &1 <= norm y}
     ==> closed_in top (IMAGE H C)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `H':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `(C:real^3->bool) SUBSET {y | &1 / &2 < norm y}` ASSUME_TAC THENL
   [UNDISCH_TAC `(C:real^3->bool) SUBSET {y | &1 <= norm y}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_ARITH `&1 <= x ==> &1 / &2 < x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (H:real^3->A) C SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_PARAM_IMAGE_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_EQ] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `z:A`]
    P2HN_MFD_COMPACT_NBHD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `TT = {y:real^3 | y IN C /\ (H:real^3->A) y IN K}` THEN
  SUBGOAL_THEN `compact (TT:real^3->bool) /\ TT SUBSET {y | &1 / &2 < norm y}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "TT" THEN
      UNDISCH_TAC `(C:real^3->bool) SUBSET {y | &1 / &2 < norm y}` THEN SET_TAC[]] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `{y:real^3 | &1 <= norm y /\ (H:real^3->A) y IN K}` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "TT" THEN UNDISCH_TAC `(C:real^3->bool) SUBSET {y | &1 <= norm y}` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:real^3->A`; `subtopology euclidean {y:real^3 | &1 / &2 < norm y}`;
                   `top:A topology`; `K:A->bool`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                 INTER_UNIV; CLOSED_IN_CLOSED] THEN
    DISCH_THEN(X_CHOOSE_THEN `FF:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `TT = FF INTER (C:real^3->bool)` SUBST1_TAC THENL
     [EXPAND_TAC "TT" THEN
      UNDISCH_TAC `{x | x IN {y:real^3 | &1 / &2 < norm y} /\ (H:real^3->A) x IN K} =
                   {y | &1 / &2 < norm y} INTER FF` THEN
      UNDISCH_TAC `(C:real^3->bool) SUBSET {y | &1 / &2 < norm y}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (H:real^3->A) TT)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `{y:real^3 | &1 / &2 < norm y}`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN top closure_of (N INTER IMAGE (H:real^3->A) C)` MP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `N:A->bool`; `IMAGE (H:real^3->A) C`]
      OPEN_IN_INTER_CLOSURE_OF_SUBSET) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (N INTER IMAGE (H:real^3->A) C) SUBSET IMAGE H TT` MP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `N INTER IMAGE (H:real^3->A) C`;
                   `IMAGE (H:real^3->A) TT`] CLOSURE_OF_MINIMAL_EQ) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "TT" THEN UNDISCH_TAC `(N:A->bool) SUBSET K` THEN SET_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "TT" THEN SET_TAC[]);;

(* The horn set itself.                                                       *)

let P2HN_HORN_SET_CLOSED = prove
 (`!top atlas (H:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K})
     ==> closed_in top (IMAGE H {y | &1 <= norm y})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2HN_HORN_CLOSED_IMAGE THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  SUBGOAL_THEN `{y:real^3 | &1 <= norm y} = (:real^3) DIFF ball(vec 0,&1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_BALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_UNIV; OPEN_BALL]]);;

let P2HN_HORN_FRONTIER = prove
 (`!top atlas (H:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K})
     ==> top frontier_of (IMAGE H {y | &1 <= norm y}) SUBSET IMAGE H (sphere(vec 0,&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `H:real^3->A`]
    P2HN_HORN_SET_CLOSED) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (H:real^3->A) {y | &1 < norm y} SUBSET
                top interior_of (IMAGE H {y | &1 <= norm y})` ASSUME_TAC THENL
   [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `{y:real^3 | &1 / &2 < norm y}`] THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `{y:real^3 | &1 < norm y} = (:real^3) DIFF cball(vec 0,&1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV; CLOSED_CBALL]]];
    ALL_TAC] THEN
  REWRITE_TAC[frontier_of] THEN
  FIRST_ASSUM(SUBST1_TAC o REWRITE_RULE[GSYM CLOSURE_OF_EQ]) THEN
  UNDISCH_TAC `IMAGE (H:real^3->A) {y | &1 < norm y} SUBSET
               top interior_of (IMAGE H {y | &1 <= norm y})` THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE; IN_ELIM_THM; IN_SPHERE_0] THEN
  MESON_TAC[REAL_ARITH `&1 <= x ==> &1 < x \/ x = &1`]);;

let P2HN_CONNECTED_IN_HORN = prove
 (`!top atlas (H:real^3->A) c.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
     connected_in top c /\ ~DISJOINT c (IMAGE H {y | &1 <= norm y}) /\
     DISJOINT c (IMAGE H (sphere(vec 0,&1)))
     ==> c SUBSET IMAGE H {y | &1 <= norm y}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `c:A->bool`; `IMAGE (H:real^3->A) {y | &1 <= norm y}`]
    CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `H:real^3->A`]
    P2HN_HORN_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~DISJOINT c (IMAGE (H:real^3->A) {y | &1 <= norm y})` THEN
  UNDISCH_TAC `DISJOINT c (IMAGE (H:real^3->A) (sphere(vec 0,&1)))` THEN
  UNDISCH_TAC `~(c SUBSET IMAGE (H:real^3->A) {y | &1 <= norm y})` THEN
  SET_TAC[]);;

(* Near the centre of a neck the scalar curvature is at most 3/2 R(centre). *)

let P2HN_NECK_SCALAR_NEAR = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x e w.
       &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ riemannian_metric atlas g /\
       rfs_neck (top,atlas) g eps x e /\
       w IN mfd_ball (top,atlas) g x (&2 * inv(sqrt(mfd_scalar atlas g x)))
       ==> mfd_scalar atlas g w <= &3 / &2 * mfd_scalar atlas g x`,
  MP_TAC(SPEC `&1 / &2` (REWRITE_RULE[APX_NECK_CURV_STATEMENT] (ISPEC `(:A)` APX_NECK_CURV))) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  EXISTS_TAC `min eps1 (&1 / &20)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `&2 * inv(sqrt R)`] P2BN_NECK_BALL_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_OF_NUM_LT;
                                                ARITH];
      ASM_SIMP_TAC[REAL_FIELD `&0 < s ==> (&2 * inv s) * s = &2`; SQRT_POS_LT; REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[IN_DIFF] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    UNDISCH_TAC `(y:real^3) IN cball(vec 0,exp(&3)) DIFF ball(vec 0,exp(--(&3)))` THEN
    REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
    SUBGOAL_THEN `&3 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
     [SUBGOAL_THEN `sqrt(&2) * eps < &1 / &3` MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * &1 / &20` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        DISCH_TAC THEN
        SUBGOAL_THEN `&0 < sqrt(&2) * eps` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_RINV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--(&3))` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(&3)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "curv" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`]
    (REWRITE_RULE[APX_PULLBACK_SCALAR_STATEMENT] (ISPEC `(:A)` APX_PULLBACK_SCALAR))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lscalar (\z. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) z) y =
                lscalar (rfs_pullback atlas e g) y / R` SUBST1_TAC THENL
   [MATCH_MP_TAC LSCALAR_SCALE THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) (e(y:real^3)) =
               lscalar (rfs_pullback atlas e g) y` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) (e(y:real^3)) / R <= &3 / &2` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* Balls about a horn point of large curvature miss the inner sphere and   *)
(* hence lie in the horn set (MT Claim 11.33, first part).                  *)

let P2HN_BALL_IN_HORN_SLICE = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) en (H:real^3->A) Mb x r.
       &0 < en /\ en <= eps1 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
       riemannian_metric atlas g /\
       mfd_param top atlas {y | &1 / &2 < norm y} H /\
       (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
       (!z. z IN sphere(vec 0,&1) ==> ?e. rfs_neck (top,atlas) g en (H z) e) /\
       &0 < Mb /\ (!z. z IN sphere(vec 0,&1) ==> mfd_scalar atlas g (H z) <= Mb) /\
       x IN IMAGE H {y | &1 <= norm y} /\ &3 / &2 * Mb < mfd_scalar atlas g x /\
       &0 < r /\ r <= inv(sqrt Mb)
       ==> mfd_ball (top,atlas) g x r SUBSET IMAGE H {y | &1 <= norm y}`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))
    P2HN_NECK_SCALAR_NEAR THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `{y:real^3 | &1 / &2 < norm y}`; `H:real^3->A`; `{y:real^3 | &1 <= norm y}`]
      MFD_PARAM_IMAGE_SUBSET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(x:A) IN IMAGE (H:real^3->A) {y | &1 <= norm y}` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2HN_CONNECTED_IN_HORN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  ASM_SIMP_TAC[P2HN_MFD_BALL_CONNECTED] THEN CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `q:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `q:A = H(z:real^3)`)) THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `e:real^3->A` o C MATCH_MP (ASSUME `(z:real^3) IN sphere(vec 0,&1)`) o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_neck" with Failure _ -> false))
          (concl th))) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((H:real^3->A) z) /\
                mfd_scalar atlas g (H z) <= Mb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[rfs_neck]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `en:real`; `(H:real^3->A) z`; `e:real^3->A`; `x:A`]) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `(H:real^3->A) z`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(sqrt Mb)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ b <= a ==> b <= &2 * a`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]);;

(* A nonempty compact component of the target cannot lie inside the image   *)
(* of a diffeomorphism from an open subset of a connected noncompact space. *)

let P2HN_COMPONENT_IN_IMAGE_ABSURD = prove
 (`!(topl:B topology) (atlasl:((B->bool)#(B->real^3))->bool) (topA:A topology)
    (atlasA:((A->bool)#(A->real^3))->bool) W (phi:B->A) psi U.
     hausdorff_space topl /\ connected_space topl /\ ~compact_space topl /\
     smooth_manifold_atlas topA atlasA /\
     mfd_diffeo topl atlasl W topA atlasA (IMAGE phi W) phi psi /\
     U IN connected_components_of topA /\ compact_in topA U /\
     U SUBSET IMAGE phi W
     ==> F`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in topA (U:A->bool) /\ ~(U = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
      ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED;
                    LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE];
      ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in topl (IMAGE (psi:A->B) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology topA (IMAGE (phi:B->A) W)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topl (IMAGE (psi:A->B) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:B->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      try fst(dest_const t) = "homeomorphic_maps" with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[HOMEOMORPHIC_MAPS_MAP] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`psi:A->B`; `subtopology topA (IMAGE (phi:B->A) W)`;
                   `subtopology topl (W:B->bool)`; `U:A->bool`] HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET_INTER]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:A->B) U = topspace topl` ASSUME_TAC THENL
   [UNDISCH_TAC `connected_space (topl:B topology)` THEN
    REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (psi:A->B) U`) THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `~compact_space (topl:B topology)` THEN
  REWRITE_TAC[compact_space] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Horn sequences.  p2hn_hseq collects the                                  *)
(* properties of the maximal extensions V n of the bad histories of the     *)
(* proof of MT Thm 11.31 that the blow-up argument uses: regular pinched    *)
(* views with empty slices before 0 and separating neck spheres, base      *)
(* points x n in en-horns H n of the slice at t n whose inner spheres have  *)
(* R <= Mb, (C1,eps1)-canonical neighbourhoods above a fixed level Lc, and *)
(* R(x n, t n) -> infinity; slices before t n are compact, and R is proper *)
(* on the slice at t n.                                                      *)
(* ========================================================================= *)

let p2hn_hseq = new_definition
 `p2hn_hseq (C1:real,eps1:real,en:real,Lc:real,Mb:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) (t:num->real) (H:num->real^3->A) <=>
    &0 < Mb /\
    (!n. p2c_regular_view (V n) /\ rfs_pinched (V n) /\
         (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {}) /\
         (!s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
         p3_horn (V n) (t n) en (H n) /\ x n IN p3_horn_set (H n) /\
         (!z. z IN sphere(vec 0,&1) ==> rfs_vscalar (V n) (t n) (H n z) <= Mb) /\
         (!y s. s <= t n /\ y IN topspace(rfs_vtop (V n) s) /\ Lc <= rfs_vscalar (V n) s y
                ==> p3_canon_at (V n) C1 eps1 y s) /\
         (!s. s < t n ==> compact_space (rfs_vtop (V n) s)) /\
         (!c. compact_in (rfs_vtop (V n) (t n))
                {y | y IN topspace(rfs_vtop (V n) (t n)) /\ rfs_vscalar (V n) (t n) y <= c})) /\
    (!B. ?N. !n. N <= n ==> B < rfs_vscalar (V n) (t n) (x n))`;;

let P2HN_HSEQ_SUBSEQ = prove
 (`!C1 eps1 en Lc Mb V (x:num->A) t H sub.
     p2hn_hseq (C1,eps1,en,Lc,Mb) V x t H /\ p3_subseq sub
     ==> p2hn_hseq (C1,eps1,en,Lc,Mb) (V o sub) (x o sub) (t o sub) (H o sub)`,
  REWRITE_TAC[p2hn_hseq; p3_subseq; o_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "Q"))) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `B:real` THEN
  USE_THEN "Q" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MONOTONE_BIGGER]);;

(* Strong necks of a view give necks of the slice. *)

let P2HN_STRONG_NECK_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t e.
     rfs_strong_neck V eps x t e
     ==> rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps x e`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_strong_neck; rfs_evolving_neck; rfs_vtop; rfs_vatlas;
              rfs_vmetric] THEN MESON_TAC[]);;

(* MT Claim 11.33, first part: the balls B(x n, t n, A Q n^(-1/2)) lie in   *)
(* the horns for n large.                                                    *)

let P2HN_HSEQ_BALL_IN_HORN = prove
 (`?eps1. &0 < eps1 /\
     !C1 eps1' en Lc Mb V (x:num->A) t H.
       &0 < en /\ en <= eps1 /\ p2hn_hseq (C1,eps1',en,Lc,Mb) V x t H
       ==> !A. &0 < A
               ==> ?N. !n. N <= n
                       ==> rfs_vball (V n) (t n) (x n)
                             (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                           SUBSET p3_horn_set (H n)`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "slice"))
    P2HN_BALL_IN_HORN_SLICE THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[p2hn_hseq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "Q"))))) THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "Q" (X_CHOOSE_TAC `N:num` o SPEC `max (&3 / &2 * Mb) (A pow 2 * Mb)`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_MAX_LT] THEN STRIP_TAC THEN
  USE_THEN "per" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `Vn = (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) n` THEN
  ABBREV_TAC `Q = rfs_vscalar (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (t(n:num)) (x n)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_horn] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "p3_horn" with Failure _ -> false))
        (concl th))) THEN
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (t(n:num))) /\
    smooth_manifold_atlas (rfs_vtop Vn (t n)) (rfs_vatlas Vn (t n)) /\
    riemannian_metric (rfs_vatlas Vn (t n)) (rfs_vmetric Vn (t n)) /\
    (x:num->A) n IN topspace (rfs_vtop Vn (t n))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:num->A) n IN topspace (rfs_vtop (Vn:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t(n:num)))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(x:num->A) n IN p3_horn_set (H(n:num))` THEN REWRITE_TAC[p3_horn_set] THEN
      MP_TAC(ISPECL [`rfs_vtop (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (t(n:num))`;
                     `rfs_vatlas (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (t(n:num))`;
                     `{y:real^3 | &1 / &2 < norm y}`; `(H:num->real^3->A) n`;
                     `{y:real^3 | &1 <= norm y}`] MFD_PARAM_IMAGE_SUBSET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2c_regular_view (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[P2HN_VBALL_EQ; p3_horn_set] THEN
  USE_THEN "slice" MATCH_MP_TAC THEN EXISTS_TAC `en:real` THEN EXISTS_TAC `Mb:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_strong_neck"
                               with Failure _ -> false)) (concl th) &&
      not (is_exists(concl th)))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN REAL_ARITH_TAC;
      MESON_TAC[P2HN_STRONG_NECK_SLICE]];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Mb:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`,
             `Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric];
    UNDISCH_TAC `(x:num->A) n IN p3_horn_set (H(n:num))` THEN REWRITE_TAC[p3_horn_set];
    SUBGOAL_THEN `mfd_scalar (rfs_vatlas (Vn:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t(n:num)))
                    (rfs_vmetric Vn (t n)) (x n) = Q` SUBST1_TAC THENL
     [EXPAND_TAC "Q" THEN
      SPEC_TAC(`Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)`,
               `Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < Q /\ &0 < sqrt Mb /\ &0 < A * sqrt Mb` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[SQRT_POS_LT];
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * inv(A * sqrt Mb)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `A * sqrt Mb = sqrt(A pow 2 * Mb)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE; POW_2_SQRT];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL]]]);;

(* ========================================================================= *)
(* The Q0 propagation step of MT p. 291.                                    *)
(* MT: 'for all t in [-t',0] we have R(phi_n(z),t) <= R(phi_n(z),0) (this   *)
(* follows from the fact that the partial derivative in the time-direction  *)
(* of the scalar curvature of a strong eps-neck of scale one is positive    *)
(* and bounded away from 0)', and Q0 (the bound of R on the time-0 limit)   *)
(* then bounds R on the whole backward window.  Our form: if (x,s) is the   *)
(* centre of a strong eps-neck for every s in [s0,s1], then                 *)
(* R(x,s) <= (1 + alpha) R(x,s1) on [s0,s1] (P2HN_NECK_R_BACKWARD); the     *)
(* estimate along one strong neck is P2BN_NECK_SCALAR, chained backwards in *)
(* steps of length 1/(2 R).  Deviation from MT: the bound Q0 is not read    *)
(* off a limit that is identified as a product S^2 x R (no splitting        *)
(* theorem); it is the sequence property R <= Qb Q_n on the A-balls at the  *)
(* final times, which passes to subsequences (P2HN_Q0_PROPAGATION).         *)
(* ========================================================================= *)

(* One strong neck: R(x,s) <= (1/(1 - (s-u)R(x,u)) + alpha) R(x,u).          *)

let P2HN_NECK_R_STEP = prove
 (`!alpha. &0 < alpha
     ==> ?eps2. &0 < eps2 /\
           !V eps (x:A) u e s.
              p2c_regular_view V /\ rfs_strong_neck V eps x u e /\ eps <= eps2 /\
              u - inv(rfs_vscalar V u x) < s /\ s <= u
              ==> &0 < rfs_vscalar V u x /\
                  rfs_vscalar V s x <=
                  (&1 / (&1 - (s - u) * rfs_vscalar V u x) + alpha) * rfs_vscalar V u x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BN_NECK_SCALAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))) THEN
  EXISTS_TAC `eps2:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `u:real`; `e:real^3->A`; `s:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `rfs_neck (rfs_vtop V u,rfs_vatlas V u) (rfs_vmetric V u) eps (x:A) e`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_neck V eps (x:A) u e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar V u (x:A)` ASSUME_TAC THENL
   [REWRITE_TAC[P2BN_RFS_VSCALAR] THEN ASM_MESON_TAC[P2BN_NECK_CENTRE_FACTS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?y0. y0 IN rfs_neck_dom eps /\ (e:real^3->A) y0 = x` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar V u (x:A)` THEN
  ABBREV_TAC `sg = (s - u) * Q` THEN
  SUBGOAL_THEN `--(&1) < sg /\ sg <= &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `--inv Q * Q` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_LNEG; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
        ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "ns" (MP_TAC o SPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `u:real`; `&1`; `e:real^3->A`; `sg:real`; `y0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u + sg / Q = s` SUBST1_TAC THENL
   [EXPAND_TAC "sg" THEN
    SUBGOAL_THEN `~(Q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `rfs_vscalar V s (x:A) / Q <= &1 / (&1 - sg) + alpha` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]]);;

(* MT p. 291: R is almost nonincreasing backwards along strong necks.       *)

let P2HN_NECK_R_BACKWARD = prove
 (`!alpha. &0 < alpha /\ alpha <= &1 / &4
     ==> ?eps2. &0 < eps2 /\
           !V eps (x:A) s0 s1.
              p2c_regular_view V /\ eps <= eps2 /\ s0 <= s1 /\
              (!s. s0 <= s /\ s <= s1 ==> ?e. rfs_strong_neck V eps x s e)
              ==> !s. s0 <= s /\ s <= s1
                      ==> rfs_vscalar V s x <= (&1 + alpha) * rfs_vscalar V s1 x`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `alpha:real` P2HN_NECK_R_STEP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  EXISTS_TAC `eps2:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `s0:real`; `s1:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. s0 <= u /\ u <= s1
        ==> &0 < rfs_vscalar V u (x:A) /\
            !s. u - inv(rfs_vscalar V u x) < s /\ s <= u
                ==> rfs_vscalar V s x <=
                    (&1 / (&1 - (s - u) * rfs_vscalar V u x) + alpha) * rfs_vscalar V u x`
  (LABEL_TAC "one") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `e:real^3->A`) THEN
    SUBGOAL_THEN `&0 < rfs_vscalar V u (x:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_strong_neck V eps (x:A) u e` THEN
      REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR] THEN
      MESON_TAC[P2BN_NECK_CENTRE_FACTS];
      ASM_REWRITE_TAC[]] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "st" (MP_TAC o SPECL
     [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `eps:real`; `x:A`; `u:real`; `e:real^3->A`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `M = rfs_vscalar V s1 (x:A)` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN USE_THEN "one" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k u. s0 <= u /\ u <= s1 /\ rfs_vscalar V u (x:A) <= M /\ u - s0 <= &k / (&2 * M)
          ==> !s. s0 <= s /\ s <= u ==> rfs_vscalar V s x <= (&1 + alpha) * M`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real` THEN REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN STRIP_TAC THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s:real = u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_LE_ADDR] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "one" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `Ru = rfs_vscalar V u (x:A)` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nu")) THEN
    ABBREV_TAC `u' = u - inv(&2 * Ru)` THEN
    SUBGOAL_THEN `&0 < inv(&2 * Ru) /\ inv(&2 * Ru) < inv Ru /\ inv(&2 * M) <= inv(&2 * Ru)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u' - u) * Ru = --(&1 / &2)` ASSUME_TAC THENL
     [EXPAND_TAC "u'" THEN
      SUBGOAL_THEN `~(Ru = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `u' <= s` THENL
     [USE_THEN "nu" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `--(&1 / &2) <= (s - u) * Ru /\ (s - u) * Ru <= &0` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            rand(concl th) = `--(&1 / &2)`)) THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 / (&1 - (s - u) * Ru) <= &1` ASSUME_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 + alpha) * Ru` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&1 / (&1 - (s - u) * Ru) + alpha) * Ru` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REMOVE_THEN "ih" (MP_TAC o SPEC `u':real`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        USE_THEN "nu" (MP_TAC o SPEC `u':real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&1 / (&1 - --(&1 / &2)) + alpha) * Ru` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * Ru` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        UNDISCH_TAC `u - s0 <= &(SUC k) / (&2 * M)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_SUC; real_div; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
        EXPAND_TAC "u'" THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `&2 * M * (s1 - s0)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `s1:real`] o check (fun th ->
    is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:num`)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `&0 < &2 * M` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The lower bound along one strong neck: in the first half of the backward *)
(* window, R(x,s) >= R(x,u) / 4 (alpha = 1/12 in P2BN_NECK_SCALAR).          *)

let P2HN_NECK_R_LOW = prove
 (`?eps2. &0 < eps2 /\
     !V eps (x:A) u e s.
        p2c_regular_view V /\ rfs_strong_neck V eps x u e /\ eps <= eps2 /\
        u - inv(&2 * rfs_vscalar V u x) <= s /\ s <= u
        ==> rfs_vscalar V u x <= &4 * rfs_vscalar V s x`,
  MP_TAC(SPEC `&1 / &12` P2BN_NECK_SCALAR) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))) THEN
  EXISTS_TAC `eps2:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `u:real`; `e:real^3->A`; `s:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `rfs_neck (rfs_vtop V u,rfs_vatlas V u) (rfs_vmetric V u) eps (x:A) e`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_neck V eps (x:A) u e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar V u (x:A)` ASSUME_TAC THENL
   [REWRITE_TAC[P2BN_RFS_VSCALAR] THEN ASM_MESON_TAC[P2BN_NECK_CENTRE_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y0. y0 IN rfs_neck_dom eps /\ (e:real^3->A) y0 = x` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar V u (x:A)` THEN
  ABBREV_TAC `sg = (s - u) * Q` THEN
  SUBGOAL_THEN `--(&1 / &2) <= sg /\ sg <= &0 /\ u + sg / Q = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--inv(&2 * Q) * Q` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `--inv(&2 * Q) * Q = --(&1 / &2)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(Q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  USE_THEN "ns" (MP_TAC o SPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `u:real`; `&1`; `e:real^3->A`; `sg:real`; `y0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 / &3 <= &1 / (&1 - sg)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 - sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &4 <= rfs_vscalar V s (x:A) / Q` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Noncollapsing inside the backward window                                  *)
(* of a strong neck.  The 11.31 iteration feeds p2c_vblowup_back            *)
(* (P2C_THM_11_8_VIEW part 1) past the interval of the current limit, so    *)
(* kappa-noncollapsing is needed at (y,s) for s in the backward window of   *)
(* the strong neck at (y,s'), where the slice is close to the shrinking     *)
(* cylinder at time sigma = (s - s') R(y,s') rather than to the standard     *)
(* cylinder.  P2HN_QF_NONCOLL is the flat-ball volume argument of           *)
(* P2BN_NECK_NONCOLL (pc_p2b_neckbd) for a parametrization whose rescaled   *)
(* pullback is between |w|^2 and 6 |w|^2 near a point.                      *)
(* ========================================================================= *)

(* |R| <= 6 |Rm|: the statement of P2AZ_MFD_SCALAR_ABS (pc_p2a_smz),         *)
(* P2AU_MFD_SCALAR_ABS_3 (pc_p2a_flow) and P3N_SCALAR_LE_RM (pc_p3_s16end),  *)
(* proved here because those units have large closures.                      *)

let P2HN_SCALAR_ABS_LE_RM = prove
 (`!top atlas (g:A->real^3^3) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top
     ==> abs(mfd_scalar atlas g y) <= &6 * mfd_rm_norm atlas g y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `y:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                             (G:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) y IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `SND(c:(A->bool)#(A->real^3)) y`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) y =
    sum(1..dimindex(:3))
       (\j. mfd_ricci atlas g y (matrix_inv(M:real^3^3) ** basis j) (matrix_inv M ** basis j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_scalar; mfd_ricci] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B_LSCALAR_FRAME THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:3)) (\j. &2 * mfd_rm_norm atlas (g:A->real^3^3) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `matrix_inv(M:real^3^3) ** basis j`] P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`transp(M:real^3^3) ** M`; `M:real^3^3`; `j:num`; `j:num`]
                  P2B_FRAME_ORTHO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC]);;

let P2HN_QF_NONCOLL = prove
 (`!top atlas (g:A->real^3^3) D (e:real^3->A) z0 R r K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas D e /\ ball(z0,&1 / &4) SUBSET D /\
     &0 < R /\ &0 < r /\ r * sqrt R <= &5 /\
     (!y w. y IN ball(z0,&1 / &4)
            ==> w dot w <= R * (w dot (rfs_pullback atlas e g y ** w)) /\
                R * (w dot (rfs_pullback atlas e g y ** w)) <= &6 * (w dot w)) /\
     compact_in top K /\ mfd_ball (top,atlas) g (e z0) r SUBSET K
     ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g (e z0) r) v /\
             pi / &6000 * r pow 3 <= v`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `U = ball(z0:real^3,&1 / &4)` THEN
  SUBGOAL_THEN `open (U:real^3->bool) /\ (z0:real^3) IN U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (U:real^3->bool) (e:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `D:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `e'':A->real^3` o GEN_REWRITE_RULE I [mfd_param]) THEN
  SUBGOAL_THEN `&0 < sqrt R` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `rho = r * sqrt R / &20` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &20`];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(z0:real^3,rho) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the image of the flat ball lies in the ball *)
  SUBGOAL_THEN `IMAGE (e:real^3->A) (ball(z0,rho)) SUBSET
                mfd_ball (top,atlas) (g:A->real^3^3) (e z0) r`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:A). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) ((e:real^3->A) z0)
                  (sqrt((&1 + &0) / (R / &6)) * rho)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIM_PB_BALL_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                            `\x:real^3. mat 1:real^3^3`; `U:real^3->bool`;
                            `IMAGE (e:real^3->A) U`; `e'':A->real^3`] THEN
      ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; P2BN_FLAT_BALL; REAL_LE_REFL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[P2BN_PULLBACK_OPEN_UNIV; MATRIX_VECTOR_MUL_LID; REAL_ADD_RID;
                  REAL_MUL_LID] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `v:real^3`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `&6`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
      MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN
      SUBGOAL_THEN `sqrt((&1 + &0) / (R / &6)) = sqrt(&6) / sqrt R` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ADD_RID] THEN
        SUBGOAL_THEN `&1 / (R / &6) = &6 / R` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        ASM_SIMP_TAC[SQRT_DIV; REAL_POS; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      EXPAND_TAC "rho" THEN
      SUBGOAL_THEN `sqrt(&6) / sqrt R * r * sqrt R / &20 = sqrt(&6) * r / &20`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(&6) <= &3` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(&6) * r <= &3 * r` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the ball has a volume *)
  SUBGOAL_THEN
   `mfd_has_volume (top,atlas) (g:A->real^3^3)
      (mfd_ball (top,atlas) g ((e:real^3->A) z0) r)
      (mfd_volume (top,atlas) g (mfd_ball (top,atlas) g (e z0) r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN EXISTS_TAC `K:A->bool` THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_volume (top,atlas) (g:A->real^3^3)
                (mfd_ball (top,atlas) g ((e:real^3->A) z0) r)` THEN
  ASM_REWRITE_TAC[] THEN
  (* the volume of the image of the flat ball *)
  SUBGOAL_THEN
   `mfd_has_volume (top,atlas) (g:A->real^3^3) (IMAGE (e:real^3->A) (ball(z0,rho)))
      (mfd_volume (top,atlas) g (IMAGE e (ball(z0,rho))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN EXISTS_TAC `K:A->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `U:real^3->bool`] THEN
      ASM_REWRITE_TAC[OPEN_BALL];
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
                                      REAL_MUL_LID; P2BN_PULLBACK_OPEN_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `w:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `&6`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
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
  SUBGOAL_THEN `rho pow 3 = (r * sR / &20) pow 3` SUBST1_TAC THENL
   [EXPAND_TAC "rho" THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sR pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 / &3 * pi * (r * sR / &20) pow 3 = (pi / &6000 * r pow 3) * sR pow 3 /\
    sR pow 2 * sR * mfd_volume (top,atlas) (g:A->real^3^3) (IMAGE (e:real^3->A) (ball(z0,rho))) =
    mfd_volume (top,atlas) g (IMAGE e (ball(z0,rho))) * sR pow 3`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Bounds of the shrinking-cylinder quadratic form near the unit sphere for *)
(* -1/2 <= s <= 0 (from LRG_CYL_FLOW_DOT and Cauchy-Schwarz).               *)

let P2HN_CYL_QF_NUM = prove
 (`!s (y:real^3) w.
     --(&1 / &2) <= s /\ s <= &0 /\ &3 / &4 < norm y /\ norm y < &5 / &4
     ==> &32 / &25 * (w dot w) <= w dot (cylinder_flow s y ** w) /\
         w dot (cylinder_flow s y ** w) <= &16 / &3 * (w dot w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LRG_CYL_FLOW_DOT] THEN
  ABBREV_TAC `W = (w:real^3) dot w` THEN
  ABBREV_TAC `n2 = norm(y:real^3) pow 2` THEN
  ABBREV_TAC `p = ((w:real^3) dot y) * (w dot y)` THEN
  ABBREV_TAC `c = &2 / n2` THEN
  SUBGOAL_THEN `&0 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &16 < n2 /\ n2 < &25 / &16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n2" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&9 / &16 = (&3 / &4) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&25 / &16 = (&5 / &4) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * n2 = &2 /\ &32 / &25 <= c /\ c <= &32 / &9` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    SUBGOAL_THEN `&0 < n2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p /\ p <= W * n2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
    EXPAND_TAC "W" THEN EXPAND_TAC "n2" THEN
    SUBGOAL_THEN `((w:real^3) dot y) * (w dot y) = abs(w dot y) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW2_ABS; REAL_POW_2]; ALL_TAC] THEN
    REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --s / &2 * (c * (c * (W * n2 - p)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --s / &2 * (c * (c * p))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s / &2 * (c * (c * (W * n2))) = s * c * W` ASSUME_TAC THENL
   [SUBGOAL_THEN `s / &2 * (c * (c * (W * n2))) = s / &2 * c * W * (c * n2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&32 / &25 * W <= c * W` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - s) * c <= &16 / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &32 / &9` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - s) * c) * W <= &16 / &3 * W` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Noncollapsing at (x,s) for s in the first half of the backward window of *)
(* a strong eps-neck at (x,t), in a compact slice: the slice at             *)
(* s = t + sigma/R, -1/2 < sigma <= 0, is close to the shrinking cylinder at *)
(* sigma (rfs_close_fam), whose quadratic form is between 32/25 and 16/3 on *)
(* the core (P2HN_CYL_QF_NUM); |Rm| <= r^(-2) at (x,s) and R(x,s) >=         *)
(* (5/12) R (P2BN_NECK_SCALAR) give r R^(1/2) <= 5.                          *)

let P2HN_EVNECK_NONCOLL = prove
 (`?eps3. &0 < eps3 /\
     !V eps (x:A) t e s r.
        p2c_regular_view V /\ rfs_strong_neck V eps x t e /\ eps <= eps3 /\
        t - inv(&2 * rfs_vscalar V t x) < s /\ s <= t /\
        compact_space (rfs_vtop V s) /\
        &0 < r /\ mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) x <= inv(r pow 2)
        ==> ?v. mfd_has_volume (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s)
                               (rfs_vball V s x r) v /\
                pi / &6000 * r pow 3 <= v`,
  MP_TAC(SPEC `&1 / &4` P2BN_NECK_SCALAR) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))) THEN
  EXISTS_TAC `min eps2 (&1 / &10)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `t:real`; `e:real^3->A`; `s:real`; `r:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps (x:A) e /\
    rfs_close_fam (rfs_kreg eps) eps {s | --(&1) < s /\ s <= &0}
      (rfs_neck_dom eps) cylinder_flow
      (\s y. rfs_vscalar V t x %%
             rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                          (rfs_vmetric V (t + s / rfs_vscalar V t x)) y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_neck V eps (x:A) t e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `R = rfs_vscalar V t (x:A)` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
    ASM_MESON_TAC[P2BN_NECK_CENTRE_FACTS];
    ALL_TAC] THEN
  ABBREV_TAC `sg = (s - t) * R` THEN
  SUBGOAL_THEN `--(&1 / &2) < sg /\ sg <= &0 /\ t + sg / R = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `--inv(&2 * R) * R` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `--inv(&2 * R) * R = --(&1 / &2)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(R = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) < sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `t:real`; `&1`; `e:real^3->A`; `sg:real`]
   P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?z0. z0 IN sphere(vec 0:real^3,&1) /\ (e:real^3->A) z0 = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps (x:A) e` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z0:real^3) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` P2BN_NECK_CORE_DOM) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `z0:real^3`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ball(z0:real^3,&1 / &4) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  (* closeness at sigma *)
  UNDISCH_TAC
   `rfs_close_fam (rfs_kreg eps) eps {s | --(&1) < s /\ s <= &0}
      (rfs_neck_dom eps) cylinder_flow
      (\s y. R %% rfs_pullback (rfs_vatlas V (t + s / R)) (e:real^3->A)
                               (rfs_vmetric V (t + s / R)) y)` THEN
  REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `sg:real`))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "cl") THEN
  (* quadratic form bounds *)
  SUBGOAL_THEN
   `!y w. y IN ball(z0:real^3,&1 / &4)
          ==> w dot w <= R * (w dot (rfs_pullback (rfs_vatlas V s) (e:real^3->A)
                                                 (rfs_vmetric V s) y ** w)) /\
              R * (w dot (rfs_pullback (rfs_vatlas V s) e (rfs_vmetric V s) y ** w))
              <= &6 * (w dot w)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ &3 / &4 < norm y /\ norm y < &5 / &4`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN ball(z0,&1 / &4)` THEN REWRITE_TAC[IN_BALL] THEN
      UNDISCH_TAC `norm(z0:real^3) = &1` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_kreg eps`; `rfs_neck_dom eps`; `cylinder_flow sg`;
                   `\y. R %% rfs_pullback (rfs_vatlas V s) (e:real^3->A) (rfs_vmetric V s) y`;
                   `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
        EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow sg)
             (\y. R %% rfs_pullback (rfs_vatlas V s) (e:real^3->A) (rfs_vmetric V s) y) y)
      <= &1 / &10`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
       [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN USE_THEN "cl" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
         [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]]];
      ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    ABBREV_TAC `dd = sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow sg)
                   (\y. R %% rfs_pullback (rfs_vatlas V s) (e:real^3->A)
                                          (rfs_vmetric V s) y) y)` THEN
    ABBREV_TAC `A0 = (w:real^3) dot (cylinder_flow sg y ** w)` THEN
    MP_TAC(SPECL [`sg:real`; `y:real^3`; `w:real^3`] P2HN_CYL_QF_NUM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= (w:real^3) dot w` ASSUME_TAC THENL
     [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `dd * A0 <= &1 / &10 * A0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scale bound r R^(1/2) <= 5 *)
  SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop V s)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` (MP_TAC o CONJUNCT1 o CONJUNCT2)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&5 / &12 * R <= rfs_vscalar V s (x:A)` ASSUME_TAC THENL
   [USE_THEN "ns" (MP_TAC o SPECL
     [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `eps:real`; `x:A`; `t:real`; `&1`; `e:real^3->A`; `sg:real`; `z0:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN
      MATCH_MP_TAC(SET_RULE `!a s t. (a:real^3) IN s /\ s SUBSET t ==> a IN t`) THEN
      EXISTS_TAC `ball(z0:real^3,&1 / &4)` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 / &3 <= &1 / (&1 - sg)` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &1 - sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&5 / &12 <= rfs_vscalar V s (x:A) / R` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r * sqrt R <= &5` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) s`; `x:A`] P2HN_SCALAR_ABS_LE_RM) THEN
    ASM_REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN DISCH_TAC THEN
    SUBGOAL_THEN `R <= &72 / &5 * inv(r pow 2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `r pow 2 * R <= &72 / &5` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r pow 2 * (&72 / &5 * inv(r pow 2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> a * (&72 / &5 * inv a) = &72 / &5`;
                     REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH_EQ; REAL_POS; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the flat-ball argument *)
  REWRITE_TAC[P2HN_VBALL_EQ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:real^3->A) z0 = x`)) THEN
  MATCH_MP_TAC P2HN_QF_NONCOLL THEN
  MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `R:real`;
                        `topspace(rfs_vtop (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)`] THEN
  ASM_REWRITE_TAC[P2AP_BALL_SUBSET; GSYM compact_space]);;

(* ========================================================================= *)
(* The iteration of MT p. 291 without a                                      *)
(* diagonal subsequence.  A property that holds eventually along a further   *)
(* subsequence of every subsequence holds eventually (P2HN_EVENTUALLY_BY_    *)
(* SUBSEQ); so p2c_vblowup_back for the sequence itself follows from the    *)
(* step 'limit on (-T0,0] along some subsequence ==> backward hypothesis     *)
(* up to T0 + c' (P2HN_BACK_ITERATE).                                       *)
(* ========================================================================= *)

(* A property that holds frequently holds along a subsequence.               *)

let P2HN_FREQ_SUBSEQ = prove
 (`!P:num->bool. (!N. ?n. N <= n /\ P n) ==> ?sub. p3_subseq sub /\ !n. P (sub n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(prove_recursive_functions_exist num_RECURSION
   `(f:num->num) 0 = (@n. P n) /\ (!k. f (SUC k) = @n. SUC(f k) <= n /\ P n)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!k. (P:num->bool) (f k) /\ f k < f (SUC k)` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[];
        SUBGOAL_THEN `?n. SUC((f:num->num) k) <= n /\ (P:num->bool) n` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?n. SUC((f:num->num) k) <= n /\ (P:num->bool) n` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SELECT_RULE) THEN ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `f:num->num` THEN ASM_REWRITE_TAC[p3_subseq] THEN
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Eventually along a further subsequence of every subsequence implies      *)
(* eventually.                                                               *)

let P2HN_EVENTUALLY_BY_SUBSEQ = prove
 (`!P:num->bool.
     (!sub. p3_subseq sub
            ==> ?sub'. p3_subseq sub' /\ ?N. !n. N <= n ==> P (sub (sub' n)))
     ==> ?N. !n. N <= n ==> P n`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `?N. !n. N <= n ==> (P:num->bool) n` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `\n. ~((P:num->bool) n)` P2HN_FREQ_SUBSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sub:num->num` o check (fun th ->
    is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub':num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)))) THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* The backward hypothesis of P2C_THM_11_8_VIEW by subsequences.             *)

let P2HN_VBACK_BY_SUBSEQ = prove
 (`!kappa r0 (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) x t Tb.
     (!sub. p3_subseq sub
            ==> ?sub'. p3_subseq sub' /\
                       p2c_vblowup_back (kappa,r0) (\n. V (sub (sub' n)))
                         (\n. x (sub (sub' n))) (\n. t (sub (sub' n))) Tb)
     ==> p2c_vblowup_back (kappa,r0) V x t Tb`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2c_vblowup_back] THEN
  X_GEN_TAC `A:real` THEN
  MATCH_MP_TAC(BETA_RULE(ISPEC
   `\n. rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) n)
          (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
          (t n - Tb * inv(rfs_vscalar (V n) (t n) (x n))) (t n) /\
        !s y. t n - Tb * inv(rfs_vscalar (V n) (t n) (x n)) < s /\ s <= t n /\
              y IN rfs_vball (V n) (t n) (x n)
                     (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
              ==> p3_noncoll_at (V n) kappa r0 y s`
   P2HN_EVENTUALLY_BY_SUBSEQ)) THEN
  X_GEN_TAC `sub:num->num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sub:num->num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub':num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sub':num->num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A:real` o GEN_REWRITE_RULE I [p2c_vblowup_back]) THEN
  REWRITE_TAC[]);;

(* p3_subseq is closed under composition (written here to keep the unit's   *)
(* closure small).                                                           *)

let P2HN_SUBSEQ_O = prove
 (`!sub sub'. p3_subseq sub /\ p3_subseq sub' ==> p3_subseq (sub o sub')`,
  REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[]);;

let P2HN_SUBSEQ_ID = prove
 (`p3_subseq (\n:num. n)`,
  REWRITE_TAC[p3_subseq]);;

(* The iteration: a base step for backward times below c, and the step      *)
(* from T0 >= c to T0 + c along a further subsequence, give the backward    *)
(* hypothesis for every backward time along the sequence itself.            *)

let P2HN_BACK_ITERATE = prove
 (`!kappa r0 (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) x t c.
     &0 < c /\
     (!sub Tb. p3_subseq sub /\ Tb < c
               ==> p2c_vblowup_back (kappa,r0) (\n. V (sub n)) (\n. x (sub n))
                                    (\n. t (sub n)) Tb) /\
     (!sub T0. p3_subseq sub /\ c <= T0 /\
               (!Tb. Tb < T0
                     ==> p2c_vblowup_back (kappa,r0) (\n. V (sub n)) (\n. x (sub n))
                                          (\n. t (sub n)) Tb)
               ==> ?sub'. p3_subseq sub' /\
                          !Tb. Tb < T0 + c
                               ==> p2c_vblowup_back (kappa,r0) (\n. V (sub (sub' n)))
                                     (\n. x (sub (sub' n))) (\n. t (sub (sub' n))) Tb)
     ==> !Tb. p2c_vblowup_back (kappa,r0) V x t Tb`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "base")
    (LABEL_TAC "step"))) THEN
  SUBGOAL_THEN
   `!k sub Tb. p3_subseq sub /\ Tb < c + &k * c
               ==> p2c_vblowup_back (kappa,r0)
                     (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (sub n))
                     (\n. (x:num->A) (sub n)) (\n. (t:num->real) (sub n)) Tb`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`sub:num->num`; `Tb:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL
     [`kappa:real`; `r0:real`;
      `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) ((sub:num->num) n)`;
      `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`;
      `Tb:real`]
     P2HN_VBACK_BY_SUBSEQ)) THEN
    X_GEN_TAC `sub2:num->num` THEN DISCH_TAC THEN
    USE_THEN "step" (MP_TAC o SPECL [`(sub:num->num) o (sub2:num->num)`; `c + &k * c`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P2HN_SUBSEQ_O] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        X_GEN_TAC `Tb':real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`(sub:num->num) o (sub2:num->num)`; `Tb':real`]) THEN
        ASM_SIMP_TAC[P2HN_SUBSEQ_O]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sub3:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sub3:num->num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Tb:real`) THEN REWRITE_TAC[o_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `Tb < c + &(SUC k) * c` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `Tb:real` THEN
  MP_TAC(SPEC `Tb / c` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `\n:num. n`; `Tb:real`]) THEN
  REWRITE_TAC[P2HN_SUBSEQ_ID; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `Tb <= &k * c` MP_TAC THENL
   [UNDISCH_TAC `Tb / c <= &k` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* One backward step at a single time s'.                                   *)
(* An open set B of the slice at s' all of whose points are centres of     *)
(* strong eps-necks with R <= K persists on (s' - 1/K, s'] (union of the    *)
(* neck images, P2BN_PERSISTS_COVER), and its points are noncollapsed at    *)
(* the times (s' - 1/(2K), s') (P2HN_EVNECK_NONCOLL) and at s' itself        *)
(* (P2BN_NECK_NONCOLL).  This is the form in which the iteration of MT      *)
(* p. 291 extends the backward hypothesis p2c_vblowup_back.                  *)
(* ========================================================================= *)

let P2HN_NECK_WINDOW_EXTEND = prove
 (`?eps3. &0 < eps3 /\
     !V eps (B:A->bool) s' K r0.
        p2c_regular_view V /\ &0 < eps /\ eps <= eps3 /\ &0 < K /\
        open_in (rfs_vtop V s') B /\ ~(B = {}) /\
        (!y. y IN B ==> (?e. rfs_strong_neck V eps y s' e) /\ rfs_vscalar V s' y <= K) /\
        (!s. s < s' ==> compact_space (rfs_vtop V s))
        ==> rfs_persists V B (s' - inv K) s' /\
            !s y. s' - inv(&2 * K) < s /\ s <= s' /\ y IN B
                  ==> p3_noncoll_at V (pi / &6000) r0 y s`,
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "enc"))
    (INST_TYPE [`:A`,`:A`] P2HN_EVNECK_NONCOLL) THEN
  X_CHOOSE_THEN `eps4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_NONCOLL) THEN
  EXISTS_TAC `min eps3 (min eps4 (&1 / &4))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `B:A->bool`; `s':real`; `K:real`; `r0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BN_PERSISTS_COVER THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> s - x < s`) THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`N:A->bool`; `s' - inv K`; `s':real`; `s:real`] o
        check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 4)) THEN
      ASM_REWRITE_TAC[mfd_diffeo] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real^3->A`) ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `rfs_strong_neck V eps (w:A) s' e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2BN_NECK_CENTRE_FACTS]; ALL_TAC] THEN
    REWRITE_TAC[P2BN_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s' - inv K` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= x ==> s - x <= s - y`) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN
    ASM_MESON_TAC[P2BN_NECK_CENTRE_FACTS; P2BN_RFS_VSCALAR];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real^3->A`) ASSUME_TAC) THEN
  REWRITE_TAC[p3_noncoll_at] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop V s',rfs_vatlas V s') (rfs_vmetric V s') eps (y:A) e`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_neck V eps (y:A) s' e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop V s)` ASSUME_TAC THENL
   [ASM_CASES_TAC `s = s':real` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `eps:real`;
                     `y:A`; `e:real^3->A`] P2BN_NECK_CENTRE_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop V s) (IMAGE (e:real^3->A) (rfs_neck_dom eps))` MP_TAC THENL
     [UNDISCH_TAC `rfs_strong_neck V eps (y:A) s' e` THEN
      REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th)))) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s' - inv(&2 * K)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= x ==> s - x <= s - y`) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      SUBGOAL_THEN `&0 < rfs_vscalar V s' (y:A)` ASSUME_TAC THENL
       [REWRITE_TAC[P2BN_RFS_VSCALAR] THEN ASM_MESON_TAC[P2BN_NECK_CENTRE_FACTS];
        ASM_REAL_ARITH_TAC];
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `eps:real`;
                     `y:A`; `e:real^3->A`] P2BN_NECK_CENTRE_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) /\
                smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                riemannian_metric (rfs_vatlas V s) (rfs_vmetric V s)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "hausdorff_space"))
          (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists"))
          (concl th)))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) (y:A) <= inv(r pow 2)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> s - x < s`) THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; P2HN_VBALL_EQ; MFD_CENTRE_IN_BALL];
    ALL_TAC] THEN
  ASM_CASES_TAC `s = s':real` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "nc" (MP_TAC o SPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                                   `eps:real`; `y:A`; `e:real^3->A`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[P2HN_VBALL_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pi / &750 * r pow 3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar V s' (y:A)` ASSUME_TAC THENL
   [REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `eps:real`;
                   `y:A`; `e:real^3->A`] P2BN_NECK_CENTRE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "enc" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`eps:real`; `s':real`; `e:real^3->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s' - inv(&2 * K)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= x ==> s - x <= s - y`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Tools on the limit side of MT Claim                                      *)
(* 11.35.  Uniform containment of approximant balls in the images of limit  *)
(* balls (P2HN_LIM_BALL_IN_UNIF: LIM_BALL_IN of pc_lim_close made uniform    *)
(* in the centre and the time), one compact set for the limit balls of      *)
(* the slices of a limit flow on [a',0] (P2HN_LIM_BALLS_COMPACT), and the     *)
(* exclusion of the alternatives other than necks: compact components       *)
(* (P2HN_NO_COMPONENT_NEAR) and caps (P2HN_NO_CAP_NEAR).                    *)
(* ========================================================================= *)

(* Uniform form of LIM_BALL_IN (pc_lim_close; same proof).                    *)

let P2HN_LIM_BALL_IN_UNIF = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi a b K Kc r r'.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k s. a <= s /\ s <= b ==> hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     real_interval[a,b] SUBSET J /\
     (!s. a <= s /\ s <= b
          ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)) /\
     K SUBSET topspace top /\ compact_in top Kc /\
     (!y s. y IN K /\ a <= s /\ s <= b
            ==> mfd_ball (top,atlas) (g s) y (r' + &1) SUBSET Kc) /\
     &0 < r /\ r < r'
     ==> ?k0. !k y s z. k0 <= k /\ y IN K /\ a <= s /\ s <= b /\
                        z IN mfd_ball (rfs_vtop (V k) (t k + s / Q k),
                                       rfs_vatlas (V k) (t k + s / Q k))
                                      (rfs_vmetric (V k) (t k + s / Q k))
                                      (phi k y) (r * inv(sqrt(Q k)))
                        ==> z IN IMAGE (phi k) (mfd_ball (top,atlas) (g s) y r' INTER W k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  ABBREV_TAC `rho0 = (r + r') / &2` THEN
  SUBGOAL_THEN `&0 < rho0 /\ r < rho0 /\ rho0 < r'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / rho0 /\ r / rho0 < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `dd = &1 - (r / rho0) pow 2` THEN
  SUBGOAL_THEN `&0 < dd /\ dd < &1 /\ sqrt(&1 - dd) = r / rho0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 < (r / rho0) pow 2 /\ (r / rho0) pow 2 < &1` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_1_LT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `a:real`; `b:real`; `Kc:B->bool`;
                 `dd:real`] LIM_QF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s':real` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:B`; `s:real`; `z:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s) /\
                mfd_complete (top,atlas) (g s) /\ (y:B) IN topspace top /\
                hausdorff_space (rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                  (t k + s / Q k))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real`)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) (LABEL_TAC "qf")))) THEN
  SUBGOAL_THEN `hausdorff_space (VT:A topology)` ASSUME_TAC THENL
   [EXPAND_TAC "VT" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `U = mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y (r' + &1)` THEN
  SUBGOAL_THEN `open_in top (U:B->bool) /\ U SUBSET Kc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `Kc:B->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) SUBSET W(k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) k`;
                 `VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                 `U:B->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Bl = mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y r'` THEN
  SUBGOAL_THEN `compact_in top (top closure_of (Bl:B->bool)) /\ top closure_of Bl SUBSET U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `y:B`; `Bl:B->bool`; `r':real`]
                    P2BL_BOUNDED_CLOSURE_COMPACT) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Bl" THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y r'` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
        ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN EXPAND_TAC "Bl" THEN
        REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
        EXPAND_TAC "U" THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[REAL_ARITH `x <= r' ==> x < r' + &1`]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `VT:A topology`;
                 `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `U:B->bool`;
                 `IMAGE ((phi:num->B->A) k) U`; `(phi:num->B->A) k`; `psi:A->B`;
                 `y:B`; `y:B`; `r':real`; `r' - rho0`; `(Q:num->real) k`; `dd:real`;
                 `r * inv(sqrt((Q:num->real) k))`; `z:A`] LIM_PB_BALL_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`w:B`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "qf" (MP_TAC o SPECL [`w:B`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_ARITH `r' - (r' - rho0) = rho0`] THEN
      SUBGOAL_THEN `&0 < sqrt((Q:num->real) k)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < q ==> q * r * inv q = r`;
                   REAL_FIELD `&0 < rho0 ==> r / rho0 * rho0 = r`; REAL_LE_REFL]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(z:A) IN IMAGE ((phi:num->B->A) k)
                 (mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y r')` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Bl:B->bool) SUBSET W(k:num)` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:B->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (Bl:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN EXPAND_TAC "Bl" THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    SET_TAC[]]);;

(* Nonnegativity of g(v,v).                                                   *)

let P2HN_METRIC_QF_POS_LE = prove
 (`!top atlas (g:A->real^N^N) x v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &0 <= v dot (g x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]);;

(* Balls of the slices of a limit flow on [a',0], about points of a compact *)
(* set and of a fixed radius, lie in one compact set: the metrics on        *)
(* [a',0] are uniformly equivalent to g(0) (bounded curvature,             *)
(* RFA_UPTO_QFORM_EQUIV) and g(0) is complete.                              *)

let P2HN_LIM_BALLS_COMPACT = prove
 (`!(top:B topology) atlas (g:real->B->real^3^3) a a' K0 Km xl rho.
     connected_space top /\
     rfs_flow_upto (top,atlas) a (&0) g /\ a < a' /\ a' <= &0 /\
     mfd_complete (top,atlas) (g (&0)) /\ xl IN topspace top /\
     (!s y. a < s /\ s <= &0 /\ y IN topspace top ==> mfd_rm_norm atlas (g s) y <= Km) /\
     compact_in top K0 /\ &0 < rho
     ==> ?Kc. compact_in top Kc /\
              !y s. y IN K0 /\ a' <= s /\ s <= &0
                    ==> mfd_ball (top,atlas) (g s) y rho SUBSET Kc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `!s. a < s /\ s <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s = &0` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Kr = &2 * max Km (&0)` THEN
  SUBGOAL_THEN `&0 <= Kr` ASSUME_TAC THENL [EXPAND_TAC "Kr" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = exp(&2 * Kr * (&0 - a))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  (* the metric comparison *)
  SUBGOAL_THEN
   `!s z v. a' <= s /\ s <= &0 /\ z IN topspace top
            ==> v dot ((g:real->B->real^3^3) (&0) z ** v) <= c * (v dot (g s z ** v))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
     [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [EXPAND_TAC "c" THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2HN_METRIC_QF_POS_LE THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a:real`; `&0`;
                   `g:real->B->real^3^3`; `z:B`; `s:real`; `Kr:real`; `v:real^3`]
                  RFA_UPTO_QFORM_EQUIV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s'`; `z:B`; `v:real^3`] P2AP_MFD_RICCI_ABS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      EXPAND_TAC "Kr" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= max k (&0)`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2HN_METRIC_QF_POS_LE THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2HN_METRIC_QF_POS_LE THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a distance bound on K0 at time 0 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `xl:B`; `K0:B->bool`] LIM_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) xl (D + sqrt c * rho)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `s:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `w:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top /\ (w:B) IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET];
      ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (xl:B) w /\
                mfd_joinable (top,atlas) xl y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_CONNECTED]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl y +
              mfd_dist (top,atlas) (g (&0)) y w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a < D /\ b <= c ==> a + b <= D + c`) THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt c * mfd_dist (top,atlas) ((g:real->B->real^3^3) s) y w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFAH_DIST_COMPARE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]]);;

(* MT Claim 11.35, the compact alternatives: a C-component or an eps-round  *)
(* component through a point x lies in a ball of radius D R(x)^(-1/2)       *)
(* (CANON_CCOMP_IN_BALL, CANON_ROUND_IN_BALL, pc_canon_diam); if that ball  *)
(* lies in the image of a connected noncompact limit, the component is a    *)
(* compact component inside the image: impossible.                          *)

let P2HN_NO_COMPONENT_NEAR = prove
 (`?eps0. &0 < eps0 /\
     !(topl:B topology) (atlasl:((B->bool)#(B->real^3))->bool) (topA:A topology)
      atlasA (gA:A->real^3^3) W phi psi C eps U x r.
       hausdorff_space topl /\ connected_space topl /\ ~compact_space topl /\
       hausdorff_space topA /\ smooth_manifold_atlas topA atlasA /\
       riemannian_metric atlasA gA /\
       mfd_diffeo topl atlasl W topA atlasA (IMAGE phi W) phi psi /\
       mfd_ball (topA,atlasA) gA x r SUBSET IMAGE phi W /\ x IN U /\
       ((&1 <= C /\ rfs_c_component (topA,atlasA) gA C U /\
         C * sqrt C * inv(sqrt(mfd_scalar atlasA gA x)) < r) \/
        (&0 < eps /\ eps <= eps0 /\ rfs_round_component (topA,atlasA) gA eps U /\
         &12 * inv(sqrt(mfd_scalar atlasA gA x)) < r))
       ==> F`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rd"))
    (INST_TYPE [`:A`,`:A`] CANON_ROUND_IN_BALL) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC P2HN_COMPONENT_IN_IMAGE_ABSURD THEN
    MAP_EVERY EXISTS_TAC [`topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`;
      `topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`; `W:B->bool`;
      `phi:B->A`; `psi:A->B`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[rfs_c_component]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[rfs_c_component]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (topA,atlasA) (gA:A->real^3^3) x r` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                   `gA:A->real^3^3`; `C:real`; `U:A->bool`; `x:A`; `z:A`]
                  CANON_CCOMP_IN_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2HN_COMPONENT_IN_IMAGE_ABSURD THEN
    MAP_EVERY EXISTS_TAC [`topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`;
      `topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`; `W:B->bool`;
      `phi:B->A`; `psi:A->B`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[rfs_round_component]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[rfs_round_component]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (topA,atlasA) (gA:A->real^3^3) x r` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "rd" (MP_TAC o SPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`;
                   `gA:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`; `z:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* MT Claim 11.35, caps: a (C,eps)-cap in an approximant that is close to a *)
(* complete connected nonnegatively curved limit with two ends would give a *)
(* (2C, K eps)-cap in the limit (P2C_REQ_CAP_FIX); there is none            *)
(* (P2C_REQ_TWO_ENDS_NO_CAP).  The splitting theorem of MT Claim 11.34 is   *)
(* not used.                                                                 *)

let P2HN_NO_CAP_NEAR = prove
 (`!u:A->bool w:B->bool.
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?K eps0. &1 <= K /\ &0 < eps0 /\
           !C eps Kr. &1 < C /\ &0 < eps /\ K * eps <= eps0
             ==> ?delta. &0 < delta /\
                   !topA atlasA (gA:A->real^3^3) (topl:B topology) atlasl gl x U Y psi psi'.
                      hausdorff_space topA /\ smooth_manifold_atlas topA atlasA /\
                      riemannian_metric atlasA gA /\
                      hausdorff_space topl /\ smooth_manifold_atlas topl atlasl /\
                      riemannian_metric atlasl gl /\ mfd_complete (topl,atlasl) gl /\
                      connected_space topl /\
                      (!y u v. y IN topspace topl /\ ~collinear {vec 0,u,v}
                               ==> &0 <= mfd_sectional atlasl gl y u v) /\
                      (?K0 U1 U2.
                         compact_in topl K0 /\
                         U1 IN connected_components_of
                                 (subtopology topl (topspace topl DIFF K0)) /\
                         U2 IN connected_components_of
                                 (subtopology topl (topspace topl DIFF K0)) /\
                         ~(U1 = U2) /\ ~compact_in topl (topl closure_of U1) /\
                         ~compact_in topl (topl closure_of U2)) /\
                      rfs_cap (topA,atlasA) gA C eps U Y /\ x IN Y /\
                      (!y l. y IN U /\ l <= 2
                             ==> lrm_deriv_norm2 l
                                   (metric_local atlasA (chart_at atlasA y)
                                      (\z. mfd_scalar atlasA gA x %% gA z))
                                   (SND(chart_at atlasA y) y) <= Kr) /\
                      mfd_diffeo topA atlasA U topl atlasl (IMAGE psi U) psi psi' /\
                      rfs_mclose (rfs_kreg delta) delta atlasA U
                        (\y. mfd_scalar atlasA gA x %% gA y)
                        (\y. mfd_scalar atlasA gA x %%
                             mfd_pullback_metric atlasA atlasl psi gl y)
                      ==> F`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_CAP_FIX_STATEMENT; P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `Kf:real` (X_CHOOSE_THEN `epsf:real` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `epst:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`Kf:real`; `min epsf epst`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `Kr:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`C:real`; `eps:real`; `&2 * C`; `Kf * eps`; `Kr:real`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_mclose")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "fix" (MP_TAC o SPECL
   [`topA:A topology`; `atlasA:((A->bool)#(A->real^3))->bool`; `gA:A->real^3^3`;
    `topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`; `gl:B->real^3^3`;
    `x:A`; `U:A->bool`; `Y:A->bool`; `psi:A->B`; `psi':B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':B->bool` (X_CHOOSE_THEN `Y':B->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&2 * C`; `Kf * eps`; `topl:B topology`;
                                `atlasl:((B->bool)#(B->real^3))->bool`; `gl:B->real^3^3`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_space")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    DISCH_THEN(MP_TAC o SPECL [`U':B->bool`; `Y':B->bool`]) THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The bound Q0 of MT p. 291 as a property of the sequence.  p3_flow_limit   *)
(* gives p3_flow_limit_on on (-Tl,0] (P2HN_FLOW_LIMIT_ON, in pc_p2c_bugq); R *)
(* of the approximants is close to R of the limit on compact sets            *)
(* (P2HN_SCALAR_FROM_LIMIT, from LCK_CURVATURE_STABILITY); a global |Rm|     *)
(* bound Km of the time-0 limit slice gives R <= (6 Km + 1) Q_n on every     *)
(* A-ball for n large (P2HN_Q0_FROM_LIMIT).                                  *)
(* ========================================================================= *)

(* P2HN_FLOW_LIMIT_ON (p3_flow_limit gives p3_flow_limit_on on (-Tl,0]) is   *)
(* in pc_p2c_bugq, loaded above.                                             *)

(* Scalar curvature of the approximants from the limit, on a compact set at *)
(* one time of the limit: R(phi_k y)/Q_k is within alpha of R_limit(y).     *)

let P2HN_SCALAR_FROM_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s K K0 alpha.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     s IN J /\ riemannian_metric atlas (g s) /\ compact_in top K /\ &0 < alpha /\
     (!y. y IN K ==> lrm_deriv_norm2 0 (metric_local atlas (chart_at atlas y) (g s))
                                       (SND(chart_at atlas y) y) <= K0 pow 2)
     ==> ?k0. !k y. k0 <= k /\ y IN K
                    ==> y IN W k /\
                        abs(rfs_vscalar (V k) (t k + s / Q k) (phi k y) / Q k -
                            mfd_scalar atlas (g s) y) <= alpha`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K0:real`; `alpha:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`; `K:B->bool`; `2`; `eta pow 2`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_INTERVAL_SING; SING_SUBSET; REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `y:B`] THEN STRIP_TAC THEN
  REMOVE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o SPEC `s:real`) (MP_TAC o SPECL [`s:real`; `y:B`]))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  SUBGOAL_THEN `(y:B) IN topspace top /\ (y:B) IN W(k:num)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (VT:A topology) VA /\ riemannian_metric VA (VG:A->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["VT"; "VA"; "VG"] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) k y` THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (W(k:num))
                   (VT:A topology) (VA:((A->bool)#(A->real^3))->bool)
                   (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER W(k:num))` THEN
  SUBGOAL_THEN `open (S:real^3->bool) /\ S SUBSET IMAGE (SND c) (FST(c:(B->bool)#(B->real^3))) /\
                SND c (y:B) IN S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                     `W(k:num):B->bool`] MFDR_RESTRICT_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR];
      SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (S:real^3->bool) (chart_inv (c:(B->bool)#(B->real^3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                  MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) S SUBSET W(k:num)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (VT:A topology) (VA:((A->bool)#(A->real^3))->bool) S ((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `W(k:num):B->bool`; `IMAGE ((phi:num->B->A) k) (W k)`;
                          `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "st" (MP_TAC o SPECL
   [`S:real^3->bool`; `metric_local atlas c ((g:real->B->real^3^3) s)`;
    `\z. (Q:num->real) k %% rfs_pullback (VA:((A->bool)#(A->real^3))->bool) ((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3))) (VG:A->real^3^3) z`;
    `SND(c:(B->bool)#(B->real^3)) y`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `riemannian_metric atlas ((g:real->B->real^3^3) s)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `VT:A topology` THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      EXPAND_TAC "c" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `lscalar (metric_local atlas c ((g:real->B->real^3^3) s))
                        (SND(c:(B->bool)#(B->real^3)) y) = mfd_scalar atlas (g s) y`
  SUBST1_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC[mfd_scalar]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (\z. (Q:num->real) k %% rfs_pullback (VA:((A->bool)#(A->real^3))->bool) ((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3))) (VG:A->real^3^3) z)
            (SND(c:(B->bool)#(B->real^3)) y) =
    rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) k) (t k + s / Q k) (phi k y) / Q k`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`;
                   `S:real^3->bool`; `(phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3))`; `(Q:num->real) k`;
                   `SND(c:(B->bool)#(B->real^3)) y`] P2B9_PARAM_LSCALAR_SCALED) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXPAND_TAC ["VA"; "VG"] THEN REWRITE_TAC[P2BN_RFS_VSCALAR; o_THM] THEN
    ASM_SIMP_TAC[];
    REAL_ARITH_TAC]);;

(* MT p. 291, Q0: a global bound Km of |Rm| on the time-0 slice of a limit  *)
(* bounds R by (6 Km + 1) Q_n on the balls B(x_n, t_n, A Q_n^(-1/2)) for   *)
(* n large, for every A: the sequence form of Q0 (inherited by              *)
(* subsequences).                                                            *)

let P2HN_Q0_FROM_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q (top:B topology) atlas g xl Tl Km.
     p3_flow_limit V x t Q (top,atlas) g xl Tl /\
     (!n s. ~(topspace(rfs_vtop (V n) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k))) /\
     (!k. Q k = rfs_vscalar (V k) (t k) (x k)) /\
     riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0)) /\
     (!y. y IN topspace top ==> mfd_rm_norm atlas (g (&0)) y <= Km)
     ==> !A. &0 < A
             ==> ?N. !n y. N <= n /\
                           y IN rfs_vball (V n) (t n) (x n)
                                  (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                           ==> rfs_vscalar (V n) (t n) y <=
                               (&6 * Km + &1) * rfs_vscalar (V n) (t n) (x n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_FLOW_LIMIT_ON) THEN
  REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_TAC `phi:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `(&0) IN {s | --Tl < s /\ s <= &0}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. t k + &0 / Q k = (t:num->real) k` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `{s | --Tl < s /\ s <= &0}`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `&0`; `xl:B`; `A:real`; `A + &1`] LIM_BALL_IN) THEN
  ASM_REWRITE_TAC[REAL_ARITH `A < A + &1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "in")) THEN
  ABBREV_TAC `Kb = mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) xl (A + &1)` THEN
  SUBGOAL_THEN `compact_in top (Kb:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `Kb:B->bool`] P2HN_RMD2_COMPACT_KR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Kr:real`) THEN
  MP_TAC(ISPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `{s | --Tl < s /\ s <= &0}`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `&0`; `Kb:B->bool`; `max (&1) Kr`; `&1`]
   P2HN_SCALAR_FROM_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kr:real` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`y:B`; `0`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `Kr:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[LE_0];
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `max (&1) Kr` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "sc")) THEN
  EXISTS_TAC `MAX k0 k1` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
  REMOVE_THEN "in" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
  ASM_REWRITE_TAC[GSYM P2HN_VBALL_EQ] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z:B) IN Kb` ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN UNDISCH_TAC
     `(z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl (A + &1)` THEN
    REWRITE_TAC[mfd_ball; mfd_cball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REMOVE_THEN "sc" (MP_TAC o SPECL [`n:num`; `z:B`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z <= &6 * Km` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `z:B`] P2HN_SCALAR_ABS_LE_RM) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Km:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) n) (t n) (x n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) n) (t n) ((phi:num->B->A) n z) /
                rfs_vscalar (V n) (t n) (x n) <= &6 * Km + &1` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]]);;

(* ========================================================================= *)
(* The backward hypothesis of P2C_THM_11_8_VIEW from strong necks.  If, for  *)
(* every A, eventually all points of the A-ball about x_n at a time s'_n =   *)
(* t_n - t'/Q_n are centres of strong eps-necks with R <= Kb Q_n (and the    *)
(* ball persists on [s'_n, t_n] with noncollapsing there), then              *)
(* p2c_vblowup_back holds up to t' + 1/(2 Kb).                               *)
(* ========================================================================= *)

(* Persistence on a smaller interval. *)

let P2HN_PERSISTS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a a' b b'.
     rfs_persists V W a b /\ a <= a' /\ b' <= b ==> rfs_persists V W a' b'`,
  REWRITE_TAC[P2BN_PERSISTS_ALT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Persistence on two adjacent intervals. *)

let P2HN_PERSISTS_UNION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b c.
     rfs_persists V W a b /\ rfs_persists V W b c ==> rfs_persists V W a c`,
  REWRITE_TAC[P2BN_PERSISTS_ALT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ab") (LABEL_TAC "bc")) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= b` THENL
   [USE_THEN "ab" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    USE_THEN "bc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The base step: strong necks at t_n with R <= Kb Q_n on every A-ball for  *)
(* n large give p2c_vblowup_back for backward times Tb <= 1/(2 Kb).          *)

let P2HN_BACK_BASE = prove
 (`?eps3. &0 < eps3 /\
     !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      (x:num->A) t eps Kb r0 Tb.
        (!n. p2c_regular_view (V n)) /\ &0 < eps /\ eps <= eps3 /\ &0 < Kb /\
        Tb <= inv(&2 * Kb) /\
        (!n s. s < t n ==> compact_space (rfs_vtop (V n) s)) /\
        (!n. x n IN topspace(rfs_vtop (V n) (t n)) /\ &0 < rfs_vscalar (V n) (t n) (x n)) /\
        (!A. &0 < A
             ==> ?N. !n y. N <= n /\
                           y IN rfs_vball (V n) (t n) (x n)
                                  (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                           ==> (?e. rfs_strong_neck (V n) eps y (t n) e) /\
                               rfs_vscalar (V n) (t n) y <=
                               Kb * rfs_vscalar (V n) (t n) (x n))
        ==> p2c_vblowup_back (pi / &6000,r0) V x t Tb`,
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_WINDOW_EXTEND) THEN
  EXISTS_TAC `eps3:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2c_vblowup_back] THEN X_GEN_TAC `A:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max A (&1)` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th))) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ABBREV_TAC `Qn = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  SUBGOAL_THEN `&0 < Qn` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `B = rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n) ((x:num->A) n)
                    (max A (&1) * inv(sqrt Qn))` THEN
  SUBGOAL_THEN `&0 < Kb * Qn` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n)) /\
    smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n)) /\
    riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o el 0 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view] o
      SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_regular_view"))
            (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `(t:num->real) n`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s < (t:num->real) n
                   ==> compact_space (rfs_vtop ((V:num->(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "ext" (MP_TAC o SPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
    `eps:real`; `B:A->bool`; `(t:num->real) n`; `Kb * Qn`; `r0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[P2HN_VBALL_EQ] THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[P2HN_VBALL_EQ] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      REMOVE_THEN "N" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `t n - Tb * inv Qn >= (t:num->real) n - inv(&2 * (Kb * Qn))` ASSUME_TAC THENL
   [REWRITE_TAC[real_ge; REAL_ARITH `a - x <= a - y <=> y <= x`] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `inv(&2) * inv Kb * inv Qn = inv(&2 * Kb) * inv Qn` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * (Kb * Qn)) <= inv(Kb * Qn)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2HN_PERSIST_OPEN_SUB THEN EXISTS_TAC `B:A->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2HN_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(t:num->real) n - inv(Kb * Qn)`; `(t:num->real) n`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "B" THEN REWRITE_TAC[P2HN_VBALL_EQ] THEN
      MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[P2HN_VBALL_EQ] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)
                     (A * inv(sqrt Qn))` THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[P2HN_VBALL_EQ] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (y:A) IN s ==> y IN t`) THEN
      MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]]]);;

(* The extension step: p2c_vblowup_back up to T' > t' and, eventually on    *)
(* every A-ball, strong eps-necks at s'_n = t_n - t'/Q_n with R <= Kb Q_n   *)
(* give p2c_vblowup_back up to t' + 1/(2 Kb).                                *)

let P2HN_BACK_EXTEND = prove
 (`?eps3. &0 < eps3 /\
     !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      (x:num->A) t eps Kb r0 t' T' Tb.
        (!n. p2c_regular_view (V n)) /\ &0 < eps /\ eps <= eps3 /\ &0 < Kb /\
        &0 <= t' /\ t' < T' /\ Tb <= t' + inv(&2 * Kb) /\
        (!n s. s < t n ==> compact_space (rfs_vtop (V n) s)) /\
        (!n. x n IN topspace(rfs_vtop (V n) (t n)) /\ &0 < rfs_vscalar (V n) (t n) (x n)) /\
        p2c_vblowup_back (pi / &6000,r0) V x t T' /\
        (!A. &0 < A
             ==> ?N. !n y. N <= n /\
                           y IN rfs_vball (V n) (t n) (x n)
                                  (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                           ==> (?e. rfs_strong_neck (V n) eps y
                                      (t n - t' * inv(rfs_vscalar (V n) (t n) (x n))) e) /\
                               rfs_vscalar (V n)
                                 (t n - t' * inv(rfs_vscalar (V n) (t n) (x n))) y <=
                               Kb * rfs_vscalar (V n) (t n) (x n))
        ==> p2c_vblowup_back (pi / &6000,r0) V x t Tb`,
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_WINDOW_EXTEND) THEN
  EXISTS_TAC `eps3:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2c_vblowup_back] THEN X_GEN_TAC `A:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max A (&1)` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th))) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max A (&1)` o GEN_REWRITE_RULE I [p2c_vblowup_back] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) =
      "p2c_vblowup_back")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
  ABBREV_TAC `Qn = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  SUBGOAL_THEN `&0 < Qn` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `B = rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n) ((x:num->A) n)
                    (max A (&1) * inv(sqrt Qn))` THEN
  ABBREV_TAC `s' = (t:num->real) n - t' * inv Qn` THEN
  SUBGOAL_THEN `&0 < Kb * Qn` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc1")) THEN
  SUBGOAL_THEN `t n - T' * inv Qn < s' /\ s' <= (t:num->real) n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN
    SUBGOAL_THEN `t' * inv Qn < T' * inv Qn /\ &0 <= t' * inv Qn` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s') B`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) B
                  (t n - T' * inv Qn) (t n)` THEN
    REWRITE_TAC[P2BN_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `s':real`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN B` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))
         (rfs_vatlas (V n) (t n)) /\
      riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o el 0 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view] o
        check (fun th -> can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "p2c_regular_view")) (concl th) && not(is_forall(concl th)))) THEN
      DISCH_THEN(MP_TAC o SPEC `(t:num->real) n`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; SIMP_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[P2HN_VBALL_EQ] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s < s' ==> compact_space (rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ext" (MP_TAC o SPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
    `eps:real`; `B:A->bool`; `s':real`; `Kb * Qn`; `r0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      REMOVE_THEN "N2" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc2")) THEN
  SUBGOAL_THEN `s' - inv(&2 * (Kb * Qn)) <= (t:num->real) n - Tb * inv Qn` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN
    MATCH_MP_TAC(REAL_ARITH `Tb * q <= t' * q + i ==> t - t' * q - i <= t - Tb * q`) THEN
    SUBGOAL_THEN `inv(&2 * (Kb * Qn)) = inv(&2 * Kb) * inv Qn` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * (Kb * Qn)) <= inv(Kb * Qn)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) B
                  (t n - Tb * inv Qn) (t n)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_PERSISTS_UNION THEN EXISTS_TAC `s':real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2HN_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`s' - inv(Kb * Qn)`; `s':real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2HN_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(t:num->real) n - T' * inv Qn`; `(t:num->real) n`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)
                  (A * inv(sqrt Qn)) SUBSET B`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[P2HN_VBALL_EQ] THEN
    MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2HN_PERSIST_OPEN_SUB THEN EXISTS_TAC `B:A->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2HN_VBALL_EQ] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    FIRST_X_ASSUM(MP_TAC o el 0 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view] o
      check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "p2c_regular_view")) (concl th) && not(is_forall(concl th)))) THEN
    DISCH_THEN(MP_TAC o SPEC `(t:num->real) n`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN B` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s' < s` THENL
   [USE_THEN "nc1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "nc2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* MT Claim 11.35 at one point of one                                       *)
(* approximant slice.  A strong (C,eps)-canonical neighbourhood of a point  *)
(* y whose ball B(y, r) lies in the image of a connected, complete,         *)
(* nonnegatively curved limit with two ends, and is close to it there, is   *)
(* a strong eps-neck: caps (P2HN_NO_CAP_NEAR) and compact components         *)
(* (P2HN_NO_COMPONENT_NEAR) are excluded.                                   *)
(* ========================================================================= *)

let P2HN_CANON_AT_CASES = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t.
     p3_canon_at V C eps x t
     ==> (?e. rfs_strong_neck V eps x t e) \/
         (?U Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps U Y /\ x IN Y) \/
         (?U. x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U) \/
         (?U. x IN U /\
              rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)`,
  REWRITE_TAC[FORALL_PAIR_THM; p3_canon_at; rfs_strong_canonical; rfs_vtop; rfs_vatlas;
              rfs_vmetric] THEN
  MESON_TAC[]);;

(* Two ends imply noncompactness. *)

let P2HN_TWO_ENDS_NONCOMPACT = prove
 (`!(top:B topology).
     (?K U1 U2. compact_in top K /\
                U1 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                U2 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                ~(U1 = U2) /\ ~compact_in top (top closure_of U1) /\
                ~compact_in top (top closure_of U2))
     ==> ~compact_space top`,
  GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~compact_in top (top closure_of (U1:B->bool))` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]);;

(* R > 0 on the core of a cap. *)

let P2HN_CAP_SCALAR_POS = prove
 (`!top atlas (g:A->real^3^3) C eps U Y x.
     rfs_cap (top,atlas) g C eps U Y /\ x IN Y ==> &0 < mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_cap]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

let P2HN_CANON_IS_NECK = prove
 (`!u:A->bool w:B->bool.
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?K eps0. &1 <= K /\ &0 < eps0 /\
           !C eps Kr. &1 < C /\ &0 < eps /\ K * eps <= eps0
             ==> ?delta. &0 < delta /\
                   !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3))
                    tau y (topl:B topology) atlasl gl W phi psi r.
                      hausdorff_space (rfs_vtop V tau) /\
                      smooth_manifold_atlas (rfs_vtop V tau) (rfs_vatlas V tau) /\
                      riemannian_metric (rfs_vatlas V tau) (rfs_vmetric V tau) /\
                      p3_canon_at V C eps y tau /\
                      hausdorff_space topl /\ smooth_manifold_atlas topl atlasl /\
                      riemannian_metric atlasl gl /\ mfd_complete (topl,atlasl) gl /\
                      connected_space topl /\
                      (!z u v. z IN topspace topl /\ ~collinear {vec 0,u,v}
                               ==> &0 <= mfd_sectional atlasl gl z u v) /\
                      (?K0 U1 U2.
                         compact_in topl K0 /\
                         U1 IN connected_components_of
                                 (subtopology topl (topspace topl DIFF K0)) /\
                         U2 IN connected_components_of
                                 (subtopology topl (topspace topl DIFF K0)) /\
                         ~(U1 = U2) /\ ~compact_in topl (topl closure_of U1) /\
                         ~compact_in topl (topl closure_of U2)) /\
                      mfd_diffeo topl atlasl W (rfs_vtop V tau) (rfs_vatlas V tau)
                                 (IMAGE phi W) phi psi /\
                      mfd_ball (rfs_vtop V tau,rfs_vatlas V tau) (rfs_vmetric V tau) y r
                      SUBSET IMAGE phi W /\
                      max C (max (C * sqrt C) (&12)) *
                      inv(sqrt(mfd_scalar (rfs_vatlas V tau) (rfs_vmetric V tau) y)) < r /\
                      (!z l. z IN mfd_ball (rfs_vtop V tau,rfs_vatlas V tau)
                                           (rfs_vmetric V tau) y r /\ l <= 2
                             ==> lrm_deriv_norm2 l
                                   (metric_local (rfs_vatlas V tau)
                                      (chart_at (rfs_vatlas V tau) z)
                                      (\w. mfd_scalar (rfs_vatlas V tau) (rfs_vmetric V tau) y %%
                                           rfs_vmetric V tau w))
                                   (SND(chart_at (rfs_vatlas V tau) z) z) <= Kr) /\
                      (?d. d < delta pow 2 /\
                           !z. z IN mfd_ball (rfs_vtop V tau,rfs_vatlas V tau)
                                             (rfs_vmetric V tau) y r
                               ==> lck_dist2 (rfs_kreg delta)
                                     (metric_local (rfs_vatlas V tau)
                                        (chart_at (rfs_vatlas V tau) z)
                                        (\w. mfd_scalar (rfs_vatlas V tau) (rfs_vmetric V tau) y %%
                                             rfs_vmetric V tau w))
                                     (metric_local (rfs_vatlas V tau)
                                        (chart_at (rfs_vatlas V tau) z)
                                        (\w. mfd_scalar (rfs_vatlas V tau) (rfs_vmetric V tau) y %%
                                             mfd_pullback_metric (rfs_vatlas V tau) atlasl psi gl w))
                                     (SND(chart_at (rfs_vatlas V tau) z) z) <= d)
                      ==> ?e. rfs_strong_neck V eps y tau e`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_NO_CAP_NEAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `epsc:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cap"))))) THEN
  X_CHOOSE_THEN `epsr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "comp"))
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_NO_COMPONENT_NEAR) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `min epsc (min epsr (&1 / &40))`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `Kr:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  USE_THEN "cap" (MP_TAC o SPECL [`C:real`; `eps:real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `tau:real`; `y:A`; `topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`;
    `gl:B->real^3^3`; `W:B->bool`; `phi:B->A`; `psi:A->B`; `r:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~compact_space (topl:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_TWO_ENDS_NONCOMPACT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eps <= K * eps` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps <= epsr /\ eps <= &1 / &40` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `VT = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tau` THEN
  ABBREV_TAC `VA = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tau` THEN
  ABBREV_TAC `VG = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tau` THEN
  ABBREV_TAC `Ry = mfd_scalar (VA:((A->bool)#(A->real^3))->bool) (VG:A->real^3^3) y` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP P2HN_CANON_AT_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 MP_TAC (DISJ_CASES_THEN2 MP_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET mfd_ball (VT,VA) (VG:A->real^3^3) y r` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`;
                     `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `y:A`; `z:A`]
                    CANON_CAP_IN_BALL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C * inv(sqrt Ry)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `max C (max (C * sqrt C) (&12)) * inv(sqrt Ry)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      EXPAND_TAC "Ry" THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC P2HN_CAP_SCALAR_POS THEN
      MAP_EVERY EXISTS_TAC [`VT:A topology`; `C:real`; `eps:real`; `U:A->bool`;
                            `Y:A->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPECL
     [`VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`;
      `topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`; `gl:B->real^3^3`;
      `y:A`; `U:A->bool`; `Y:A->bool`; `psi:A->B`; `phi:B->A`]) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (phi:B->A) W`; `W:B->bool`] THEN
      CONJ_TAC THENL [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `rfs_cap (VT,VA) (VG:A->real^3^3) C eps U Y` THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_cap]) THEN
        SIMP_TAC[];
        ASM SET_TAC[]];
      REWRITE_TAC[rfs_mclose] THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "comp" (MP_TAC o SPECL
     [`topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`; `VT:A topology`;
      `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `W:B->bool`; `phi:B->A`;
      `psi:A->B`; `C:real`; `eps:real`; `U:A->bool`; `y:A`; `r:real`]) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `max C (max (C * sqrt C) (&12)) * inv(sqrt Ry)` THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
    EXPAND_TAC "Ry" THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(ISPECL [`VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`;
                   `C:real`; `U:A->bool`; `y:A`] P2B_C_COMPONENT_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:A` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "comp" (MP_TAC o SPECL
     [`topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`; `VT:A topology`;
      `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `W:B->bool`; `phi:B->A`;
      `psi:A->B`; `C:real`; `eps:real`; `U:A->bool`; `y:A`; `r:real`]) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `max C (max (C * sqrt C) (&12)) * inv(sqrt Ry)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
    EXPAND_TAC "Ry" THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC P2BL_ROUND_SCALAR_POS THEN
    MAP_EVERY EXISTS_TAC [`VT:A topology`; `eps:real`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The derivative bound Kr of                                               *)
(* P2C_REQ_CAP_FIX for the approximants in MT Claim 11.35, from Shi's       *)
(* estimate for views (VSHI_SHI_VIEW_CC, pc_vshi) and the normalization     *)
(* VSHI_KR_BOUND.                                                            *)
(* ========================================================================= *)

let P2HN_POW_RHO_LE = prove
 (`!rho l. &0 < rho /\ rho <= &1 /\ l <= 2 ==> &1 <= rho pow (l + 2) * inv(rho pow 4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
  SUBGOAL_THEN `rho pow 4 = rho pow (l + 2) * rho pow (2 - l)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC]);;

let P2HN_KR_FROM_RM = prove
 (`!Km Rr th rho.
     &0 < Km /\ &0 < Rr /\ &0 < th /\ &0 < rho /\ rho <= &1
     ==> ?Kr. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) y a b q.
                p2c_regular_view V /\ compact_space (rfs_vtop V b) /\
                y IN topspace(rfs_vtop V b) /\ &0 < q /\ a < b /\ th <= q * (b - a) /\
                rfs_persists V (rfs_vball V b y ((&4 * Rr) * inv(sqrt q))) a b /\
                (!s z. a < s /\ s <= b /\ z IN rfs_vball V b y ((&4 * Rr) * inv(sqrt q))
                       ==> p3_vrm V s z <= Km * q) /\
                rho * q <= rfs_vscalar V b y
                ==> !z l. z IN rfs_vball V b y (Rr * inv(sqrt q)) /\ l <= 2
                          ==> lrm_deriv_norm2 l
                                (metric_local (rfs_vatlas V b) (chart_at (rfs_vatlas V b) z)
                                   (\w. rfs_vscalar V b y %% rfs_vmetric V b w))
                                (SND(chart_at (rfs_vatlas V b) z) z) <= Kr`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `Km:real`; `Rr:real`; `th:real`] (INST_TYPE [`:A`,`:A`] VSHI_SHI_VIEW_CC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
  MP_TAC(ISPECL [`1`; `Km:real`; `Rr:real`; `th:real`] (INST_TYPE [`:A`,`:A`] VSHI_SHI_VIEW_CC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C1:real`) THEN
  MP_TAC(ISPECL [`2`; `Km:real`; `Rr:real`; `th:real`] (INST_TYPE [`:A`,`:A`] VSHI_SHI_VIEW_CC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C2:real`) THEN
  ABBREV_TAC `CA = max (&0) (max C0 (max C1 C2)) * inv(rho pow 4)` THEN
  EXISTS_TAC `CA:real` THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `y:A`; `a:real`; `b:real`; `q:real`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`z:A`; `l:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= CA` ASSUME_TAC THENL
   [EXPAND_TAC "CA" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) /\
    smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
    riemannian_metric (rfs_vatlas V b) (rfs_vmetric V (b:real))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `b:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace(rfs_vtop V b)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN rfs_vball V b y (Rr * inv(sqrt q))` THEN
    REWRITE_TAC[P2HN_VBALL_EQ] THEN MP_TAC(ISPECL
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
      `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b`; `y:A`; `Rr * inv(sqrt q)`] P2AP_BALL_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b)
                  (rfs_vtop V b closure_of rfs_vball V b (y:A) ((&4 * Rr) * inv(sqrt q)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_vderiv2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) 0 b (z:A) <= C0 * q pow (0 + 2) /\
                p3_vderiv2 V 1 b z <= C1 * q pow (1 + 2) /\
                p3_vderiv2 V 2 b z <= C2 * q pow (2 + 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:A`; `a:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l'. l' <= 2 ==> p3_vderiv2 V l' b (z:A) <=
                     max (&0) (max C0 (max C1 C2)) * q pow (l' + 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l':num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= q pow (l' + 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `l' = 0 \/ l' = 1 \/ l' = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    W(fun (asl,w) -> let lw = lhand w in
        FIRST_ASSUM(fun th -> if is_binary "real_le" (concl th) && lhand(concl th) = lw
                              then MP_TAC th else NO_TAC)) THEN
    MATCH_MP_TAC(REAL_ARITH `c * w <= m * w ==> x <= c * w ==> x <= m * w`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Ry = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b (y:A)` THEN
  SUBGOAL_THEN `&0 < rho * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                 `rho * q`; `Ry / (rho * q)`; `CA:real`; `z:A`] VSHI_KR_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    X_GEN_TAC `l':num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max (&0) (max C0 (max C1 C2)) * q pow (l' + 2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM p3_vderiv2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "CA" THEN REWRITE_TAC[REAL_POW_MUL] THEN
      SUBGOAL_THEN `(max (&0) (max C0 (max C1 C2)) * inv(rho pow 4)) *
                    (rho pow (l' + 2) * q pow (l' + 2)) =
                    (max (&0) (max C0 (max C1 C2)) * q pow (l' + 2)) *
                    (rho pow (l' + 2) * inv(rho pow 4))` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC P2HN_POW_RHO_LE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= c ==> y <= c`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `w:A` THEN REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < rho * q` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* MT Claim 11.35 in one approximant.                                       *)
(* ========================================================================= *)

(* |Rm| at the centre of a strong neck along its backward window.           *)

let P2HN_RM_IN_WINDOW = prove
 (`?K1. &0 < K1 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      eps z u e s K.
        p2c_regular_view V /\ &0 < eps /\ eps <= &1 / &4 /\ rfs_strong_neck V eps z u e /\
        rfs_vscalar V u z <= K /\ u - inv K < s /\ s <= u
        ==> p3_vrm V s z <= K1 * K`,
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm"))
    (INST_TYPE [`:A`,`:A`] P2BN_EVNECK_RM) THEN
  EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `z:A`; `u:real`; `e:real^3->A`; `s:real`; `K:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rfs_vscalar V u (z:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_neck V eps (z:A) u e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR] THEN
    MESON_TAC[P2BN_NECK_CENTRE_FACTS];
    ALL_TAC] THEN
  ABBREV_TAC `R = rfs_vscalar V u (z:A)` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `sg = (s - u) * R` THEN
  SUBGOAL_THEN `--(&1) < sg /\ sg <= &0 /\ u + sg / R = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `--inv R * R` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_LNEG; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
        ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN
        SUBGOAL_THEN `inv K <= inv R` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(R = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `z:A`; `u:real`; `&1`; `e:real^3->A`; `sg:real`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "rm" (MP_TAC o SPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `z:A`; `u:real`; `&1`; `e:real^3->A`; `sg:real`]) THEN
  ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN
  REWRITE_TAC[p3_vrm] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* The sequence and limit packages of MT Claim 11.35.  p2hn_spk: regular    *)
(* views, compact slices before t n, (C1,eps1)-canonical neighbourhoods     *)
(* above Lc, Q n = R(x n, t n) -> infinity, on every A-ball at t n for n    *)
(* large strong eps1-necks with R <= Qb Q n (Q0), and on every A-ball for n *)
(* large Q n <= D1 R with D1 depending on A (no splitting theorem is used,  *)
(* so no uniform lower bound).  p2hn_lpack: a limit on (-T0,0] with an      *)
(* explicit exhaustion W and maps phi, complete with nonnegative curvature, *)
(* |Rm| bounded on [a,0], connected, with two ends.                         *)

let p2hn_spk = new_definition
 `p2hn_spk (C1:real,eps1:real,Lc:real,Qb:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) (t:num->real) <=>
    &0 < Qb /\
    (!n. p2c_regular_view (V n) /\ x n IN topspace(rfs_vtop (V n) (t n)) /\
         &0 < rfs_vscalar (V n) (t n) (x n)) /\
    (!n s. s < t n ==> compact_space (rfs_vtop (V n) s)) /\
    (!n y s. s <= t n /\ y IN topspace(rfs_vtop (V n) s) /\ Lc <= rfs_vscalar (V n) s y
             ==> p3_canon_at (V n) C1 eps1 y s) /\
    (!B. ?N. !n. N <= n ==> B < rfs_vscalar (V n) (t n) (x n)) /\
    (!A. &0 < A
         ==> ?N. !n y. N <= n /\
                       y IN rfs_vball (V n) (t n) (x n)
                              (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                       ==> (?e. rfs_strong_neck (V n) eps1 y (t n) e) /\
                           rfs_vscalar (V n) (t n) y <= Qb * rfs_vscalar (V n) (t n) (x n)) /\
    (!A. &0 < A
         ==> ?D1 N. &0 < D1 /\
                    !n y. N <= n /\
                          y IN rfs_vball (V n) (t n) (x n)
                                 (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                          ==> rfs_vscalar (V n) (t n) (x n) <= D1 * rfs_vscalar (V n) (t n) y)`;;

let p2hn_lpack = new_definition
 `p2hn_lpack (T0:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) (t:num->real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B)
    (W:num->B->bool) (phi:num->B->A) <=>
    &0 < T0 /\
    p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) {s | --T0 < s /\ s <= &0}
                        (top,atlas) g xl W phi /\
    (!a. --T0 < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
    (!s. --T0 < s /\ s <= &0
         ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
             (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                      ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
    (!a. --T0 < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                ==> mfd_rm_norm atlas (g s) y <= K) /\
    connected_space top /\
    (?K0 U1 U2. compact_in top K0 /\
                U1 IN connected_components_of (subtopology top (topspace top DIFF K0)) /\
                U2 IN connected_components_of (subtopology top (topspace top DIFF K0)) /\
                ~(U1 = U2) /\ ~compact_in top (top closure_of U1) /\
                ~compact_in top (top closure_of U2))`;;

let P2HN_SPK_SUBSEQ = prove
 (`!C1 eps1 Lc Qb (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) x t sub.
     p2hn_spk (C1,eps1,Lc,Qb) V x t /\ p3_subseq sub
     ==> p2hn_spk (C1,eps1,Lc,Qb) (\n. V (sub n)) (\n. x (sub n)) (\n. t (sub n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2hn_spk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Q") (CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "lb")))))))
    ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_MESON_TAC[p3_subseq]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `B:real` THEN USE_THEN "Q" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LE_TRANS];
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `A:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS];
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "lb" (MP_TAC o SPEC `A:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`D1:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS]]);;

(* MT Claim 11.35 at one point (y,s) of one approximant: strong eps1-necks  *)
(* at the time sj on an open set B' with R <= (5/4) Qb q, a time s in       *)
(* [sj - 1/(4 Qb q), sj), and the limit data on the ball of radius           *)
(* rr q^(-1/2) about y at time s give a strong eps1-neck at (y,s) with      *)
(* R(y,s) >= (rho/4) q.                                                       *)

let P2HN_1135_POINT = prove
 (`!u:A->bool w:B->bool.
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C1 eps1 Qb rho.
              &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\ &0 < Qb /\ &0 < rho /\ rho <= &1
              ==> ?delta rr. &0 < delta /\ &0 < rr /\
                    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3))
                     tn sj s q y B' Lc (topl:B topology) atlasl gl W phi psi d.
                       p2c_regular_view V /\
                       (!s'. s' < tn ==> compact_space (rfs_vtop V s')) /\
                       (!y' s'. s' <= tn /\ y' IN topspace(rfs_vtop V s') /\
                                Lc <= rfs_vscalar V s' y'
                                ==> p3_canon_at V C1 eps1 y' s') /\
                       &0 < q /\ Lc <= rho / &4 * q /\ s < sj /\ sj <= tn /\
                       sj - inv(&4 * Qb * q) <= s /\
                       open_in (rfs_vtop V sj) B' /\
                       (!w. w IN B'
                            ==> (?e. rfs_strong_neck V eps1 w sj e) /\
                                rfs_vscalar V sj w <= &5 / &4 * Qb * q) /\
                       y IN B' /\ rho * q <= rfs_vscalar V sj y /\
                       rfs_vball V s y ((&4 * rr) * inv(sqrt q)) SUBSET B' /\
                       rfs_vball V s y (rr * inv(sqrt q)) SUBSET IMAGE phi W /\
                       hausdorff_space topl /\ smooth_manifold_atlas topl atlasl /\
                       riemannian_metric atlasl gl /\ mfd_complete (topl,atlasl) gl /\
                       connected_space topl /\
                       (!z u v. z IN topspace topl /\ ~collinear {vec 0,u,v}
                                ==> &0 <= mfd_sectional atlasl gl z u v) /\
                       (?K0 U1 U2.
                          compact_in topl K0 /\
                          U1 IN connected_components_of
                                  (subtopology topl (topspace topl DIFF K0)) /\
                          U2 IN connected_components_of
                                  (subtopology topl (topspace topl DIFF K0)) /\
                          ~(U1 = U2) /\ ~compact_in topl (topl closure_of U1) /\
                          ~compact_in topl (topl closure_of U2)) /\
                       mfd_diffeo topl atlasl W (rfs_vtop V s) (rfs_vatlas V s)
                                  (IMAGE phi W) phi psi /\
                       d < delta pow 2 /\
                       (!z. z IN rfs_vball V s y (rr * inv(sqrt q))
                            ==> lck_dist2 (rfs_kreg delta)
                                  (metric_local (rfs_vatlas V s)
                                     (chart_at (rfs_vatlas V s) z)
                                     (\w. rfs_vscalar V s y %% rfs_vmetric V s w))
                                  (metric_local (rfs_vatlas V s)
                                     (chart_at (rfs_vatlas V s) z)
                                     (\w. rfs_vscalar V s y %%
                                          mfd_pullback_metric (rfs_vatlas V s) atlasl psi gl w))
                                  (SND(chart_at (rfs_vatlas V s) z) z) <= d)
                       ==> (?e. rfs_strong_neck V eps1 y s e) /\
                           rho / &4 * q <= rfs_vscalar V s y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_CANON_IS_NECK) THEN
  DISCH_THEN(X_CHOOSE_THEN `Kn:real` (X_CHOOSE_THEN `epsn:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cn"))))) THEN
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_WINDOW_EXTEND) THEN
  X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_R_LOW) THEN
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmw"))
    (INST_TYPE [`:A`,`:A`] P2HN_RM_IN_WINDOW) THEN
  EXISTS_TAC `min (epsn / Kn) (min eps3 (min eps2 (&1 / &4)))` THEN
  SUBGOAL_THEN `&0 < Kn` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C1:real`; `eps1:real`; `Qb:real`; `rho:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Kn * eps1 <= epsn` ASSUME_TAC THENL
   [UNDISCH_TAC `eps1 <= epsn / Kn` THEN
    SUBGOAL_THEN `&0 < Kn` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Dc = max C1 (max (C1 * sqrt C1) (&12))` THEN
  SUBGOAL_THEN `&0 < Dc` ASSUME_TAC THENL [EXPAND_TAC "Dc" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `rr = &2 * Dc * inv(sqrt(rho / &4))` THEN
  SUBGOAL_THEN `&0 < sqrt(rho / &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K1 * &5 / &4 * Qb`; `rr:real`; `inv(&8 * Qb)`; `rho / &4`]
                (INST_TYPE [`:A`,`:A`] P2HN_KR_FROM_RM)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ; REAL_ARITH `&0 < &5 / &4`;
                 REAL_ARITH `&0 < &8`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kr:real` (LABEL_TAC "kr")) THEN
  USE_THEN "cn" (MP_TAC o SPECL [`C1:real`; `eps1:real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cnd"))) THEN
  MAP_EVERY EXISTS_TAC [`delta:real`; `rr:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `tn:real`; `sj:real`; `s:real`; `q:real`; `y:A`; `B':A->bool`; `Lc:real`;
    `topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`; `gl:B->real^3^3`;
    `W:B->bool`; `phi:B->A`; `psi:A->B`; `d:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Kq = &5 / &4 * Qb * q` THEN
  SUBGOAL_THEN `&0 < Kq` ASSUME_TAC THENL
   [EXPAND_TAC "Kq" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(Qb * q) /\ inv(&4 * Qb * q) = &1 / &4 * inv(Qb * q) /\
                inv(&8 * Qb * q) = &1 / &8 * inv(Qb * q) /\
                inv Kq = &4 / &5 * inv(Qb * q)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < Qb * q` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN EXPAND_TAC "Kq" THEN
    UNDISCH_TAC `&0 < Qb * q` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* the window of the necks at sj *)
  USE_THEN "ext" (MP_TAC o SPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps1:real`; `B':A->bool`; `sj:real`; `Kq:real`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `inv(&4 * Qb * q) < inv Kq` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop V s) /\
                hausdorff_space (rfs_vtop V s) /\
                smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                riemannian_metric (rfs_vatlas V s) (rfs_vmetric V s)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop V s)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists V (B':A->bool) (sj - inv Kq) sj` THEN
      REWRITE_TAC[P2BN_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the lower bound of R(y,s) *)
  SUBGOAL_THEN `rho / &4 * q <= rfs_vscalar V s (y:A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck"))
          (concl th) && not(can (find_term (fun t -> t = `C1:real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real^3->A`) ASSUME_TAC) THEN
    USE_THEN "low" (MP_TAC o SPECL
     [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `eps1:real`; `y:A`; `sj:real`; `e:real^3->A`; `s:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&0 < rfs_vscalar V sj (y:A)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho * q` THEN
        ASM_SIMP_TAC[REAL_LT_MUL];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(&2 * Kq) <= inv(&2 * rfs_vscalar V sj (y:A))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `inv(&2 * Kq) = &1 / &2 * inv Kq` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `rho * q <= r ==> r <= &4 * b ==> rho / &4 * q <= b`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the Kr bound from Shi *)
  USE_THEN "kr" (MP_TAC o SPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `y:A`; `s - inv(&8 * Qb * q)`; `s:real`; `q:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `q * inv(Qb * q) = inv Qb /\ inv(&8 * Qb) = &1 / &8 * inv Qb`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [SUBGOAL_THEN `&0 < Qb * q` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
          CONV_TAC REAL_FIELD;
          REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2HN_PERSIST_OPEN_SUB THEN EXISTS_TAC `B':A->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2HN_PERSISTS_MONO THEN
        MAP_EVERY EXISTS_TAC [`sj - inv Kq`; `sj:real`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[P2HN_VBALL_EQ] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`s'':real`; `z':A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z':A) IN B'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z':A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck"))
            (concl th) && not(can (find_term (fun t -> t = `C1:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e':real^3->A`) ASSUME_TAC) THEN
      USE_THEN "rmw" (MP_TAC o SPECL
       [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `eps1:real`; `z':A`; `sj:real`; `e':real^3->A`; `s'':real`; `Kq:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Kq" THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "kb") THEN
  (* CANON_IS_NECK *)
  USE_THEN "cnd" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`topl:B topology`; `atlasl:((B->bool)#(B->real^3))->bool`;
    `gl:B->real^3^3`; `W:B->bool`; `phi:B->A`; `psi:A->B`; `rr * inv(sqrt q)`] THEN
  ASM_REWRITE_TAC[GSYM P2HN_VBALL_EQ; GSYM P2BN_RFS_VSCALAR] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[];
    (* Dc R^(-1/2) < rr q^(-1/2) *)
    SUBGOAL_THEN `inv(sqrt(rfs_vscalar V s (y:A))) <= inv(sqrt(rho / &4)) * inv(sqrt q)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT];
        REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `Dc * inv(sqrt(rho / &4)) * inv(sqrt q)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      EXPAND_TAC "rr" THEN
      SUBGOAL_THEN `&0 < Dc * inv(sqrt(rho / &4)) * inv(sqrt q)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT];
        REAL_ARITH_TAC]];
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* MT Claim 11.35 along the sequence, one                                   *)
(* backward step.  If, for every compact set K of the limit, eventually the *)
(* points (phi_n z, t_n + tau/Q_n) with z in K and tau in [a,0] are strong  *)
(* eps1-neck centres with R >= rho Q_n, then the same holds on              *)
(* [max(-t', a - 1/(4 Qb)), 0] with R >= rho Q_n / 4 (P2HN_1135_STEP).  The *)
(* new times are handled by the point lemma P2HN_1135_POINT applied to the  *)
(* open set B' = phi_n(O), O a ball of the time-0 limit metric containing   *)
(* the compact set Kc of the relevant balls; the points of B' are strong    *)
(* necks at the old time sj = t_n + a/Q_n with R <= (5/4) Qb Q_n, by        *)
(* P2HN_NECK_R_BACKWARD and the sequence bound R <= Qb Q_n at t_n.          *)
(* ========================================================================= *)

let P2HN_REGULAR_HAUSDORFF = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s.
     p2c_regular_view V ==> hausdorff_space (rfs_vtop V s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) s) = {}` THENL
   [ASM_REWRITE_TAC[hausdorff_space; NOT_IN_EMPTY];
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    ASM_SIMP_TAC[]]);;

let P2HN_DIFFEO_IMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W top' (atlas':((B->bool)#(B->real^M))->bool)
    W' f g O.
     mfd_diffeo top atlas W top' atlas' W' f g /\ open_in top O /\ O SUBSET W
     ==> open_in top' (IMAGE f O)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`; `W':B->bool`;
                 `f:A->B`; `g:B->A`; `O:A->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[mfd_diffeo]);;

(* A closeness threshold below 1/4 with Mk th < dl.                        *)

let P2HN_SMALL_TH = prove
 (`!Mk dl. &0 <= Mk /\ &0 < dl ==> ?th. &0 < th /\ th <= &1 / &4 /\ Mk * th < dl`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min (&1 / &4) (dl / (&2 * (Mk + &1)))` THEN
  SUBGOAL_THEN `&0 < &2 * (Mk + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dl / (&2 * (Mk + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Mk * dl / (&2 * (Mk + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Mk * dl / (&2 * (Mk + &1)) = (Mk * dl) / (&2 * (Mk + &1))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= Mk * dl` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The backward step of Claim 11.35.                                         *)

let P2HN_1135_STEP = prove
 (`!u:A->bool w:B->bool.
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C1 eps1 Lc Qb T0
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t (top:B topology) atlas g xl W phi t' a.
              &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\
              p2hn_spk (C1,eps1,Lc,Qb) V x t /\
              p2hn_lpack T0 V x t (top,atlas) g xl W phi /\
              &0 <= t' /\ t' < T0 /\ --t' <= a /\ a <= &0 /\
              (!K. compact_in top K
                   ==> ?rho N. &0 < rho /\ rho <= &1 /\
                       !n z tau. N <= n /\ z IN K /\ a <= tau /\ tau <= &0
                           ==> z IN W n /\
                               (?e. rfs_strong_neck (V n) eps1 (phi n z)
                                      (t n + tau / rfs_vscalar (V n) (t n) (x n)) e) /\
                               rho * rfs_vscalar (V n) (t n) (x n) <=
                               rfs_vscalar (V n) (t n + tau / rfs_vscalar (V n) (t n) (x n))
                                           (phi n z))
              ==> !K. compact_in top K
                      ==> ?rho N. &0 < rho /\ rho <= &1 /\
                          !n z tau. N <= n /\ z IN K /\
                                        max (--t') (a - inv(&4 * Qb)) <= tau /\ tau <= &0
                              ==> z IN W n /\
                                  (?e. rfs_strong_neck (V n) eps1 (phi n z)
                                         (t n + tau / rfs_vscalar (V n) (t n) (x n)) e) /\
                                  rho * rfs_vscalar (V n) (t n) (x n) <=
                                  rfs_vscalar (V n) (t n + tau / rfs_vscalar (V n) (t n) (x n))
                                              (phi n z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_1135_POINT) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0p:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  MP_TAC(SPEC `&1 / &4` (INST_TYPE [`:A`,`:A`] P2HN_NECK_R_BACKWARD)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2b:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bw"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] P2HN_NECK_R_LOW) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2l:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low"))) THEN
  EXISTS_TAC `min eps0p (min eps2b eps2l)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `t':real`;
    `a:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th)
    then LABEL_TAC "ih" th else failwith "ih") THEN
  X_GEN_TAC `K:B->bool` THEN DISCH_TAC THEN
  USE_THEN "ih" (MP_TAC o SPEC `K:B->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `N0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N0"))))) THEN
  (* constants from the point lemma *)
  USE_THEN "pt" (MP_TAC o SPECL [`C1:real`; `eps1:real`; `Qb:real`; `rho:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN
    SIMP_TAC[p2hn_spk];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (X_CHOOSE_THEN `rr:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ptd"))))) THEN
  (* unpack the packages *)
  UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN
  REWRITE_TAC[p2hn_spk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
    (CONJUNCTS_THEN2 (LABEL_TAC "can") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "lb"))))))) THEN
  UNDISCH_TAC `p2hn_lpack T0 V (x:num->A) t (top:B topology,atlas) g xl W phi` THEN
  REWRITE_TAC[p2hn_lpack] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "cplt")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ends"))))))) THEN
  SUBGOAL_THEN `!n s. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2HN_REGULAR_HAUSDORFF THEN
    USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "reg" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a0 = (--T0 + --t') / &2` THEN
  SUBGOAL_THEN `--T0 < a0 /\ a0 < --t'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "rmb" (MP_TAC o SPEC `a0:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Km:real` (LABEL_TAC "Km")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2c_flow_limit_with")) (concl th))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `a0:real`; `--t'`; `K:B->bool`; `Km:real`;
                 `xl:B`; `&4 * rr + &2`] P2HN_LIM_BALLS_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "cplt" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN USE_THEN "Km" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Kc"))) THEN
  (* the open set O and its compact closure Ks *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `xl:B`; `Kc:B->bool`] LIM_COMPACT_DIST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "cplt" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `O = mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D0` THEN
  ABBREV_TAC `Ks = mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D0` THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0)) /\
                mfd_complete (top,atlas) (g (&0))` STRIP_ASSUME_TAC THENL
   [USE_THEN "cplt" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Kc:B->bool) SUBSET O /\ O SUBSET Ks /\ open_in top O /\ compact_in top Ks`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O"; "Ks"] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `Kc:B->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
        ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `D0:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the inductive hypothesis on Ks *)
  USE_THEN "ih" (MP_TAC o SPEC `Ks:B->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rhos:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1"))))) THEN
  (* O maps into a ball about x n at t n *)
  SUBGOAL_THEN `!k. t k + &0 / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) (x k) = (t:num->real) k`
  ASSUME_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `{s | --T0 < s /\ s <= &0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`; `xl:B`;
    `D0:real`; `D0 + &1`] LIM_BALL_OUT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ARITH `D < D + &1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  USE_THEN "nk" (MP_TAC o SPEC `D0 + &1`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  (* uniform ball containment along the approximants *)
  MP_TAC(ISPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `{s | --T0 < s /\ s <= &0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `--t'`; `&0`;
    `K:B->bool`; `Kc:B->bool`; `&4 * rr`; `&4 * rr + &1`] P2HN_LIM_BALL_IN_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "cplt" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ARITH `(&4 * rr + &1) + &1 = &4 * rr + &2`] THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4")) THEN
  (* the closeness transfer constant and the closeness threshold th *)
  MP_TAC(SPEC `rfs_kreg delta` (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_LCK_SOURCE_FROM_LIMIT)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "src"))) THEN
  ABBREV_TAC `Mk = (&1 + &4 / rho) pow (rfs_kreg delta) * M` THEN
  SUBGOAL_THEN `&0 <= Mk` ASSUME_TAC THENL
   [EXPAND_TAC "Mk" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN
    SUBGOAL_THEN `&0 <= &4 / rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Mk:real`; `delta pow 2`] P2HN_SMALL_TH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC) THEN
  (* closeness of the approximants on Kc *)
  FIRST_ASSUM(MP_TAC o SPECL [`--t'`; `&0`; `Kc:B->bool`; `rfs_kreg delta`; `th:real`] o
    check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 5 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N5:num` (LABEL_TAC "N5")) THEN
  USE_THEN "Qinf" (MP_TAC o SPEC `&4 * Lc / rho`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N6:num` (LABEL_TAC "N6")) THEN
  MAP_EVERY EXISTS_TAC [`rho / &4`; `MAX N0 (MAX N1 (MAX N2 (MAX N3 (MAX N4 (MAX N5 N6)))))`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:B`; `tau:real`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`; REAL_MAX_LE] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN Kc` ASSUME_TAC THENL
   [USE_THEN "Kc" (MP_TAC o SPECL [`z:B`; `&0`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(z:B) IN s ==> s SUBSET t ==> z IN t`) THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `K:B->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN O /\ z IN Ks` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Kc:B->bool) SUBSET O` THEN UNDISCH_TAC `(O:B->bool) SUBSET Ks` THEN
    UNDISCH_TAC `(z:B) IN Kc` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a <= tau` THENL
   [(* times in [a,0]: the inductive hypothesis *)
    USE_THEN "N0" (MP_TAC o SPECL [`n:num`; `z:B`; `tau:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rho * Q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* times in [a - 1/(4 Qb), a): the point lemma at s from the necks at sj *)
  ABBREV_TAC `sj = (t:num->real) n + a / Q` THEN ABBREV_TAC `s = (t:num->real) n + tau / Q` THEN
  SUBGOAL_THEN `s < sj /\ sj <= (t:num->real) n /\ sj - inv(&4 * Qb * Q) <= s`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sj"; "s"] THEN
    SUBGOAL_THEN `tau / Q < a / Q /\ a / Q <= &0 /\ (a - inv(&4 * Qb)) / Q <= tau / Q /\
                  (a - inv(&4 * Qb)) / Q = a / Q - inv(&4 * Qb * Q)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < Qb /\ &0 < Q` MP_TAC THENL [ASM_REWRITE_TAC[]; CONV_TAC REAL_FIELD]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "N5" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "cl5"))) THEN
  USE_THEN "dif" (MP_TAC o SPEC `tau:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  USE_THEN "dif" (MP_TAC o SPEC `a:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `psia:A->B`) THEN
  SUBGOAL_THEN `(O:B->bool) SUBSET W(n:num)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z':B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z':B) IN Ks` ASSUME_TAC THENL
     [UNDISCH_TAC `(O:B->bool) SUBSET Ks` THEN UNDISCH_TAC `(z':B) IN O` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "N1" (MP_TAC o SPECL [`n:num`; `z':B`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `B' = IMAGE ((phi:num->B->A) n) O` THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) sj) B'` ASSUME_TAC THENL
   [EXPAND_TAC "B'" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `W(n:num):B->bool`;
      `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) sj`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) sj`;
      `IMAGE ((phi:num->B->A) n) (W n)`; `(phi:num->B->A) n`; `psia:A->B`; `O:B->bool`]
      P2HN_DIFFEO_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN W(n:num)` ASSUME_TAC THENL
   [UNDISCH_TAC `(O:B->bool) SUBSET W(n:num)` THEN UNDISCH_TAC `(z:B) IN O` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)` ASSUME_TAC THENL
   [USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN B'
        ==> (?e. rfs_strong_neck ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) eps1 w sj e) /\
            rfs_vscalar (V n) sj w <= &5 / &4 * Qb * Q`
  ASSUME_TAC THENL
   [EXPAND_TAC "B'" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `z':B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z':B) IN Ks` ASSUME_TAC THENL
     [UNDISCH_TAC `(O:B->bool) SUBSET Ks` THEN UNDISCH_TAC `(z':B) IN O` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!s''. sj <= s'' /\ s'' <= (t:num->real) n
            ==> ?e. rfs_strong_neck ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) eps1 ((phi:num->B->A) n z') s'' e`
    ASSUME_TAC THENL
     [X_GEN_TAC `s'':real` THEN STRIP_TAC THEN
      USE_THEN "N1" (MP_TAC o SPECL [`n:num`; `z':B`; `(s'' - (t:num->real) n) * Q`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `a / Q <= s'' - (t:num->real) n` MP_TAC THENL
           [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]];
          MATCH_MP_TAC(REAL_ARITH `&0 <= --x * q ==> x * q <= &0`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(t:num->real) n + ((s'' - t n) * Q) / Q = s''` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(Q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        MESON_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `sj:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "bw" (MP_TAC o SPECL
     [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
      `eps1:real`; `(phi:num->B->A) n z'`; `sj:real`; `(t:num->real) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `sj:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "N2" (MP_TAC o SPECL [`n:num`; `z':B`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "N3" (MP_TAC o SPECL [`n:num`; `(phi:num->B->A) n z'`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[P2HN_VBALL_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "N0" (MP_TAC o SPECL [`n:num`; `z:B`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `ej:real^3->A`) ASSUME_TAC) THEN
  SUBGOAL_THEN `rho / &4 * Q <= rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z)` ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) sj ((phi:num->B->A) n z) <= &5 / &4 * Qb * Q` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(phi:num->B->A) n z` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `B':A->bool`)) (concl th))) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "B'" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho * Q /\ &0 < Qb * Q` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "low" (MP_TAC o SPECL
     [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
      `eps1:real`; `(phi:num->B->A) n z`; `sj:real`; `ej:real^3->A`; `s:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `inv(&4 * Qb * Q) <= inv(&2 * rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) sj ((phi:num->B->A) n z))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rho * Q /\ &0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rho * Q` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) ((g:real->B->real^3^3) tau) z (&4 * rr + &1) SUBSET Kc` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) ((g:real->B->real^3^3) tau) z (&4 * rr + &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_BALL_MONO THEN REAL_ARITH_TAC;
      USE_THEN "Kc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) ((&4 * rr) * inv(sqrt Q)) SUBSET IMAGE (phi n) (Kc INTER W n)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; P2HN_VBALL_EQ] THEN X_GEN_TAC `z':A` THEN DISCH_TAC THEN
    USE_THEN "N4" (MP_TAC o SPECL [`n:num`; `z:B`; `tau:real`; `z':A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_ball (top,atlas) ((g:real->B->real^3^3) tau) z (&4 * rr + &1) SUBSET Kc` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) (rr * inv(sqrt Q)) SUBSET rfs_vball (V n) s (phi n z) ((&4 * rr) * inv(sqrt Q))` ASSUME_TAC THENL
   [REWRITE_TAC[P2HN_VBALL_EQ] THEN MATCH_MP_TAC RFA_MFD_BALL_MONO THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((phi:num->B->A) n z) IN topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
        can (find_term (fun t -> t = `psi:A->B`)) (concl th) &&
        not (is_forall (concl th)))) THEN
    MATCH_MP_TAC(SET_RULE `(x:A) IN s ==> s SUBSET t ==> x IN t`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s) (rfs_vatlas (V n) s) /\ riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) n z` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) tau) /\ mfd_complete (top,atlas) (g tau) /\
                (!y u v. y IN topspace top /\ ~collinear {vec 0, u, v} ==> &0 <= mfd_sectional atlas (g tau) y u v)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cplt" (MP_TAC o SPEC `tau:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv Q` ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas (\v. inv Q %% (g:real->B->real^3^3) tau v) /\
                mfd_complete (top,atlas) (\v. inv Q %% g tau v) /\
                (!y u v. y IN topspace top /\ ~collinear {vec 0, u, v}
                         ==> &0 <= mfd_sectional atlas (\v. inv Q %% g tau v) y u v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) tau`; `inv Q`] MFD_COMPLETE_SCALE) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) tau`; `inv Q`; `y:B`; `u:real^3`; `v:real^3`]
        RFA_MFD_SECTIONAL_CMUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* closeness at every point of the small ball, through the source lemma *)
  SUBGOAL_THEN
   `!z'. z' IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) (rr * inv(sqrt Q))
         ==> lck_dist2 (rfs_kreg delta)
               (metric_local (rfs_vatlas (V n) s) (chart_at (rfs_vatlas (V n) s) z')
                  (\w. rfs_vscalar (V n) s (phi n z) %% rfs_vmetric (V n) s w))
               (metric_local (rfs_vatlas (V n) s) (chart_at (rfs_vatlas (V n) s) z')
                  (\w. rfs_vscalar (V n) s (phi n z) %%
                       mfd_pullback_metric (rfs_vatlas (V n) s) atlas psi
                         (\v. inv Q %% (g:real->B->real^3^3) tau v) w))
               (SND (chart_at (rfs_vatlas (V n) s) z') z') <= Mk * th`
  ASSUME_TAC THENL
   [X_GEN_TAC `z':A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z':A) IN IMAGE ((phi:num->B->A) n) (Kc INTER W n)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) = false &&
        can (find_term ((=) `Kc:B->bool`)) (concl th) &&
        can (find_term ((=) `rr:real`)) (concl th) &&
        not (can (find_term ((=) `&4 * rr + &1`)) (concl th)))) THEN
      UNDISCH_TAC `(z':A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) (rr * inv(sqrt Q))` THEN
      FIRST_ASSUM(MP_TAC o check (fun th ->
        can (find_term ((=) `rr * inv(sqrt Q)`)) (concl th) &&
        can (find_term ((=) `(&4 * rr) * inv(sqrt Q)`)) (concl th))) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(psi:A->B) z' = w` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `w:B` o el 4 o CONJUNCTS o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
        can (find_term (fun t -> t = `psi:A->B`)) (concl th) && not (is_forall (concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "src" (MP_TAC o SPECL
     [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) tau`;
      `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s`;
      `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s`;
      `W(n:num):B->bool`; `(phi:num->B->A) n`; `psi:A->B`; `Q:real`;
      `rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z)`;
      `z':A`; `th:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        USE_THEN "cl5" (MP_TAC o SPECL [`tau:real`; `w:B`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> x <= b ==> x <= c`) THEN
    EXPAND_TAC "Mk" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        SUBGOAL_THEN `&4 / rho * rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) = (&4 * rfs_vscalar (V n) s (phi n z)) / rho` SUBST1_TAC THENL
         [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* the point lemma *)
  USE_THEN "ptd" (MP_TAC o SPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
    `(t:num->real) n`; `sj:real`; `s:real`; `Q:real`;
    `(phi:num->B->A) n z`; `B':A->bool`; `Lc:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `\v. inv Q %% (g:real->B->real^3^3) tau v`;
    `W(n:num):B->bool`; `(phi:num->B->A) n`; `psi:A->B`; `Mk * th`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "N6" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&4 * Lc / rho = (&4 * Lc) / rho` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      EXPAND_TAC "B'" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "B'" THEN
      UNDISCH_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) ((&4 * rr) * inv(sqrt Q)) SUBSET IMAGE (phi n) (Kc INTER W n)` THEN
      UNDISCH_TAC `(Kc:B->bool) SUBSET O` THEN SET_TAC[];
      UNDISCH_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) ((&4 * rr) * inv(sqrt Q)) SUBSET IMAGE (phi n) (Kc INTER W n)` THEN
      UNDISCH_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s ((phi:num->B->A) n z) (rr * inv(sqrt Q)) SUBSET rfs_vball (V n) s (phi n z) ((&4 * rr) * inv(sqrt Q))` THEN
      SET_TAC[]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* MT Claim 11.35 on the whole window.                                      *)
(* The base (P2HN_1135_BASE): for a compact set K of the limit, eventually  *)
(* the points phi_n z (z in K) lie in a fixed rescaled ball about x_n at    *)
(* t_n, hence are strong necks with Q_n <= D1 R (D1 depending on K).  The  *)
(* induction (P2HN_1135_ALL): j applications of P2HN_1135_STEP cover        *)
(* [max(-t', -j/(4 Qb)), 0] with R >= rho Q_n, rho depending on K; j large *)
(* covers [-t', 0].                                                         *)
(* ========================================================================= *)

(* The base of the induction: necks at the final times.                     *)

let P2HN_1135_BASE = prove
 (`!C1 eps1 Lc Qb T0
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t (top:B topology) atlas g xl W phi K.
     p2hn_spk (C1,eps1,Lc,Qb) V x t /\
     p2hn_lpack T0 V x t (top,atlas) g xl W phi /\
     compact_in top K
     ==> ?D1 N. &0 < D1 /\
                !n z. N <= n /\ z IN K
                   ==> z IN W n /\
                       (?e. rfs_strong_neck (V n) eps1 (phi n z) (t n) e) /\
                       rfs_vscalar (V n) (t n) (phi n z) <= Qb * rfs_vscalar (V n) (t n) (x n) /\
                       rfs_vscalar (V n) (t n) (x n) <= D1 * rfs_vscalar (V n) (t n) (phi n z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2hn_spk; p2hn_lpack] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
    (CONJUNCTS_THEN2 (LABEL_TAC "can") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "lb")))))))
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "cplt")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ends")))))))
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "reg" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2c_flow_limit_with")) (concl th))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0)) /\
                mfd_complete (top,atlas) (g (&0))` STRIP_ASSUME_TAC THENL
   [USE_THEN "cplt" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `xl:B`; `K:B->bool`] LIM_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!k. t k + &0 / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) (x k) = (t:num->real) k`
  ASSUME_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `{s | --T0 < s /\ s <= &0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`; `xl:B`;
    `D0:real`; `D0 + &1`] LIM_BALL_OUT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ARITH `D < D + &1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  USE_THEN "nk" (MP_TAC o SPEC `D0 + &1`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  USE_THEN "lb" (MP_TAC o SPEC `D0 + &1`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `N4:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N4")))) THEN
  MAP_EVERY EXISTS_TAC [`D1:real`; `MAX N2 (MAX N3 N4)`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:B`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D0` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `K:B->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `D0:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "N2" (MP_TAC o SPECL [`n:num`; `z:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "N3" (MP_TAC o SPECL [`n:num`; `(phi:num->B->A) n z`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2HN_VBALL_EQ]; ALL_TAC] THEN
  USE_THEN "N4" (MP_TAC o SPECL [`n:num`; `(phi:num->B->A) n z`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2HN_VBALL_EQ]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* Claim 11.35 for all backward times in [-t', 0].                           *)

let P2HN_1135_ALL = prove
 (`!u:A->bool w:B->bool.
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C1 eps1 Lc Qb T0
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t (top:B topology) atlas g xl W phi t'.
              &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\
              p2hn_spk (C1,eps1,Lc,Qb) V x t /\
              p2hn_lpack T0 V x t (top,atlas) g xl W phi /\
              &0 <= t' /\ t' < T0
              ==> !K. compact_in top K
                      ==> ?rho N. &0 < rho /\
                          !n z tau. N <= n /\ z IN K /\ --t' <= tau /\ tau <= &0
                                ==> z IN W n /\
                                    (?e. rfs_strong_neck (V n) eps1 (phi n z)
                                           (t n + tau / rfs_vscalar (V n) (t n) (x n)) e) /\
                                    rho * rfs_vscalar (V n) (t n) (x n) <=
                                    rfs_vscalar (V n) (t n + tau / rfs_vscalar (V n) (t n) (x n))
                                                (phi n z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_1135_STEP) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "step"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `t':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Qb` ASSUME_TAC THENL
   [UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN SIMP_TAC[p2hn_spk];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = inv(&4 * Qb)` THEN
  SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j K. compact_in top K
          ==> ?rho N. &0 < rho /\ rho <= &1 /\
                !n z tau. N <= n /\ z IN K /\ max (--t') (--(&j * c0)) <= tau /\ tau <= &0
                  ==> z IN W n /\
                      (?e. rfs_strong_neck ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) eps1 ((phi:num->B->A) n z)
                             (t n + tau / rfs_vscalar (V n) (t n) ((x:num->A) n)) e) /\
                      rho * rfs_vscalar (V n) (t n) (x n) <=
                      rfs_vscalar (V n) (t n + tau / rfs_vscalar (V n) (t n) (x n)) (phi n z)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [(* the base: tau = 0 *)
      X_GEN_TAC `K:B->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
        `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
        `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`]
        P2HN_1135_BASE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `N:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bN")))) THEN
      ABBREV_TAC `rho0 = inv(max (&1) D1)` THEN
      SUBGOAL_THEN `&0 < rho0 /\ rho0 <= &1 /\ rho0 * D1 <= &1` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "rho0" THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(max (&1) D1) * max (&1) D1` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
            SUBGOAL_THEN `~(max (&1) D1 = &0)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LE_REFL]]];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`rho0:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `z:B`; `tau:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `tau = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
      USE_THEN "bN" (MP_TAC o SPECL [`n:num`; `z:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((phi:num->B->A) n z)` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` ASSUME_TAC THENL
         [UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN
          REWRITE_TAC[p2hn_spk] THEN SIMP_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `&0 < D1 * rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((phi:num->B->A) n z)` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_MUL_EQ]];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `rho0 * D1 * rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((phi:num->B->A) n z)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC(REAL_ARITH `c * r <= &1 * r ==> c * r <= r`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    (* the step *)
    X_GEN_TAC `K:B->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= &j * c0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
    USE_THEN "step" (MP_TAC o SPECL
     [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
      `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `t':real`;
      `max (--t') (--(&j * c0))`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `K:B->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `N:num`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sN"))))) THEN
    MAP_EVERY EXISTS_TAC [`rho:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:B`; `tau:real`] THEN
    STRIP_TAC THEN
    USE_THEN "sN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `max (--t') (--(&(SUC j) * c0)) <= tau` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* enough steps to cover [-t',0] *)
  MP_TAC(SPEC `t' / c0` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `J:num`) THEN
  SUBGOAL_THEN `t' <= &J * c0` ASSUME_TAC THENL
   [UNDISCH_TAC `t' / c0 <= &J` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  X_GEN_TAC `K:B->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`J:num`; `K:B->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `N:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "jN"))))) THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:B`; `tau:real`] THEN STRIP_TAC THEN
  USE_THEN "jN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The limit package of MT pp. 290-291.                                     *)
(* A limit on (-T0,0] given by Thm 11.8 part 1, restricted to the joinable  *)
(* class of the base point (connected), satisfies p2hn_lpack: Ricci flow,   *)
(* complete with nonnegative curvature and |Rm| bounded on each [a,0], and  *)
(* two ends at time 0 (P2HN_LPACK_FROM_LIMIT).  The two ends come from the  *)
(* necks at every point of the limit (P2HN_LIMIT_NECKS: the horn necks at   *)
(* phi_n z transfer by P2HN_NECK_TO_LIMIT) and P2HN_TWO_ENDS, with the      *)
(* sphere separation of the limit from P2B_SEP_FROM_FLOW_LIMIT.             *)
(* ========================================================================= *)

(* Riemannian metrics along a flow up to time 0, and curvature of a         *)
(* restriction to an open set.                                               *)

let P2HN_UPTO_RIEMANNIAN = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) g T0.
     &0 < T0 /\ (!a. --T0 < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)
     ==> !s. --T0 < s /\ s <= &0 ==> riemannian_metric atlas (g s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--T0 / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[rfs_flow_upto];
    FIRST_X_ASSUM(MP_TAC o SPEC `(--T0 + s) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2HN_RESTRICT_POINT = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) C y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top C /\
     y IN topspace (subtopology top C)
     ==> y IN topspace top /\
         mfd_rm_norm (restrict_atlas atlas C) (restrict_metric atlas C g) y =
         mfd_rm_norm atlas g y /\
         !u v. ~collinear {vec 0,u,v}
               ==> ?u' v'. ~collinear {vec 0,u',v'} /\
                           mfd_sectional (restrict_atlas atlas C) (restrict_metric atlas C g) y u v =
                           mfd_sectional atlas g y u' v'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN C /\ y IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN topspace (subtopology top C)` THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_RM_NORM_RESTRICT THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `C:B->bool`;
                 `g:B->real^3^3`; `y:B`] MFDR_SECTIONAL_SET_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `mfd_sectional (restrict_atlas atlas C)
                              (restrict_metric atlas C (g:B->real^3^3)) (y:B) u v`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u':real^3`; `v':real^3`] THEN ASM_REWRITE_TAC[]);;

(* Every point of the limit is an eps'-neck centre at time 0.                *)

let P2HN_LIMIT_NECKS = prove
 (`?epsN. &0 < epsN /\
     !C1 eps Lc Qb
      (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      x t J (top:B topology) atlas g xl W phi eps'.
        &0 < eps /\ eps <= epsN /\ eps < eps' /\ eps' <= &1 / &4 /\
        p2hn_spk (C1,eps,Lc,Qb) V x t /\
        p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) J (top,atlas) g xl W phi /\
        riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0)) /\
        connected_space top
        ==> !z. z IN topspace top ==> ?e. rfs_neck (top,atlas) (g (&0)) eps' z e`,
  X_CHOOSE_THEN `epsN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nib")) P2HN_NECK_IN_BALL THEN
  EXISTS_TAC `epsN:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps:real`; `Lc:real`; `Qb:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `eps':real`] THEN
  STRIP_TAC THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  UNDISCH_TAC `p2hn_spk (C1,eps,Lc,Qb) V (x:num->A) t` THEN REWRITE_TAC[p2hn_spk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
    (CONJUNCTS_THEN2 (LABEL_TAC "can") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "lb"))))))) THEN
  SUBGOAL_THEN `!n s. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2HN_REGULAR_HAUSDORFF THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "reg" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2c_flow_limit_with")) (concl th))) THEN
  SUBGOAL_THEN `!k. t k + &0 / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) (x k) = (t:num->real) k`
  ASSUME_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  (* the base ball containing z *)
  ABBREV_TAC `D0 = mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl z + &1` THEN
  SUBGOAL_THEN `&0 < D0 /\ (z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl z` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl z` MP_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`; `xl:B`;
    `D0:real`; `D0 + &1`] LIM_BALL_OUT) THEN
  ASM_REWRITE_TAC[REAL_ARITH `D < D + &1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  USE_THEN "nk" (MP_TAC o SPEC `D0 + &1`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  USE_THEN "lb" (MP_TAC o SPEC `D0 + &1`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `N3b:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N3b")))) THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `inv D1`]
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_NECK_TO_LIMIT)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ntl"))) THEN
  ABBREV_TAC `r = &2 * (inv eps + &5) * sqrt D1` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV];
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) z (r + &2)` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[&0,&0] SUBSET (J:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 <= s /\ s <= &0 ==> s = &0`)) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`; `&0`;
    `{z:B}`; `Kc:B->bool`; `r:real`; `r + &1`] P2HN_LIM_BALL_IN_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 <= s /\ s <= &0 ==> s = &0`)) THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SING_SUBSET];
      REWRITE_TAC[IN_SING] THEN MAP_EVERY X_GEN_TAC [`y:B`; `s:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN
      REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `d < (r + &1) + &1 ==> d <= r + &2`];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4")) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&0`; `&0`; `Kc:B->bool`; `rfs_kreg eps`; `th:real`] o
    check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 5 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N5:num` (LABEL_TAC "N5")) THEN
  ABBREV_TAC `n = MAX N2 (MAX N3 (MAX N3b (MAX N4 N5)))` THEN
  SUBGOAL_THEN `N2 <= (n:num) /\ N3 <= n /\ N3b <= n /\ N4 <= n /\ N5 <= n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  SUBGOAL_THEN `&0 < Q /\ (x:num->A) n IN topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) (rfs_vatlas (V n) (t n)) /\ riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "N2" (MP_TAC o SPECL [`n:num`; `z:B`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "N3b" (MP_TAC o SPECL [`n:num`; `(phi:num->B->A) n z`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2HN_VBALL_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "N3" (MP_TAC o SPECL [`n:num`; `(phi:num->B->A) n z`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2HN_VBALL_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e0:real^3->A`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n),rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) eps ((phi:num->B->A) n z) e0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_STRONG_NECK_SLICE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((phi:num->B->A) n z)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < D1 * rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((phi:num->B->A) n z)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_MUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((phi:num->B->A) n z))) <= sqrt D1 * inv(sqrt Q)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_INV; GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    SUBGOAL_THEN `D1 * inv Q = inv(Q / D1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) z (r + &1) INTER W n)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n), rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) ((phi:num->B->A) n z) (r * inv(sqrt Q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n), rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) ((phi:num->B->A) n z) (&2 * (inv eps + &5) * inv(sqrt(mfd_scalar (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) (phi n z))))` THEN
      CONJ_TAC THENL
       [USE_THEN "nib" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFA_MFD_BALL_MONO THEN REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN
        EXPAND_TAC "r" THEN
        SUBGOAL_THEN `(&2 * (inv eps + &5) * sqrt D1) * inv(sqrt Q) = &2 * (inv eps + &5) * (sqrt D1 * inv(sqrt Q))` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 <= x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV]];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      USE_THEN "N4" (MP_TAC o SPECL [`n:num`; `z:B`; `&0`; `w:A`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_SING; REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "N5" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "cl5"))) THEN
  USE_THEN "dif" (MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN `!v:B. v IN W(n:num) ==> (psi:A->B) ((phi:num->B->A) n v) = v` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o el 4 o CONJUNCTS o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
      can (find_term (fun t -> t = `psi:A->B`)) (concl th) && not (is_forall (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th)));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE ((psi:A->B) o e0) (rfs_neck_dom eps)
        ==> lck_dist2 (rfs_kreg eps)
              (metric_local atlas (chart_at atlas y) ((g:real->B->real^3^3) (&0)))
              (\z. Q %% rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))
                          ((phi:num->B->A) n o chart_inv (chart_at atlas y))
                          (rfs_vmetric (V n) (t n)) z)
              (SND(chart_at atlas y) y) <= th`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e0:real^3->A) w IN IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) z (r + &1) INTER W n)` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) z (r + &1) INTER W n)` THEN
      UNDISCH_TAC `(w:real^3) IN rfs_neck_dom eps` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `v:B` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "cl5" (MP_TAC o SPECL [`&0`; `v:B`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN EXPAND_TAC "Kc" THEN
      UNDISCH_TAC `(v:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) z (r + &1)` THEN
      REWRITE_TAC[mfd_ball; mfd_cball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ntl" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (&0)`;
    `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `W(n:num):B->bool`; `(phi:num->B->A) n`; `psi:A->B`; `Q:real`; `(phi:num->B->A) n z`;
    `e0:real^3->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) z (r + &1) INTER W n)` THEN
      SET_TAC[];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `(psi:A->B) o (e0:real^3->A)` THEN
  ASM_REWRITE_TAC[]);;

(* The limit package.                                                        *)

let P2HN_LPACK_FROM_LIMIT = prove
 (`?eps0. &0 < eps0 /\
     !C1 eps1 Lc Qb
      (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      x t (top:B topology) atlas g xl T0.
        &0 < eps1 /\ eps1 <= eps0 /\
        p2hn_spk (C1,eps1,Lc,Qb) V x t /\
        (!n. apx_sphere_sep (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))) /\
        p3_flow_limit V x t (\n. rfs_vscalar (V n) (t n) (x n)) (top,atlas) g xl T0 /\
        (!s. --T0 < s /\ s <= &0
             ==> mfd_complete (top,atlas) (g s) /\
                 (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
        (!a. --T0 < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                    ==> mfd_rm_norm atlas (g s) y <= K)
        ==> ?top' atlas' g' W phi. p2hn_lpack T0 V x t (top',atlas') g' xl W phi`,
  X_CHOOSE_THEN `epsN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lnk"))
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_LIMIT_NECKS) THEN
  X_CHOOSE_THEN `epsT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "two"))
    (INST_TYPE [`:B`,`:A`] P2HN_TWO_ENDS) THEN
  EXISTS_TAC `min epsN (min epsT (&1 / &4)) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `T0:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sep")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cs") (LABEL_TAC "rmb"))))))) THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN
    REWRITE_TAC[p2hn_spk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `n:num` o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\ smooth_manifold_atlas top atlas /\
                xl IN topspace top /\ &0 < T0 /\
                (!a. --T0 < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t (\n. rfs_vscalar (V n) (t n) (x n)) (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B) T0` THEN
    REWRITE_TAC[p3_flow_limit] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `T0:real`] P2HN_UPTO_RIEMANNIAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "riem") THEN
  MP_TAC(ISPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
    `xl:B`; `T0:real`] P2CO_P3_FLOW_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`]
    P2CO_CLASS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Cs = {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (subtopology (top:B topology) Cs) /\
                smooth_manifold_atlas (subtopology top Cs) (restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs) /\
                xl IN topspace (subtopology top Cs) /\
                (!a. --T0 < a /\ a < &0
                     ==> rfs_flow_upto (subtopology top Cs,restrict_atlas atlas Cs) a (&0)
                           (\s. restrict_metric atlas Cs ((g:real->B->real^3^3) s)))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p3_flow_limit")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "subtopology")) (concl th))) THEN
    REWRITE_TAC[p3_flow_limit] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_FLOW_LIMIT_ON o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p3_flow_limit")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "subtopology")) (concl th))) THEN
  REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A` (LABEL_TAC "fl"))) THEN
  MP_TAC(ISPECL [`subtopology (top:B topology) Cs`; `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs`;
                 `\s. restrict_metric (atlas:((B->bool)#(B->real^3))->bool) Cs ((g:real->B->real^3^3) s)`; `T0:real`] P2HN_UPTO_RIEMANNIAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "riem'") THEN
  SUBGOAL_THEN `!s. --T0 < s /\ s <= &0
                    ==> mfd_complete (subtopology (top:B topology) Cs,restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs)
                                     (restrict_metric atlas Cs ((g:real->B->real^3^3) s))`
  (LABEL_TAC "cpl'") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `xl:B`] P2CO_CLASS_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "cs" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs) (restrict_metric atlas Cs ((g:real->B->real^3^3) (&0))) /\ mfd_complete (subtopology (top:B topology) Cs,restrict_atlas atlas Cs) (restrict_metric atlas Cs (g (&0)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "riem'" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "cpl'" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN topspace (subtopology (top:B topology) Cs) ==> ?e. rfs_neck (subtopology top Cs,restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs) (restrict_metric atlas Cs ((g:real->B->real^3^3) (&0))) (&2 * eps1) z e` (LABEL_TAC "nks") THENL
   [USE_THEN "lnk" (MP_TAC o SPECL
     [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `{s | --T0 < s /\ s <= &0}`; `subtopology (top:B topology) Cs`;
      `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs`;
      `\s. restrict_metric (atlas:((B->bool)#(B->real^3))->bool) Cs ((g:real->B->real^3^3) s)`;
      `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&2 * eps1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sphere_sep (subtopology (top:B topology) Cs) (restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2B_SEP_FROM_FLOW_LIMIT) THEN
    MAP_EVERY EXISTS_TAC
     [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`;
      `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
      `\s. restrict_metric (atlas:((B->bool)#(B->real^3))->bool) Cs ((g:real->B->real^3^3) s)`;
      `xl:B`; `T0:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    FIRST_ASSUM(MP_TAC o SPECL [`k:num`; `(t:num->real) k`] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) k` THEN
    UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN
    REWRITE_TAC[p2hn_spk] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "nks" (MP_TAC o SPEC `xl:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ex:real^3->B`) THEN
  USE_THEN "two" (MP_TAC o SPECL
   [`subtopology (top:B topology) Cs`; `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs`;
    `restrict_metric (atlas:((B->bool)#(B->real^3))->bool) Cs ((g:real->B->real^3^3) (&0))`;
    `&2 * eps1`; `xl:B`; `ex:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology (top:B topology) Cs`; `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) Cs`;
    `\s. restrict_metric (atlas:((B->bool)#(B->real^3))->bool) Cs ((g:real->B->real^3^3) s)`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[p2hn_lpack] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "riem'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "cpl'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `Cs:B->bool`; `y:B`] P2HN_RESTRICT_POINT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
        (MP_TAC o SPECL [`u:real^3`; `v:real^3`]))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "cs" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rmb" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN EXISTS_TAC `K:real` THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `Cs:B->bool`; `y:B`] P2HN_RESTRICT_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
    USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* One step of the backward iteration of                                    *)
(* MT p. 291.  With the limit package on (-T0,0] and the backward           *)
(* hypothesis below T0, Claim 11.35 (P2HN_1135_ALL) at t' = T0 - c gives    *)
(* strong necks at (y, t_n - t'/Q_n) for y in the A-balls, with            *)
(* R <= (5/4) Qb Q_n by P2HN_NECK_R_BACKWARD; P2HN_BACK_EXTEND then gives   *)
(* the backward hypothesis below T0 + c, c = 1/(5 Qb).                      *)
(* ========================================================================= *)

let P2HN_STEP_FROM_LPACK = prove
 (`!u:A->bool w:B->bool.
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C1 eps1 Lc Qb T0
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t (top:B topology) atlas g xl W phi r0.
              &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\
              p2hn_spk (C1,eps1,Lc,Qb) V x t /\
              p2hn_lpack T0 V x t (top,atlas) g xl W phi /\
              inv(&5 * Qb) <= T0 /\
              (!Tb. Tb < T0 ==> p2c_vblowup_back (pi / &6000,r0) V x t Tb)
              ==> !Tb. Tb < T0 + inv(&5 * Qb) ==> p2c_vblowup_back (pi / &6000,r0) V x t Tb`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_1135_ALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `epsA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all"))) THEN
  MP_TAC(SPEC `&1 / &4` (INST_TYPE [`:A`,`:A`] P2HN_NECK_R_BACKWARD)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2b:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bw"))) THEN
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))
    (INST_TYPE [`:A`,`:A`] P2HN_BACK_EXTEND) THEN
  EXISTS_TAC `min epsA (min eps2b eps3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `r0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  X_GEN_TAC `Tb:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < Qb` ASSUME_TAC THENL
   [UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN SIMP_TAC[p2hn_spk];
    ALL_TAC] THEN
  ABBREV_TAC `c = inv(&5 * Qb)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t' = T0 - c` THEN
  USE_THEN "all" (MP_TAC o SPECL
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `t':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "c35") THEN
  USE_THEN "ext" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`eps1:real`; `&5 / &4 * Qb`; `t':real`; `(t' + T0) / &2`] THEN
  UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN REWRITE_TAC[p2hn_spk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
    (CONJUNCTS_THEN2 (LABEL_TAC "can") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "lb"))))))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv (&2 * &5 / &4 * Qb) = &2 * c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < Qb` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_vblowup_back")) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `p2hn_lpack T0 V (x:num->A) t (top:B topology,atlas) g xl W phi` THEN
  REWRITE_TAC[p2hn_lpack] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "cplt")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ends"))))))) THEN
  SUBGOAL_THEN `!n s. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2HN_REGULAR_HAUSDORFF THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "reg" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2c_flow_limit_with")) (concl th))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0)) /\
                mfd_complete (top,atlas) (g (&0))` STRIP_ASSUME_TAC THENL
   [USE_THEN "cplt" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. t k + &0 / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) (x k) = (t:num->real) k`
  ASSUME_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  ABBREV_TAC `Kc = mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) xl (A + &3)` THEN
  ABBREV_TAC `Kz = mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) xl (A + &1)` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool) /\ compact_in top (Kz:B->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kc"; "Kz"] THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[&0,&0] SUBSET {s | --T0 < s /\ s <= &0}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `{s | --T0 < s /\ s <= &0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`; `&0`;
    `{xl:B}`; `Kc:B->bool`; `A:real`; `A + &1`] P2HN_LIM_BALL_IN_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 <= s /\ s <= &0 ==> s = &0`)) THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SING_SUBSET];
      REWRITE_TAC[IN_SING] THEN MAP_EVERY X_GEN_TAC [`y:B`; `s:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN
      REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `d < (A + &1) + &1 ==> d <= A + &3`];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4")) THEN
  USE_THEN "c35" (MP_TAC o SPEC `Kz:B->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))) THEN
  USE_THEN "nk" (MP_TAC o SPEC `A:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  EXISTS_TAC `MAX N1 (MAX N3 N4)` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
  USE_THEN "N4" (MP_TAC o SPECL [`n:num`; `xl:B`; `&0`; `y:A`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_SING; REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM P2HN_VBALL_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:B) IN Kz` ASSUME_TAC THENL
   [EXPAND_TAC "Kz" THEN
    UNDISCH_TAC `(z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl (A + &1)` THEN
    REWRITE_TAC[mfd_ball; mfd_cball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s''. t n - t' * inv Q <= s'' /\ s'' <= (t:num->real) n
                      ==> ?e. rfs_strong_neck ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) eps1 (y:A) s'' e`
  ASSUME_TAC THENL
   [X_GEN_TAC `s'':real` THEN STRIP_TAC THEN
    USE_THEN "N1" (MP_TAC o SPECL [`n:num`; `z:B`; `(s'' - (t:num->real) n) * Q`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `--t' = (--(t' * inv Q)) * Q` SUBST1_TAC THENL
         [SUBGOAL_THEN `~(Q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x * q ==> x * q <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:num->real) n + ((s'' - t n) * Q) / Q = s''` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(Q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t' * inv Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `s'':real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "bw" (MP_TAC o SPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
    `eps1:real`; `y:A`; `(t:num->real) n - t' * inv Q`; `(t:num->real) n`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(t:num->real) n - t' * inv Q`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "N3" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n) (A * inv(sqrt Q))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The backward iteration of MT p. 291 along the horn sequence: Thm 11.8     *)
(* part 1 (in the form P2HN_118_LIMIT) gives limits on (-T0,0] along         *)
(* subsequences; with P2HN_LPACK_FROM_LIMIT and P2HN_STEP_FROM_LPACK the     *)
(* step of P2HN_BACK_ITERATE holds with c = 1/(5 Qb), and the base is        *)
(* P2HN_BACK_BASE.  Result: p2c_vblowup_back for every backward time         *)
(* (P2HN_BACK_ALL), the hypothesis of Thm 11.8 part 2.                       *)
(* ========================================================================= *)

(* Subsequences.                                                             *)

let P2HN_SUBSEQ_GE = prove
 (`!sub n. p3_subseq sub ==> n <= sub n`,
  REWRITE_TAC[p3_subseq] THEN MESON_TAC[MONOTONE_BIGGER]);;

let P2HN_VBACK_SUBSEQ = prove
 (`!kappa r0 (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) x t Tb sub.
     p2c_vblowup_back (kappa,r0) V x t Tb /\ p3_subseq sub
     ==> p2c_vblowup_back (kappa,r0) (\n. V (sub n)) (\n. x (sub n)) (\n. t (sub n)) Tb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_vblowup_back] THEN STRIP_TAC THEN
  X_GEN_TAC `A:real` THEN FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[P2HN_SUBSEQ_GE]);;

let P2HN_VSEQ_SUBSEQ = prove
 (`!C eps kappa r0 mu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) x t sub.
     p2c_vblowup_seq (C,eps,kappa,r0,mu) V x t /\ p3_subseq sub
     ==> p2c_vblowup_seq (C,eps,kappa,r0,mu) (\n. V (sub n)) (\n. x (sub n)) (\n. t (sub n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_vblowup_seq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Q")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))))))) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `B:real` THEN USE_THEN "Q" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_SIMP_TAC[P2HN_SUBSEQ_GE];
    X_GEN_TAC `A:real` THEN USE_THEN "nc" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
    EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P2HN_SUBSEQ_GE]]);;

(* Thm 11.8 part 1 in the form used here.                                    *)

let P2HN_118_LIMIT = prove
 (`!u:A->bool w:B->bool.
     P2C_THM_11_8_VIEW_STATEMENT u w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t T0.
             &1 < C /\ &0 < eps /\ eps <= eps0 /\
             p2c_vblowup_seq (C,eps,kappa,r0,mu) V x t /\
             (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
             (!A. ?N. !n. N <= n
                          ==> compact_in (rfs_vtop (V n) (t n))
                                (rfs_vtop (V n) (t n) closure_of
                                 rfs_vball (V n) (t n) (x n)
                                   (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
             &0 < T0 /\ (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb)
             ==> ?sub (top:B topology) atlas g xl.
                    p3_subseq sub /\
                    p3_flow_limit (\n. V (sub n)) (\n. x (sub n)) (\n. t (sub n))
                      (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n))) (top,atlas) g xl T0 /\
                    (!s. --T0 < s /\ s <= &0
                         ==> mfd_complete (top,atlas) (g s) /\
                             (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                                      ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
                    (!a. --T0 < a
                         ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                       ==> mfd_rm_norm atlas (g s) y <= K)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_THM_11_8_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `T0:real`] THEN
  STRIP_TAC THEN
  USE_THEN "v" (MP_TAC o SPECL
   [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `T0:real` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN SIMP_TAC[]);;

(* The backward hypothesis for all backward times.                           *)

let P2HN_BACK_ALL = prove
 (`!u:A->bool w:B->bool.
     P2C_THM_11_8_VIEW_STATEMENT u w /\ P2C_REQ_CAP_FIX_STATEMENT u w /\
     P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps mu C1 eps1 Lc Qb r0
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t.
             &1 < C /\ &0 < eps /\ eps <= eps0 /\
             &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\
             p2c_vblowup_seq (C,eps,pi / &6000,r0,mu) V x t /\
             (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
             (!A. ?N. !n. N <= n
                          ==> compact_in (rfs_vtop (V n) (t n))
                                (rfs_vtop (V n) (t n) closure_of
                                 rfs_vball (V n) (t n) (x n)
                                   (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
             p2hn_spk (C1,eps1,Lc,Qb) V x t
             ==> !Tb. p2c_vblowup_back (pi / &6000,r0) V x t Tb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2HN_118_LIMIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e8:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l8"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2HN_STEP_FROM_LPACK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `es:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sfl"))) THEN
  X_CHOOSE_THEN `ep:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lpk"))
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_LPACK_FROM_LIMIT) THEN
  X_CHOOSE_THEN `eb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))
    (INST_TYPE [`:A`,`:A`] P2HN_BACK_BASE) THEN
  EXISTS_TAC `min e8 (min es (min ep eb))` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC
   [`C:real`; `eps:real`; `mu:real`; `C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `r0:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Qb` ASSUME_TAC THENL
   [UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN SIMP_TAC[p2hn_spk];
    ALL_TAC] THEN
  MATCH_MP_TAC P2HN_BACK_ITERATE THEN EXISTS_TAC `inv(&5 * Qb)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`sub:num->num`; `Tb:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `sub:num->num`] P2HN_SPK_SUBSEQ) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[p2hn_spk] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
      (CONJUNCTS_THEN2 (LABEL_TAC "can") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
      (CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "lb"))))))) THEN
    USE_THEN "base" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`eps1:real`; `Qb:real`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&5 * Qb)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`sub:num->num`; `T0:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < inv(&5 * Qb)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "l8" (MP_TAC o SPECL
     [`C:real`; `eps:real`; `pi / &6000`; `r0:real`; `mu:real`;
      `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
      `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`; `T0:real`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P2HN_VSEQ_SUBSEQ] THEN CONJ_TAC THENL
       [X_GEN_TAC `A:real` THEN
        FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `A:real` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "closure_of")) (concl th))) THEN
        EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
        ASM_SIMP_TAC[P2HN_SUBSEQ_GE];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top:B topology`
      (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
      (X_CHOOSE_THEN `xl:B` STRIP_ASSUME_TAC))))) THEN
    SUBGOAL_THEN `p2hn_spk (C1,eps1,Lc,Qb)
                    (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) ((sub2:num->num) n)))
                    (\n. (x:num->A) (sub (sub2 n))) (\n. (t:num->real) (sub (sub2 n)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(BETA_RULE(ISPECL [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
        `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
        `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`;
        `sub2:num->num`] P2HN_SPK_SUBSEQ)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2HN_SPK_SUBSEQ THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "lpk" (MP_TAC o SPECL
     [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
      `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) ((sub2:num->num) n))`;
      `\n. (x:num->A) ((sub:num->num) ((sub2:num->num) n))`; `\n. (t:num->real) ((sub:num->num) ((sub2:num->num) n))`;
      `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
      `xl:B`; `T0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
      (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `W:num->B->bool`
      (X_CHOOSE_THEN `phi:num->B->A` ASSUME_TAC))))) THEN
    EXISTS_TAC `sub2:num->num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sfl" (MP_TAC o SPECL
     [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
      `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) ((sub2:num->num) n))`;
      `\n. (x:num->A) ((sub:num->num) ((sub2:num->num) n))`; `\n. (t:num->real) ((sub:num->num) ((sub2:num->num) n))`;
      `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
      `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `r0:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `Tb:real` THEN DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL [`pi / &6000`; `r0:real`;
        `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
        `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`;
        `Tb:real`; `sub2:num->num`] P2HN_VBACK_SUBSEQ)) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
      SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Tools for the kappa-solution limit of                                    *)
(* MT p. 292: Thm 11.8 part 2 in the form used here (P2HN_118_KSOL), necks  *)
(* of a limit at any time s from strong necks of the approximants at the    *)
(* rescaled times (P2HN_LIMIT_NECKS_AT), and the transfer of evolving necks *)
(* of a kappa-solution limit back to the approximants (P2HN_NECK_LIMIT).    *)
(* ========================================================================= *)

(* Thm 11.8 part 2 in the form used here.                                    *)

let P2HN_118_KSOL = prove
 (`!u:A->bool w:B->bool.
     P2C_THM_11_8_VIEW_STATEMENT u w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t.
             &1 < C /\ &0 < eps /\ eps <= eps0 /\
             p2c_vblowup_seq (C,eps,kappa,r0,mu) V x t /\
             (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
             (!A. ?N. !n. N <= n
                          ==> compact_in (rfs_vtop (V n) (t n))
                                (rfs_vtop (V n) (t n) closure_of
                                 rfs_vball (V n) (t n) (x n)
                                   (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
             (!Tb. &0 < Tb ==> p2c_vblowup_back (kappa,r0) V x t Tb)
             ==> ?sub (top:B topology) atlas g xl.
                    p3_subseq sub /\
                    (!Tl. &0 < Tl
                          ==> p3_flow_limit (\n. V (sub n)) (\n. x (sub n)) (\n. t (sub n))
                                (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                                (top,atlas) g xl Tl) /\
                    p2b_kappa_solution kappa (top,atlas) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_THM_11_8_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`] THEN
  STRIP_TAC THEN
  USE_THEN "v" (MP_TAC o SPECL
   [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN SIMP_TAC[]);;

(* Necks of a limit at time s0.                                              *)

let P2HN_LIMIT_NECKS_AT = prove
 (`?epsN. &0 < epsN /\
     !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      x t J (top:B topology) atlas g xl W phi eps eps' s0.
        &0 < eps /\ eps <= epsN /\ eps < eps' /\ eps' <= &1 / &4 /\
        (!n. p2c_regular_view (V n)) /\
        p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) J (top,atlas) g xl W phi /\
        s0 IN J /\ riemannian_metric atlas (g s0) /\ mfd_complete (top,atlas) (g s0) /\
        (!K. compact_in top K
             ==> ?c1 N. &0 < c1 /\
                        !n z. N <= n /\ z IN K
                           ==> z IN W n /\
                               (?e. rfs_strong_neck (V n) eps (phi n z)
                                      (t n + s0 / rfs_vscalar (V n) (t n) (x n)) e) /\
                               c1 * rfs_vscalar (V n) (t n) (x n) <=
                               rfs_vscalar (V n) (t n + s0 / rfs_vscalar (V n) (t n) (x n))
                                           (phi n z))
        ==> !z. z IN topspace top ==> ?e. rfs_neck (top,atlas) (g s0) eps' z e`,
  X_CHOOSE_THEN `epsN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nib")) P2HN_NECK_IN_BALL THEN
  EXISTS_TAC `epsN:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `eps:real`; `eps':real`; `s0:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh")))))))))) THEN
  X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n s. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2HN_REGULAR_HAUSDORFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2c_flow_limit_with")) (concl th))) THEN
  (* the neck hypothesis at z *)
  USE_THEN "nh" (MP_TAC o SPEC `{z:B}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SING]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `N3:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N3")))) THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `c1:real`]
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_NECK_TO_LIMIT)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ntl"))) THEN
  ABBREV_TAC `r = &2 * (inv eps + &5) * inv(sqrt c1)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV];
        MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = mfd_cball (top,atlas) ((g:real->B->real^3^3) s0) z (r + &2)` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s0)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[s0,s0] SUBSET (J:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `s0 <= s /\ s <= s0 ==> s = s0`)) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `s0:real`; `s0:real`;
    `{z:B}`; `Kc:B->bool`; `r:real`; `r + &1`] P2HN_LIM_BALL_IN_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `s0 <= s /\ s <= s0 ==> s = s0`)) THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SING_SUBSET];
      REWRITE_TAC[IN_SING] THEN MAP_EVERY X_GEN_TAC [`y:B`; `s:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s:real = s0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN
      REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `d < (r + &1) + &1 ==> d <= r + &2`];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4")) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s0:real`; `s0:real`; `Kc:B->bool`; `rfs_kreg eps`; `th:real`] o
    check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 5 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N5:num` (LABEL_TAC "N5")) THEN
  ABBREV_TAC `n = MAX N3 (MAX N4 N5)` THEN
  SUBGOAL_THEN `N3 <= (n:num) /\ N4 <= n /\ N5 <= n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "N3" (MP_TAC o SPECL [`n:num`; `z:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `e0:real^3->A`)
    ASSUME_TAC)) THEN
  ABBREV_TAC `Q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  ABBREV_TAC `ts = (t:num->real) n + s0 / Q` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&0`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th)))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts,rfs_vatlas (V n) ts) (rfs_vmetric (V n) ts) eps ((phi:num->B->A) n z) e0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_STRONG_NECK_SLICE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts) (rfs_vmetric (V n) ts)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `ts:real`] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) n z` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts ((phi:num->B->A) n z))) <= inv(sqrt c1) * inv(sqrt Q)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_INV; GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) z (r + &1) INTER W n)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts, rfs_vatlas (V n) ts) (rfs_vmetric (V n) ts) ((phi:num->B->A) n z) (r * inv(sqrt Q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts, rfs_vatlas (V n) ts) (rfs_vmetric (V n) ts) ((phi:num->B->A) n z) (&2 * (inv eps + &5) * inv(sqrt(mfd_scalar (rfs_vatlas (V n) ts) (rfs_vmetric (V n) ts) (phi n z))))` THEN
      CONJ_TAC THENL
       [USE_THEN "nib" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFA_MFD_BALL_MONO THEN REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN
        EXPAND_TAC "r" THEN
        SUBGOAL_THEN `(&2 * (inv eps + &5) * inv(sqrt c1)) * inv(sqrt Q) = &2 * (inv eps + &5) * (inv(sqrt c1) * inv(sqrt Q))` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 <= x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV]];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      USE_THEN "N4" (MP_TAC o SPECL [`n:num`; `z:B`; `s0:real`; `w:A`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_SING; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "N5" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "cl5"))) THEN
  USE_THEN "dif" (MP_TAC o SPEC `s0:real`) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN `!v:B. v IN W(n:num) ==> (psi:A->B) ((phi:num->B->A) n v) = v` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o el 4 o CONJUNCTS o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
      can (find_term (fun t -> t = `psi:A->B`)) (concl th) && not (is_forall (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th)));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE ((psi:A->B) o e0) (rfs_neck_dom eps)
        ==> lck_dist2 (rfs_kreg eps)
              (metric_local atlas (chart_at atlas y) ((g:real->B->real^3^3) s0))
              (\z. Q %% rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts)
                          ((phi:num->B->A) n o chart_inv (chart_at atlas y))
                          (rfs_vmetric (V n) ts) z)
              (SND(chart_at atlas y) y) <= th`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e0:real^3->A) w IN IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) z (r + &1) INTER W n)` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) z (r + &1) INTER W n)` THEN
      UNDISCH_TAC `(w:real^3) IN rfs_neck_dom eps` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `v:B` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "cl5" (MP_TAC o SPECL [`s0:real`; `v:B`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN EXPAND_TAC "Kc" THEN
      UNDISCH_TAC `(v:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) z (r + &1)` THEN
      REWRITE_TAC[mfd_ball; mfd_cball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ntl" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) s0`;
    `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts`;
    `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts`;
    `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ts`;
    `W(n:num):B->bool`; `(phi:num->B->A) n`; `psi:A->B`; `Q:real`; `(phi:num->B->A) n z`;
    `e0:real^3->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN
    UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET IMAGE ((phi:num->B->A) n) (mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) z (r + &1) INTER W n)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `(psi:A->B) o (e0:real^3->A)` THEN
  ASM_REWRITE_TAC[]);;

(* MT p. 292, the transfer back: generalizes P2BL_NECK_LIMIT (pc_p2b_ltr):   *)
(* the hypothesis p2bl_vslices V x t is weakened to its consequence          *)
(* P2BL_VSLICES_SLICES (smooth atlases and Riemannian metrics on nonempty    *)
(* slices), the only use the proof makes of it; no completeness of the       *)
(* slices at t_n, which fails for the horizon slices of maximal extensions.  *)
(* Otherwise the proof is that of P2BL_NECK_LIMIT.                           *)

let P2HN_NECK_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl kappa eps a e
    (P:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->A->bool).
     (!k s. ~(topspace(rfs_vtop (V k) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)) /\
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl) /\
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < eps /\ eps < &1 /\
     rfs_evolving_neck (p2b_kview (top,atlas) g) eps xl (&0) a e /\
     (?delta. &0 < delta /\
        !V' t' Q' psi.
          (!s. --a < s /\ s <= &0
               ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                         (rfs_vatlas V' (t' + s / Q')) /\
                   riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                     (rfs_vmetric V' (t' + s / Q'))) /\
          p3_view_close (p2b_kview (top,atlas) g) (&0)
            (rfs_vscalar (p2b_kview (top,atlas) g) (&0) xl) (IMAGE e (rfs_neck_dom eps))
            (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta
          ==> P V' t' (psi xl))
     ==> ?N. !n. N <= n ==> P (V n) (t n) (x n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 (LABEL_TAC "lim")
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NO"))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KVIEW_NECK0) THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->B) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck" with Failure _ -> false)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_NECK_CLOSURE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                          `(g:real->B->real^3^3) (&0)`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "lim" (MP_TAC o SPEC `a / R + &1`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_flow_limit]) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `Q:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `a / R + &1`] P2BL_FLOW_LIMIT_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps)`;
                             `IMAGE (e:real^3->B) (rfs_neck_dom eps)`;
                             `--(a / R)`; `delta:real`; `R:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  SUBGOAL_THEN `(xl:B) IN IMAGE (e:real^3->B) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck" with Failure _ -> false)) THEN
    STRIP_TAC THEN MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. k0 <= n /\ --a < s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / (R * Q n)))
                                    (rfs_vatlas (V n) (t n + s / (R * Q n))) /\
              riemannian_metric (rfs_vatlas (V n) (t n + s / (R * Q n)))
                                (rfs_vmetric (V n) (t n + s / (R * Q n)))`
  (LABEL_TAC "slk") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:num->real) n + s / (R * Q n) = t n + (s / R) / Q n` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < (Q:num->real) n` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    USE_THEN "sl" MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) n xl` THEN
    USE_THEN "k0" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s / R`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[REAL_ARITH `--(s / R) = --s / R`] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:A->B` MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    MATCH_MP_TAC(SET_RULE `(a:A) IN s ==> s SUBSET t ==> a IN t`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REMOVE_THEN "NO" (MP_TAC o SPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
                                    `(t:num->real) n`; `R * (Q:num->real) n`;
                                    `(phi:num->B->A) n`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "slk" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p3_view_close; P2BL_KVIEW_ACCESS] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 + s / R <= &0 /\ --(a / R) <= &0 + s / R` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ADD_LID] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[GSYM real_div; REAL_ARITH `--(s / R) = --s / R`] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2BL_KVIEW_ACCESS] THEN
    SUBGOAL_THEN `(t:num->real) n + s / (R * Q n) = t n + (&0 + s / R) / Q n` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ADD_LID] THEN
      SUBGOAL_THEN `&0 < (Q:num->real) n` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    USE_THEN "k0" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&0 + s / R`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Local orientability of the limit (the p2b_lorient half of p2b_ksep for    *)
(* P2B_KAPPA_NECKS_ROUND_L_FIX).  The image under a horn H of the points y   *)
(* with norm y > 1/2 is diffeomorphic to an open subset of R^3, hence        *)
(* orientable (P2HN_HORN_ORIENTABLE); a relatively compact open set X of the *)
(* limit is mapped by phi_n into such a horn image for n large (the A-balls  *)
(* lie in the horns), so it is orientable by P2B_ORIENTABLE_EMBED            *)
(* (P2HN_LIMIT_LORIENT, with the orientability of R^3 as a hypothesis,       *)
(* discharged by P2HN_EUCLID_ORIENTABLE).                                    *)
(* ========================================================================= *)

(* R^3 is orientable: the statement of STDS_EUCLID_ORIENTABLE                *)
(* (pc_p2c_stdc1), proved here to keep pc_p2c_stdc1 and its closure out of   *)
(* this unit.                                                                *)

let P2HN_EUCLID_ORIENTABLE = prove
 (`mfd_orientable (euclidean:(real^3)topology) (open_set_atlas (:real^3))`,
  REWRITE_TAC[mfd_orientable] THEN EXISTS_TAC `open_set_atlas (:real^3)` THEN
  REWRITE_TAC[UNION_IDEMPOT; P2C_EUCLID_FACTS; mfd_oriented_atlas;
              RFB_OPEN_SET_ATLAS_CASES] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `(:real^3)`;
                 `\x:real^3. x`; `x:real^3`] CHART_JAC_SELF) THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; RFB_OPEN_SET_ATLAS_CASES; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_ID; DET_I; REAL_LT_01]);;

let P2HN_HORN_ORIENTABLE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) th en H.
     mfd_orientable (euclidean:(real^3)topology) (open_set_atlas (:real^3)) /\
     smooth_manifold_atlas (rfs_vtop V th) (rfs_vatlas V th) /\
     p3_horn V th en H
     ==> open_in (rfs_vtop V th) (IMAGE H {y | &1 / &2 < norm y}) /\
         mfd_orientable (subtopology (rfs_vtop V th) (IMAGE H {y | &1 / &2 < norm y}))
                        (restrict_atlas (rfs_vatlas V th) (IMAGE H {y | &1 / &2 < norm y}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_horn; mfd_param] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `e':A->real^3`) (K ALL_TAC)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_diffeo (euclidean:(real^3)topology) (open_set_atlas (:real^3))
                   {y | &1 / &2 < norm y} (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) th)
                   (rfs_vatlas V th) (IMAGE H {y | &1 / &2 < norm y}) H e'` THEN
    SIMP_TAC[mfd_diffeo];
    MATCH_MP_TAC(INST_TYPE [`:real^3`,`:B`; `:3`,`:N`] P2B_ORIENTABLE_EMBED) THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                          `{y:real^3 | &1 / &2 < norm y}`; `e':A->real^3`; `H:real^3->A`] THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS]]);;

let P2HN_LIMIT_LORIENT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t (top:B topology) atlas g xl Tl en H.
     mfd_orientable (euclidean:(real^3)topology) (open_set_atlas (:real^3)) /\
     (!n. p2c_regular_view (V n)) /\
     p3_flow_limit V x t (\n. rfs_vscalar (V n) (t n) (x n)) (top,atlas) g xl Tl /\
     riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0)) /\
     connected_space top /\
     (!n. p3_horn (V n) (t n) en (H n)) /\
     (!A. &0 < A
          ==> ?N. !n. N <= n
                      ==> rfs_vball (V n) (t n) (x n)
                            (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                          SUBSET p3_horn_set (H n))
     ==> p2b_lorient top atlas`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "horn") (LABEL_TAC "hb")))))))) THEN
  REWRITE_TAC[p2b_lorient] THEN X_GEN_TAC `X:B->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n s. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2HN_REGULAR_HAUSDORFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Tl` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t (\n. rfs_vscalar (V n) (t n) (x n)) (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B) Tl` THEN
    SIMP_TAC[p3_flow_limit];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_FLOW_LIMIT_ON) THEN REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A` (LABEL_TAC "fl"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2c_flow_limit_with")) (concl th))) THEN
  SUBGOAL_THEN `!k. t k + &0 / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) (x k) = (t:num->real) k`
  ASSUME_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  ABBREV_TAC `K = (top:B topology) closure_of X` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `xl:B`; `K:B->bool`] LIM_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:B) IN K /\ z IN topspace top` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN
      MP_TAC(ISPECL [`top:B topology`; `X:B->bool`] CLOSURE_OF_SUBSET) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `X:B->bool`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:B) IN X` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `D:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `{s | --Tl < s /\ s <= &0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`; `xl:B`;
    `D:real`; `D + &1`] LIM_BALL_OUT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ARITH `D < D + &1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  USE_THEN "hb" (MP_TAC o SPEC `D + &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&0`; `&0`; `K:B->bool`; `0`; `&1`] o
    check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 5 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N5:num` (LABEL_TAC "N5")) THEN
  ABBREV_TAC `n = MAX N2 (MAX N3 N5)` THEN
  SUBGOAL_THEN `N2 <= (n:num) /\ N3 <= n /\ N5 <= n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "N5" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `&0`) (K ALL_TAC))) THEN
  REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET W(n:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K:B->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "K" THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `U = IMAGE ((H:num->real^3->A) n) {y | &1 / &2 < norm y}` THEN
  SUBGOAL_THEN `IMAGE ((phi:num->B->A) n) X SUBSET U` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    USE_THEN "N2" (MP_TAC o SPECL [`n:num`; `z:B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(X:B->bool) SUBSET mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D` THEN
      UNDISCH_TAC `(z:B) IN X` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[GSYM P2HN_VBALL_EQ] THEN
    DISCH_TAC THEN
    USE_THEN "N3" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `(phi:num->B->A) n z`) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[p3_horn_set; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[REAL_ARITH `&1 <= x ==> &1 / &2 < x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) (rfs_vatlas (V n) (t n))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `(t:num->real) n`] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
        can (find_term (fun t -> t = `psi:A->B`)) (concl th) && not (is_forall (concl th)))) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `(t:num->real) n`; `en:real`; `(H:num->real^3->A) n`] P2HN_HORN_ORIENTABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) X (subtopology (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) U) (restrict_atlas (rfs_vatlas (V n) (t n)) U) (IMAGE ((phi:num->B->A) n) X) (phi n) (psi:A->B)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `W(n:num):B->bool`;
      `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
      `IMAGE ((phi:num->B->A) n) (W n)`; `(phi:num->B->A) n`; `psi:A->B`; `X:B->bool`]
      MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
      `U:A->bool`; `IMAGE ((phi:num->B->A) n) X`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `X:B->bool`; `psi:A->B`; `(phi:num->B->A) n`]
      P2CO_DIFFEO_SUBTOP) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE ((phi:num->B->A) n) X INTER U = IMAGE (phi n) X /\
                  IMAGE (psi:A->B) (IMAGE (phi n) X) = X` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE ((phi:num->B->A) n) X SUBSET U` THEN SET_TAC[];
        REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
        MATCH_MP_TAC(SET_RULE `(!x:B. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
        FIRST_ASSUM(MP_TAC o el 4 o CONJUNCTS o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
          can (find_term (fun t -> t = `W(n:num):B->bool`)) (concl th) &&
          can (find_term (fun t -> t = `psi:A->B`)) (concl th) && not (is_forall (concl th)))) THEN
        UNDISCH_TAC `(X:B->bool) SUBSET W(n:num)` THEN SET_TAC[]];
      DISCH_THEN(ACCEPT_TAC o MATCH_MP MFD_DIFFEO_SYM)];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:A`,`:B`; `:B`,`:A`; `:3`,`:N`] P2B_ORIENTABLE_EMBED) THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) U`;
    `restrict_atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) U`;
    `IMAGE ((phi:num->B->A) n) X`; `(phi:num->B->A) n`; `psi:A->B`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The slice necks of the kappa-solution limit of MT p. 292.  A connected    *)
(* limit satisfies p2hn_lpack without restriction (P2HN_LPACK_CONNECTED);    *)
(* for the kappa-solution limit of Thm 11.8 part 2 (connected), Claim 11.35  *)
(* on [-t',0] for every t' and P2HN_LIMIT_NECKS_AT give necks at every point *)
(* at every time s <= 0 (P2HN_KSOL_SLICE_NECKS), the neck hypothesis of      *)
(* P2B_KAPPA_NECKS_ROUND_L_FIX.                                              *)
(* ========================================================================= *)

let P2HN_LPACK_CONNECTED = prove
 (`?eps0. &0 < eps0 /\
     !C1 eps1 Lc Qb
      (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      x t (top:B topology) atlas g xl T0.
        &0 < eps1 /\ eps1 <= eps0 /\
        p2hn_spk (C1,eps1,Lc,Qb) V x t /\
        (!n. apx_sphere_sep (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))) /\
        p3_flow_limit V x t (\n. rfs_vscalar (V n) (t n) (x n)) (top,atlas) g xl T0 /\
        (!s. --T0 < s /\ s <= &0
             ==> mfd_complete (top,atlas) (g s) /\
                 (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
        (!a. --T0 < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                    ==> mfd_rm_norm atlas (g s) y <= K) /\
        connected_space top
        ==> ?W phi. p2hn_lpack T0 V x t (top,atlas) g xl W phi`,
  X_CHOOSE_THEN `epsN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lnk"))
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_LIMIT_NECKS) THEN
  X_CHOOSE_THEN `epsT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "two"))
    (INST_TYPE [`:B`,`:A`] P2HN_TWO_ENDS) THEN
  EXISTS_TAC `min epsN (min epsT (&1 / &4)) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `T0:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sep")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cs")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN
    REWRITE_TAC[p2hn_spk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `n:num` o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\ smooth_manifold_atlas top atlas /\
                xl IN topspace top /\ &0 < T0 /\
                (!a. --T0 < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t (\n. rfs_vscalar (V n) (t n) (x n)) (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B) T0` THEN
    REWRITE_TAC[p3_flow_limit] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `T0:real`] P2HN_UPTO_RIEMANNIAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "riem") THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_FLOW_LIMIT_ON o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p3_flow_limit")) (concl th))) THEN
  REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A` (LABEL_TAC "fl"))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0)) /\ mfd_complete (top,atlas) (g (&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "riem" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "cs" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN topspace (top:B topology) ==> ?e. rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) (&2 * eps1) z e` (LABEL_TAC "nks") THENL
   [USE_THEN "lnk" (MP_TAC o SPECL
     [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `{s | --T0 < s /\ s <= &0}`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
      `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&2 * eps1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sphere_sep (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2B_SEP_FROM_FLOW_LIMIT) THEN
    MAP_EVERY EXISTS_TAC
     [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`;
      `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
      `g:real->B->real^3^3`; `xl:B`; `T0:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    FIRST_ASSUM(MP_TAC o SPECL [`k:num`; `(t:num->real) k`] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) k` THEN
    UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN
    REWRITE_TAC[p2hn_spk] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "nks" (MP_TAC o SPEC `xl:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ex:real^3->B`) THEN
  USE_THEN "two" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `(g:real->B->real^3^3) (&0)`; `&2 * eps1`; `xl:B`; `ex:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[p2hn_lpack] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  USE_THEN "cs" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "riem" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SIMP_TAC[]);;

let P2HN_KSOL_SLICE_NECKS = prove
 (`!u:A->bool w:B->bool.
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C1 eps1 Lc Qb
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t (top:B topology) atlas g xl kappa.
              &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\
              p2hn_spk (C1,eps1,Lc,Qb) V x t /\
              (!n. apx_sphere_sep (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))) /\
              (!Tl. &0 < Tl
                    ==> p3_flow_limit V x t (\n. rfs_vscalar (V n) (t n) (x n))
                                      (top,atlas) g xl Tl) /\
              p2b_kappa_solution kappa (top,atlas) g
              ==> !s z. s <= &0 /\ z IN topspace top
                        ==> ?e. rfs_neck (top,atlas) (g s) (&2 * eps1) z e`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_1135_ALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `epsA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all"))) THEN
  X_CHOOSE_THEN `epsL:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lpc"))
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_LPACK_CONNECTED) THEN
  X_CHOOSE_THEN `epsN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lna"))
    (INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_LIMIT_NECKS_AT) THEN
  EXISTS_TAC `min epsA (min epsL (min epsN (&1 / &8)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `kappa:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:B`] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
  ABBREV_TAC `T0 = --s + &1` THEN
  SUBGOAL_THEN `&0 < T0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "lpc" (MP_TAC o SPECL
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `T0:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN ASM_CASES_TAC `a <= &0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th) &&
        can (find_term (fun t -> t = `a:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      EXISTS_TAC `&0` THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A` ASSUME_TAC)) THEN
  USE_THEN "all" (MP_TAC o SPECL
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`; `T0:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `--s`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "c35") THEN
  UNDISCH_TAC `p2hn_lpack T0 V (x:num->A) t (top:B topology,atlas) g xl W phi` THEN
  REWRITE_TAC[p2hn_lpack] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "cplt")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ends"))))))) THEN
  USE_THEN "lna" (MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `{s | --T0 < s /\ s <= &0}`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `eps1:real`; `&2 * eps1`; `s:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN SIMP_TAC[p2hn_spk];
      ASM_REAL_ARITH_TAC;
      USE_THEN "cplt" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "cplt" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `K:B->bool` THEN DISCH_TAC THEN
      USE_THEN "c35" (MP_TAC o SPEC `K:B->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `N:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N")))) THEN
      MAP_EVERY EXISTS_TAC [`rho:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:B`] THEN STRIP_TAC THEN
      USE_THEN "N" (MP_TAC o SPECL [`n:num`; `y:B`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:B`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* MT pp. 291-292, the round limit and the transfer back.  For a horn        *)
(* sequence with the blow-up hypotheses, the backward hypothesis holds for   *)
(* all times (P2HN_BACK_ALL), Thm 11.8 part 2 gives a kappa-solution limit   *)
(* along a subsequence, whose slices are necks everywhere                    *)
(* (P2HN_KSOL_SLICE_NECKS) and which is in the class p2b_ksep                *)
(* (P2B_SEP_FROM_FLOW_LIMIT, P2HN_LIMIT_LORIENT);                            *)
(* P2B_KAPPA_NECKS_ROUND_L_FIX gives an evolving dl'-neck of length 3 at     *)
(* (xl,0), P2B_NECK_OPEN_L and P2HN_NECK_LIMIT give evolving dl'-necks of    *)
(* length 2 at (x_n,t_n) for n large, which are evolving dl-necks inside the *)
(* horns (P2HN_SEQ_NECK).                                                    *)
(* ========================================================================= *)

let P2HN_SEQ_NECK = prove
 (`!u:A->bool w:B->bool.
     P2C_THM_11_8_VIEW_STATEMENT u w /\ P2C_REQ_CAP_FIX_STATEMENT u w /\
     P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w /\ P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps mu C1 eps1 Lc Qb r0 en
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t H dl.
             &1 < C /\ &0 < eps /\ eps <= eps0 /\
             &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\ &0 < dl /\
             p2c_vblowup_seq (C,eps,pi / &6000,r0,mu) V x t /\
             (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
             (!A. ?N. !n. N <= n
                          ==> compact_in (rfs_vtop (V n) (t n))
                                (rfs_vtop (V n) (t n) closure_of
                                 rfs_vball (V n) (t n) (x n)
                                   (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
             p2hn_spk (C1,eps1,Lc,Qb) V x t /\
             (!n. p3_horn (V n) (t n) en (H n)) /\
             (!A. &0 < A
                  ==> ?N. !n. N <= n
                              ==> rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                                  SUBSET p3_horn_set (H n))
             ==> ?n e. rfs_evolving_neck (V n) dl (x n) (t n) (&2) e /\
                       IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set (H n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2HN_BACK_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eB:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2HN_118_KSOL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e8:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ks"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2HN_KSOL_SLICE_NECKS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sn"))) THEN
  UNDISCH_TAC `P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a5l"))) THEN
  X_CHOOSE_THEN `eI:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nib"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_IN_BALL) THEN
  EXISTS_TAC `min eB (min e8 (min eS (eA / &2)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`C:real`; `eps:real`; `mu:real`; `C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `r0:real`; `en:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `H:num->real^3->A`; `dl:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  (* the backward hypothesis for all times, and the kappa-solution limit *)
  USE_THEN "ball" (MP_TAC o SPECL
   [`C:real`; `eps:real`; `mu:real`; `C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `r0:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  USE_THEN "ks" (MP_TAC o SPECL
   [`C:real`; `eps:real`; `pi / &6000`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `p2hn_spk (C1,eps1,Lc,Qb) (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)) (\n. (x:num->A) (sub n)) (\n. (t:num->real) (sub n))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_SPK_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `connected_space (top:B topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution (pi / &6000) (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN SIMP_TAC[p2hn_spk];
    ALL_TAC] THEN
  USE_THEN "sn" (MP_TAC o SPECL
   [`C1:real`; `eps1:real`; `Lc:real`; `Qb:real`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
    `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
    `xl:B`; `pi / &6000`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN(LABEL_TAC "kn") THEN
  SUBGOAL_THEN `!A. &0 < A
                    ==> ?N. !n. N <= n
                                ==> rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)) (t (sub n)) ((x:num->A) (sub n))
                                      (A * inv(sqrt(rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))))
                                    SUBSET p3_horn_set ((H:num->real^3->A) (sub n))`
  (LABEL_TAC "hbs") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `A:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn_set")) (concl th) &&
      not(can (find_term (fun t -> t = `sub:num->num`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P2HN_SUBSEQ_GE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_regular_view")) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 && not(is_imp(snd(dest_forall(concl th)))))) THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o el 0 o CONJUNCTS o
      GEN_REWRITE_RULE I [p2c_regular_view]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (x:num->A) n IN topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))` ASSUME_TAC THENL
   [UNDISCH_TAC `p2hn_spk (C1,eps1,Lc,Qb) V (x:num->A) t` THEN SIMP_TAC[p2hn_spk];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_ksep (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[p2b_ksep] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2B_SEP_FROM_FLOW_LIMIT) THEN
      MAP_EVERY EXISTS_TAC
       [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
        `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`;
        `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)) (t (sub n)) ((x:num->A) (sub n))`;
        `g:real->B->real^3^3`; `xl:B`; `&1`] THEN
      ASM_SIMP_TAC[REAL_LT_01] THEN X_GEN_TAC `k:num` THEN
      FIRST_ASSUM(MP_TAC o SPECL [`(sub:num->num) k`; `(t:num->real) ((sub:num->num) k)`] o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) ((sub:num->num) k)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(INST_TYPE [`:B`,`:B`; `:A`,`:A`] P2HN_LIMIT_LORIENT) THEN
      MAP_EVERY EXISTS_TAC
       [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
        `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`;
        `g:real->B->real^3^3`; `xl:B`; `&1`; `en:real`; `\n. (H:num->real^3->A) ((sub:num->num) n)`] THEN
      ASM_SIMP_TAC[REAL_LT_01; REAL_LE_REFL; P2HN_EUCLID_ORIENTABLE]];
    ALL_TAC] THEN
  ABBREV_TAC `dl' = min dl (min eI (&1 / &8))` THEN
  SUBGOAL_THEN `&0 < dl' /\ dl' <= dl /\ dl' <= eI /\ dl' < &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "a5l" (MP_TAC o SPECL [`&2 * eps1`; `pi / &6000`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`dl':real`; `&3`; `&0`; `xl:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_flow_limit")) (concl th))) THEN
    REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e0:real^3->B`) THEN
  MP_TAC(REWRITE_RULE[P2B_NECK_OPEN_L_STATEMENT] (ISPECL [`(:B)`; `(:A)`] P2B_NECK_OPEN_L)) THEN
  DISCH_THEN(MP_TAC o SPECL [`p2b_kview (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)`;
    `dl':real`; `xl:B`; `&0`; `&3`; `&2`; `e0:real^3->B`]) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[p2b_kview] THEN
    REWRITE_TAC[GSYM p2b_kview] THEN MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN
    EXISTS_TAC `pi / &6000` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "op") THEN
  MP_TAC(ISPECL
   [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
    `\n. (x:num->A) ((sub:num->num) n)`; `\n. (t:num->real) ((sub:num->num) n)`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)) (t (sub n)) ((x:num->A) (sub n))`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `pi / &6000`; `dl':real`; `&3`; `e0:real^3->B`;
    `\(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t' (y:A). ?e'. rfs_evolving_neck V' dl' y t' (&2) e'`]
    P2HN_NECK_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM p2b_kview] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[p2b_kview] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "hbs" (MP_TAC o SPEC `&2 * (inv dl' + &5)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  USE_THEN "N1" (MP_TAC o SPEC `MAX N1 N2`) THEN REWRITE_TAC[ARITH_RULE `N1 <= MAX N1 N2`] THEN
  DISCH_THEN(X_CHOOSE_TAC `e1:real^3->A`) THEN
  USE_THEN "N2" (MP_TAC o SPEC `MAX N1 N2`) THEN REWRITE_TAC[ARITH_RULE `N2 <= MAX N1 N2`] THEN
  ABBREV_TAC `m = (sub:num->num) (MAX N1 N2)` THEN DISCH_TAC THEN
  EXISTS_TAC `m:num` THEN EXISTS_TAC `e1:real^3->A` THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m),rfs_vatlas (V m) (t m)) (rfs_vmetric (V m) (t m)) dl' ((x:num->A) m) e1` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_EVNECK_SLICE THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2HN_REG_EVNECK_MONO THEN
    EXISTS_TAC `dl':real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e1:real^3->A) (rfs_neck_dom dl')` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m) ((x:num->A) m)
                ((&2 * (inv dl' + &5)) * inv(sqrt(rfs_vscalar (V m) (t m) (x m))))` THEN
  ASM_REWRITE_TAC[P2HN_VBALL_EQ; P2BN_RFS_VSCALAR; GSYM REAL_MUL_ASSOC] THEN
  USE_THEN "nib" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2HN_REGULAR_HAUSDORFF THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `(t:num->real) m`] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) m` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Tools for the blow-up sequence of MT                                     *)
(* Claim 11.32: shortening evolving necks, congruence of necks and          *)
(* canonical neighbourhoods for views that agree up to the time considered  *)
(* (the maximal extension agrees with the history view before the horizon), *)
(* and properness of R on Omega from Lemma 11.30 (the part of Omega_rho in  *)
(* components meeting it misses the horns, so lies in the compact core).    *)
(* ========================================================================= *)

(* Shortening an evolving neck: the statement of P3H_EVNECK_SHORTEN          *)
(* (pc_p3_c177a; also P3E_EVNECK_SHORTEN), proved here to keep those units   *)
(* out of this closure.                                                      *)

let P2HN_EVNECK_SHORTEN = prove
 (`!V eps (x:A) t a b e.
     rfs_evolving_neck V eps x t a e /\ &0 < b /\ b <= a
     ==> rfs_evolving_neck V eps x t b e`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `x:A`; `t:real`; `a:real`; `b:real`; `e:real^3->A`] THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_persists; rfs_close_fam; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) (G t) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                          (G t) eps x e` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t - b / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) (G t) x` THEN
    ASM_REWRITE_TAC[REAL_ARITH `t - a <= t - b <=> b <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Views that agree up to time t have the same necks and canonical          *)
(* neighbourhoods at time t.                                                  *)

let P2HN_EVNECK_CONG = prove
 (`!(V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    V2 eps x t len e.
     (!r. r <= t ==> rfs_vtop V1 r = rfs_vtop V2 r /\ rfs_vatlas V1 r = rfs_vatlas V2 r /\
                     rfs_vmetric V1 r = rfs_vmetric V2 r)
     ==> (rfs_evolving_neck V1 eps x t len e <=> rfs_evolving_neck V2 eps x t len e)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  MAP_EVERY X_GEN_TAC
   [`TM1:real->A topology`; `AT1:real->((A->bool)#(A->real^3))->bool`; `G1:real->A->real^3^3`;
    `TM2:real->A topology`; `AT2:real->((A->bool)#(A->real^3))->bool`; `G2:real->A->real^3^3`;
    `eps:real`; `x:A`; `t:real`; `len:real`; `e:real^3->A`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
    (ASSUME_TAC o SYM))) THEN
  REWRITE_TAC[rfs_evolving_neck] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `rfs_neck ((TM1:real->A topology) t,(AT1:real->((A->bool)#(A->real^3))->bool) t) (G1 t) eps x e` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < len` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT1:real->((A->bool)#(A->real^3))->bool) t) (G1 t) x` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar ((AT1:real->((A->bool)#(A->real^3))->bool) t) (G1 t) x` THEN
  BINOP_TAC THENL
   [REWRITE_TAC[rfs_persists] THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `TM2:real->A topology`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
    SUBGOAL_THEN `!s. --len < s /\ s <= &0
                      ==> (AT1:real->((A->bool)#(A->real^3))->bool) (t + s / R) = AT2 (t + s / R) /\
                          (G1:real->A->real^3^3) (t + s / R) = G2 (t + s / R)`
    ASSUME_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `t + s / R <= t` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `y <= &0 ==> t + y <= t`) THEN
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t + s / R` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `TM2:real->A topology`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^3`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

let P2HN_CANON_AT_CONG = prove
 (`!(V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    V2 C eps x t.
     (!r. r <= t ==> rfs_vtop V1 r = rfs_vtop V2 r /\ rfs_vatlas V1 r = rfs_vatlas V2 r /\
                     rfs_vmetric V1 r = rfs_vmetric V2 r)
     ==> (p3_canon_at V1 C eps x t <=> p3_canon_at V2 C eps x t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                `V2:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                `eps:real`; `x:A`; `t:real`; `&1`] P2HN_EVNECK_CONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `r:real`)) (concl th))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`,
           `V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`) THEN
  SPEC_TAC(`V2:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`,
           `V2:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[p3_canon_at; rfs_strong_canonical; rfs_strong_neck]);;

(* Lemma 11.30 gives compact sublevel sets of R on Omega.                    *)

let P2HN_OMEGA_PROPER = prove
 (`!u:A->bool.
     P2C_LEMMA_11_30_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps (hs:(A)rfs_history) r0 gl.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
              apx_sphere_sep (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
              rfs_pinched (rfs_view hs) /\
              (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                     inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                     ==> p3_canon_at (rfs_view hs) C eps x t) /\
              rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
              open_in (hs_top hs (hs_count hs)) (p3_omega hs)
              ==> !c. compact_in (hs_top hs (hs_count hs))
                        {x | x IN p3_omega hs /\
                             mfd_scalar (hs_atlas hs (hs_count hs)) gl x <= c}`,
  GEN_TAC THEN REWRITE_TAC[P2C_LEMMA_11_30_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l30"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`; `gl:A->real^3^3`] THEN
  STRIP_TAC THEN X_GEN_TAC `c:real` THEN
  ABBREV_TAC `rho = min (r0 / &2) (inv(sqrt(abs c + &1)))` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < r0 /\ c <= inv(rho pow 2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(abs c + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(sqrt(abs c + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "rho" THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < rho /\ rho <= inv(sqrt(abs c + &1))` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "rho" THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs c + &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `inv(abs c + &1) = inv(sqrt(abs c + &1)) pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_INV] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  USE_THEN "l30" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                                  `gl:A->real^3^3`; `rho:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num->bool` (X_CHOOSE_THEN `H:num->real^3->A`
    (X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rho SUBSET (K:A->bool) /\ K SUBSET p3_omega (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:A) IN p3_omega hs /\ y IN topspace (hs_top hs (hs_count (hs:(A)rfs_history)))` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:A) IN p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rho` THEN
        REWRITE_TAC[p3_omega_rho; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:A) IN p3_omega hs` THEN REWRITE_TAC[p3_omega; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:A) IN UNIONS {U | U IN connected_components_of (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\ ~(U INTER p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rho = {})}` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `connected_component_of (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) (y:A)` THEN
        SUBGOAL_THEN `(y:A) IN topspace (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER]; ALL_TAC] THEN
        ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        SUBGOAL_THEN `(y:A) IN connected_component_of (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) y` ASSUME_TAC THENL
         [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL]; ALL_TAC] THEN
        CONJ_TAC THENL [EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_UNION] THEN
      MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `S:A->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:A) IN p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rho` THEN
      UNDISCH_TAC `(y:A) IN S` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {U | U IN connected_components_of (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\ ~(U INTER p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega (hs:(A)rfs_history)) gl rho = {})}` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `U:A->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`] P2HN_MAXEXT_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed_in (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) {x | x IN p3_omega hs /\ mfd_scalar (hs_atlas hs (hs_count hs)) (gl:A->real^3^3) x <= c}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`mfd_scalar (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) (restrict_metric (hs_atlas hs (hs_count hs)) (p3_omega (hs:(A)rfs_history)) (gl:A->real^3^3))`;
       `subtopology (hs_top hs (hs_count hs)) (p3_omega (hs:(A)rfs_history))`; `euclideanreal`; `{r:real | r <= c}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `(s:A->bool) = t ==> closed_in (top:A topology) s ==> closed_in top t`) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
    ASM_CASES_TAC `(y:A) IN p3_omega hs` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) {x | x IN p3_omega hs /\ mfd_scalar (hs_atlas hs (hs_count hs)) (gl:A->real^3^3) x <= c}` MP_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `K:A->bool` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega (hs:(A)rfs_history)) (gl:A->real^3^3) rho` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; p3_omega_rho; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]]);;

(* ========================================================================= *)
(* The maximal extension as a view (MT                                      *)
(* Claim 11.32): it agrees with the history view before the horizon, its   *)
(* slices before the horizon are compact, sphere separating, empty before  *)
(* time 0, and it has strong (4C, Kc K eps)-canonical neighbourhoods above  *)
(* r0^-2 at all times up to the horizon (P2HN_MAXEXT_CANON: before the     *)
(* horizon from the history by P2HN_CANON_AT_CONG and P2HN_CANON_MONO, at  *)
(* the horizon from the typed Thm 11.19 applied with (2C, K eps)).          *)
(* ========================================================================= *)

let P2HN_MAXEXT_AGREE = prove
 (`!(hs:(A)rfs_history) Om gl t.
     t < rfs_horizon hs
     ==> !r. r <= t
             ==> rfs_vtop (p3_maxext hs Om gl) r = rfs_vtop (rfs_view hs) r /\
                 rfs_vatlas (p3_maxext hs Om gl) r = rfs_vatlas (rfs_view hs) r /\
                 rfs_vmetric (p3_maxext hs Om gl) r = rfs_vmetric (rfs_view hs) r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p3_maxext; rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2HN_MAXEXT_HORIZON = prove
 (`!(hs:(A)rfs_history) Om gl.
     rfs_vtop (p3_maxext hs Om gl) (rfs_horizon hs) = subtopology (hs_top hs (hs_count hs)) Om /\
     rfs_vatlas (p3_maxext hs Om gl) (rfs_horizon hs) =
       restrict_atlas (hs_atlas hs (hs_count hs)) Om /\
     rfs_vmetric (p3_maxext hs Om gl) (rfs_horizon hs) =
       restrict_metric (hs_atlas hs (hs_count hs)) Om gl`,
  REWRITE_TAC[p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2HN_MAXEXT_BEFORE = prove
 (`!(hs:(A)rfs_history) Om gl s.
     ~(s = rfs_horizon hs)
     ==> rfs_vtop (p3_maxext hs Om gl) s = rfs_top_at hs s /\
         rfs_vatlas (p3_maxext hs Om gl) s = rfs_atlas_at hs s /\
         rfs_vmetric (p3_maxext hs Om gl) s = rfs_metric_at hs s`,
  SIMP_TAC[p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2HN_MAXEXT_SLICES = prove
 (`!(hs:(A)rfs_history) Om gl.
     rfs_history_ok hs /\
     (!k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k))
     ==> &0 < rfs_horizon hs /\
         (!s. s < &0 ==> rfs_vtop (p3_maxext hs Om gl) s = discrete_topology {}) /\
         (!s. s < rfs_horizon hs ==> compact_space (rfs_vtop (p3_maxext hs Om gl) s)) /\
         (!s. ~(s = rfs_horizon hs)
              ==> apx_sphere_sep (rfs_vtop (p3_maxext hs Om gl) s)
                                 (rfs_vatlas (p3_maxext hs Om gl) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` P2HN_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k <= hs_count hs ==> compact_space (hs_top hs k:A topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(s = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P2HN_MAXEXT_BEFORE; rfs_top_at; rfs_live] THEN
    SUBGOAL_THEN `~(&0 <= s /\ s < hs_time (hs:(A)rfs_history) (hs_count hs + 1))`
      (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(s = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P2HN_MAXEXT_BEFORE; rfs_top_at] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFS_SLAB) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) s` THEN REWRITE_TAC[rfs_live; rfs_horizon] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SIMP_TAC[]];
      REWRITE_TAC[COMPACT_SPACE_DISCRETE_TOPOLOGY; FINITE_EMPTY]];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[P2HN_MAXEXT_BEFORE; rfs_top_at; rfs_atlas_at] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFS_SLAB) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) s` THEN REWRITE_TAC[rfs_live; rfs_horizon] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SIMP_TAC[]];
      REWRITE_TAC[P2B_APX_SPHERE_SEP_EMPTY]]]);;

let P2HN_CANON_FROM_TYPED = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C en ec x t.
     p2c_regular_view V /\ &0 < en /\ en <= ec /\ p3_canon_typed V C en ec x t
     ==> p3_canon_at V C ec x t`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`; `G:real->A->real^3^3`;
    `C:real`; `en:real`; `ec:real`; `x:A`; `t:real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `p3_canon_typed (TM,AT,G) C en ec (x:A) t` THEN
  REWRITE_TAC[p3_canon_typed; p3_canon_at; rfs_strong_canonical; rfs_vtop; rfs_vatlas;
              rfs_vmetric] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom ec)` THEN DISJ1_TAC THEN
    EXISTS_TAC `e:real^3->A` THEN REWRITE_TAC[rfs_strong_neck] THEN
    MATCH_MP_TAC P2HN_REG_EVNECK_MONO THEN EXISTS_TAC `en:real` THEN
    ASM_REWRITE_TAC[GSYM rfs_strong_neck];
    EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]]);;

let P2HN_MAXEXT_CANON = prove
 (`!u:A->bool.
     P2C_THM_11_19_STATEMENT u /\ P2C_MAXEXT_REGULAR_STATEMENT u
     ==> ?K Kc eps0. &1 <= K /\ &2 <= Kc /\ &0 < eps0 /\
           !C eps (hs:(A)rfs_history) r0 gl.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
              rfs_pinched (rfs_view hs) /\
              (!k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k)) /\
              (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                     inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                     ==> p3_canon_at (rfs_view hs) C eps x t) /\
              rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
              ==> open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
                  p2c_regular_view (p3_maxext hs (p3_omega hs) gl) /\
                  !y s. s <= rfs_horizon hs /\
                        y IN topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s) /\
                        inv(r0 pow 2) < rfs_vscalar (p3_maxext hs (p3_omega hs) gl) s y
                        ==> p3_canon_at (p3_maxext hs (p3_omega hs) gl) (&4 * C)
                                        (Kc * K * eps) y s`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "mreg")) THEN
  REWRITE_TAC[P2C_THM_11_19_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `e19:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t19"))))) THEN
  X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eK:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cm")))) (INST_TYPE [`:A`,`:A`] P2HN_CANON_MONO) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `Kc:real`; `min (e19 / K) (eK / (Kc * K))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`; `gl:A->real^3^3`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < K * eps /\ K * eps <= e19 /\ Kc * K * eps <= eK /\ K * eps <= Kc * K * eps /\
                &2 * K * eps <= Kc * K * eps /\ eps <= K * eps`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= e19 / K` THEN UNDISCH_TAC `eps <= eK / (Kc * K)` THEN
    SUBGOAL_THEN `&0 < K /\ &0 < Kc * K` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 < K * eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&1`; `Kc:real`; `K * eps`] REAL_LE_RMUL) THEN
    MP_TAC(SPECL [`&2`; `Kc:real`; `K * eps`] REAL_LE_RMUL) THEN
    MP_TAC(SPECL [`&1`; `K:real`; `eps:real`] REAL_LE_RMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `&2 <= Kc ==> &1 <= Kc`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `p3_omega(hs:(A)rfs_history)`; `gl:A->real^3^3`]
    P2HN_MAXEXT_SLICES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* Omega open, the maximal extension regular *)
  SUBGOAL_THEN `open_in (hs_top hs (hs_count hs)) (p3_omega (hs:(A)rfs_history))` ASSUME_TAC THENL
   [USE_THEN "t19" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (p3_maxext hs (p3_omega hs) (gl:A->real^3^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_MAXEXT_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_MAXEXT_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace (rfs_top_at hs t) /\
                      inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                      ==> p3_canon_at (p3_maxext hs (p3_omega hs) (gl:A->real^3^3)) C eps (x:A) t`
  (LABEL_TAC "hm") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p3_maxext hs (p3_omega hs) (gl:A->real^3^3)`; `rfs_view (hs:(A)rfs_history)`;
                   `C:real`; `eps:real`; `x:A`; `t:real`] P2HN_CANON_AT_CONG) THEN
    ANTS_TAC THENL [MATCH_MP_TAC P2HN_MAXEXT_AGREE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace (rfs_top_at hs t) /\
                      inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                      ==> p3_canon_at (rfs_view (hs:(A)rfs_history)) (&2 * C) (K * eps) (x:A) t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p3_maxext hs (p3_omega hs) (gl:A->real^3^3)`; `rfs_view (hs:(A)rfs_history)`;
                   `&2 * C`; `K * eps`; `x:A`; `t:real`] P2HN_CANON_AT_CONG) THEN
    ANTS_TAC THENL [MATCH_MP_TAC P2HN_MAXEXT_AGREE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "cm" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`] THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "t19" (MP_TAC o SPECL [`&2 * C`; `K * eps`; `hs:(A)rfs_history`; `r0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `gl:A->real^3^3` o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "typ") THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `s:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = rfs_horizon (hs:(A)rfs_history)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`] P2HN_MAXEXT_SLICE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN p3_omega hs` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))` THEN
      ASM_REWRITE_TAC[P2HN_MAXEXT_HORIZON];
      ALL_TAC] THEN
    MATCH_MP_TAC P2HN_CANON_FROM_TYPED THEN EXISTS_TAC `&2 * K * eps` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * C = &2 * &2 * C` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "typ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `inv (r0 pow 2) < rfs_vscalar (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (y:A)` THEN
    ASM_SIMP_TAC[P2BN_RFS_VSCALAR; P2HN_MAXEXT_HORIZON];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace (rfs_top_at hs s) /\ &0 <= s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s)` THEN
    ASM_SIMP_TAC[P2HN_MAXEXT_BEFORE] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:A) IN topspace (rfs_top_at hs s)` THEN REWRITE_TAC[rfs_top_at; rfs_live] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  USE_THEN "cm" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`] THEN
  SUBGOAL_THEN `compact_space (rfs_vtop (p3_maxext hs (p3_omega hs) (gl:A->real^3^3)) s)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_space")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "hm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `inv (r0 pow 2) < rfs_vscalar (p3_maxext hs (p3_omega hs) gl) s (y:A)` THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `p3_omega(hs:(A)rfs_history)`; `gl:A->real^3^3`; `s:real`]
    P2HN_MAXEXT_AGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  REWRITE_TAC[REAL_LE_REFL; P2BN_RFS_VSCALAR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The blow-up sequence of MT Claim 11.32,                                   *)
(* first part.  Noncollapsing at the horizon from strong necks, with a       *)
(* compact set (a sublevel set of R, by Lemma 11.30) in place of a compact  *)
(* slice (P2HN_EVNECK_NONCOLL_K), and the view facts of the maximal          *)
(* extension of one history satisfying the hypotheses of Thm 11.31           *)
(* (P2HN_HIST_PACK).                                                         *)
(* ========================================================================= *)

(* Noncollapsing near a strong neck centre in a slice with compact sublevel *)
(* sets.                                                                     *)

let P2HN_EVNECK_NONCOLL_K = prove
 (`?eps3. &0 < eps3 /\
     !V eps (x:A) t e s r K.
        p2c_regular_view V /\ rfs_strong_neck V eps x t e /\ eps <= eps3 /\
        t - inv(&2 * rfs_vscalar V t x) < s /\ s <= t /\
        compact_in (rfs_vtop V s) K /\
        rfs_vball V s x (&5 * inv(sqrt(rfs_vscalar V t x))) SUBSET K /\
        &0 < r /\ mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) x <= inv(r pow 2)
        ==> ?v. mfd_has_volume (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s)
                               (rfs_vball V s x r) v /\
                pi / &6000 * r pow 3 <= v`,
  MP_TAC(SPEC `&1 / &4` P2BN_NECK_SCALAR) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))) THEN
  EXISTS_TAC `min eps2 (&1 / &10)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `t:real`; `e:real^3->A`; `s:real`; `r:real`; `K:A->bool`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps (x:A) e /\
    rfs_close_fam (rfs_kreg eps) eps {s | --(&1) < s /\ s <= &0}
      (rfs_neck_dom eps) cylinder_flow
      (\s y. rfs_vscalar V t x %%
             rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                          (rfs_vmetric V (t + s / rfs_vscalar V t x)) y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_neck V eps (x:A) t e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `R = rfs_vscalar V t (x:A)` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
    ASM_MESON_TAC[P2BN_NECK_CENTRE_FACTS];
    ALL_TAC] THEN
  ABBREV_TAC `sg = (s - t) * R` THEN
  SUBGOAL_THEN `--(&1 / &2) < sg /\ sg <= &0 /\ t + sg / R = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `--inv(&2 * R) * R` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `--inv(&2 * R) * R = --(&1 / &2)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(R = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) < sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `t:real`; `&1`; `e:real^3->A`; `sg:real`]
   P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?z0. z0 IN sphere(vec 0:real^3,&1) /\ (e:real^3->A) z0 = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps (x:A) e` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z0:real^3) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` P2BN_NECK_CORE_DOM) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `z0:real^3`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ball(z0:real^3,&1 / &4) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  (* closeness at sigma *)
  UNDISCH_TAC
   `rfs_close_fam (rfs_kreg eps) eps {s | --(&1) < s /\ s <= &0}
      (rfs_neck_dom eps) cylinder_flow
      (\s y. R %% rfs_pullback (rfs_vatlas V (t + s / R)) (e:real^3->A)
                               (rfs_vmetric V (t + s / R)) y)` THEN
  REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `sg:real`))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "cl") THEN
  (* quadratic form bounds *)
  SUBGOAL_THEN
   `!y w. y IN ball(z0:real^3,&1 / &4)
          ==> w dot w <= R * (w dot (rfs_pullback (rfs_vatlas V s) (e:real^3->A)
                                                 (rfs_vmetric V s) y ** w)) /\
              R * (w dot (rfs_pullback (rfs_vatlas V s) e (rfs_vmetric V s) y ** w))
              <= &6 * (w dot w)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ &3 / &4 < norm y /\ norm y < &5 / &4`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN ball(z0,&1 / &4)` THEN REWRITE_TAC[IN_BALL] THEN
      UNDISCH_TAC `norm(z0:real^3) = &1` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_kreg eps`; `rfs_neck_dom eps`; `cylinder_flow sg`;
                   `\y. R %% rfs_pullback (rfs_vatlas V s) (e:real^3->A) (rfs_vmetric V s) y`;
                   `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
        EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow sg)
             (\y. R %% rfs_pullback (rfs_vatlas V s) (e:real^3->A) (rfs_vmetric V s) y) y)
      <= &1 / &10`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
       [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN USE_THEN "cl" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
         [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]]];
      ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    ABBREV_TAC `dd = sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow sg)
                   (\y. R %% rfs_pullback (rfs_vatlas V s) (e:real^3->A)
                                          (rfs_vmetric V s) y) y)` THEN
    ABBREV_TAC `A0 = (w:real^3) dot (cylinder_flow sg y ** w)` THEN
    MP_TAC(SPECL [`sg:real`; `y:real^3`; `w:real^3`] P2HN_CYL_QF_NUM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= (w:real^3) dot w` ASSUME_TAC THENL
     [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `dd * A0 <= &1 / &10 * A0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scale bound r R^(1/2) <= 5 *)
  SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop V s)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` (MP_TAC o CONJUNCT1 o CONJUNCT2)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&5 / &12 * R <= rfs_vscalar V s (x:A)` ASSUME_TAC THENL
   [USE_THEN "ns" (MP_TAC o SPECL
     [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `eps:real`; `x:A`; `t:real`; `&1`; `e:real^3->A`; `sg:real`; `z0:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN
      MATCH_MP_TAC(SET_RULE `!a s t. (a:real^3) IN s /\ s SUBSET t ==> a IN t`) THEN
      EXISTS_TAC `ball(z0:real^3,&1 / &4)` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 / &3 <= &1 / (&1 - sg)` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &1 - sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&5 / &12 <= rfs_vscalar V s (x:A) / R` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r * sqrt R <= &5` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) s`; `x:A`] P2HN_SCALAR_ABS_LE_RM) THEN
    ASM_REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN DISCH_TAC THEN
    SUBGOAL_THEN `R <= &72 / &5 * inv(r pow 2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `r pow 2 * R <= &72 / &5` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r pow 2 * (&72 / &5 * inv(r pow 2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> a * (&72 / &5 * inv a) = &72 / &5`;
                     REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH_EQ; REAL_POS; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the ball of radius r lies in K *)
  SUBGOAL_THEN `rfs_vball V s (x:A) r SUBSET K` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vball V s (x:A) (&5 * inv(sqrt R))` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2HN_VBALL_EQ] THEN MATCH_MP_TAC RFA_MFD_BALL_MONO THEN
    SUBGOAL_THEN `&0 < sqrt R` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  (* the flat-ball argument *)
  REWRITE_TAC[P2HN_VBALL_EQ] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:real^3->A) z0 = x`)) THEN
  MATCH_MP_TAC P2HN_QF_NONCOLL THEN
  MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `R:real`; `K:A->bool`] THEN
  ASM_REWRITE_TAC[P2AP_BALL_SUBSET; GSYM P2HN_VBALL_EQ]);;

(* The maximal extension of a history with the hypotheses of Thm 11.31.     *)

let P2HN_HIST_PACK = prove
 (`!u:A->bool.
     P2C_THM_11_19_STATEMENT u /\ P2C_MAXEXT_REGULAR_STATEMENT u /\ P2C_LEMMA_11_30_STATEMENT u
     ==> ?K Kc eps0. &1 <= K /\ &2 <= Kc /\ &0 < eps0 /\
           !C eps (hs:(A)rfs_history) r0 gl.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
              rfs_pinched (rfs_view hs) /\
              (!k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k)) /\
              (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                     inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                     ==> p3_canon_at (rfs_view hs) C eps x t) /\
              rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
              ==> p2c_regular_view (p3_maxext hs (p3_omega hs) gl) /\
                  rfs_pinched (p3_maxext hs (p3_omega hs) gl) /\
                  (!s. s < &0 ==> rfs_vtop (p3_maxext hs (p3_omega hs) gl) s = discrete_topology {}) /\
                  (!s. apx_sphere_sep (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s)
                                      (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) s)) /\
                  (!s. s < rfs_horizon hs
                       ==> compact_space (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s)) /\
                  (!c. compact_in (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                         {y | y IN topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs)) /\
                              rfs_vscalar (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) y <= c}) /\
                  (!y s. s <= rfs_horizon hs /\
                         y IN topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s) /\
                         inv(r0 pow 2) < rfs_vscalar (p3_maxext hs (p3_omega hs) gl) s y
                         ==> p3_canon_at (p3_maxext hs (p3_omega hs) gl) (&4 * C)
                                         (Kc * K * eps) y s) /\
                  topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs)) = p3_omega hs /\
                  (!y. y IN p3_omega hs
                       ==> rfs_vscalar (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) y =
                           mfd_scalar (hs_atlas hs (hs_count hs)) gl y)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(SPEC `u:A->bool` P2HN_MAXEXT_CANON) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `e1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mc"))))))) THEN
  MP_TAC(SPEC `u:A->bool` P2HN_OMEGA_PROPER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "op"))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `Kc:real`; `min e1 e2`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`; `gl:A->real^3^3`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  USE_THEN "mc" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                                 `gl:A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `p3_omega(hs:(A)rfs_history)`; `gl:A->real^3^3`]
    P2HN_MAXEXT_SLICES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`] P2HN_MAXEXT_SLICE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[P2HN_MAXEXT_HORIZON] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2HN_PINCH_MAXEXT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN ASM_CASES_TAC `s = rfs_horizon (hs:(A)rfs_history)` THENL
     [ASM_REWRITE_TAC[P2HN_MAXEXT_HORIZON]; ASM_SIMP_TAC[]];
    X_GEN_TAC `c:real` THEN
    USE_THEN "op" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                                   `gl:A->real^3^3`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
    MATCH_MP_TAC(MESON[] `(s:A->bool) = t /\ t SUBSET u ==> compact_in top s ==> compact_in top t /\ t SUBSET u`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
      ASM_CASES_TAC `(y:A) IN p3_omega hs` THEN ASM_SIMP_TAC[P2BN_RFS_VSCALAR; P2HN_MAXEXT_HORIZON];
      SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`y:A`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[P2BN_RFS_VSCALAR; P2HN_MAXEXT_HORIZON]]);;

(* ========================================================================= *)
(* Claim 11.32 for a sequence of horn                                        *)
(* points (MT pp. 289-293).  P2HN_HORN_POINT: a horn point whose 5-ball lies *)
(* in a compact set is noncollapsed and persists backward along its strong   *)
(* neck.  P2HN_SEQ_FROM_HSEQ: for a p2hn_hseq sequence, Thm 10.2 bounds R    *)
(* above and P2HN_R_LOWER_NEAR bounds it below on the A-balls, which lie in  *)
(* the horns; so the sequence is a view blow-up sequence, Thm 11.1 gives a   *)
(* limit along a subsequence with bounded curvature at time 0, hence the     *)
(* bound R <= Qb Q on the A-balls (P2HN_Q0_FROM_LIMIT), and P2HN_SEQ_NECK    *)
(* gives an evolving neck of length 2 at some x n inside the horn.           *)
(* ========================================================================= *)

(* A horn point y, with its 5-ball inside a compact set K, is noncollapsed   *)
(* on all scales and persists backward for mu / max(Q,R(y)).                 *)

let P2HN_HORN_POINT = prove
 (`?eps3. &0 < eps3 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      en y t e K r0 mu Q.
        p2c_regular_view V /\ &0 < en /\ en <= eps3 /\ rfs_strong_neck V en y t e /\
        compact_in (rfs_vtop V t) K /\
        rfs_vball V t y (&5 * inv(sqrt(rfs_vscalar V t y))) SUBSET K /\
        &0 < mu /\ mu <= &1 /\ &0 < Q
        ==> p3_noncoll_at V (pi / &6000) r0 y t /\
            p2c_local_persist V y (t - mu * inv(max Q (rfs_vscalar V t y))) t`,
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))
    (INST_TYPE [`:A`,`:A`] P2HN_EVNECK_NONCOLL_K) THEN
  EXISTS_TAC `eps3:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `en:real`; `y:A`; `t:real`; `e:real^3->A`; `K:A->bool`; `r0:real`; `mu:real`; `Q:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) en (y:A) e` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_STRONG_NECK_SLICE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (rfs_vmetric V t)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o el 0 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3_noncoll_at] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "nc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`en:real`; `t:real`; `e:real^3->A`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> t - x < t`) THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[P2BN_RFS_VSCALAR] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; P2HN_VBALL_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> t - x < t`) THEN MATCH_MP_TAC REAL_POW_LT THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]]];
    REWRITE_TAC[p2c_local_persist] THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom en)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_strong_neck V en (y:A) t e` THEN
    REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT; P2BN_PERSISTS_ALT] THEN STRIP_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!b. b <= a /\ t - b < s ==> t - a < s`) THEN
    EXISTS_TAC `mu * inv(max Q (rfs_vscalar V t (y:A)))` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < rfs_vscalar V t (y:A)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[P2BN_RFS_VSCALAR]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(max Q (rfs_vscalar V t (y:A)))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC]]);;


(* Every point of a horn is the centre of a strong neck.                     *)

let P2HN_HORN_SET_NECK = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    th eps H y.
     p3_horn V th eps H /\ y IN p3_horn_set H ==> ?e. rfs_strong_neck V eps y th e`,
  REWRITE_TAC[p3_horn; p3_horn_set; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Balls of views lie in the topspace.                                       *)

let P2HN_VBALL_TOPSPACE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t x r y.
     y IN rfs_vball V t x r ==> y IN topspace (rfs_vtop V t)`,
  REWRITE_TAC[P2HN_VBALL_EQ; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]);;

(* Claim 11.32 for a horn sequence: an evolving neck of length 2 inside the  *)
(* horn at some x n.                                                         *)

let P2HN_SEQ_FROM_HSEQ = prove
 (`!u:A->bool w:B->bool.
     P2C_THM_11_1_VIEW_STATEMENT u w /\ P2C_THM_11_8_VIEW_STATEMENT u w /\
     P2C_REQ_CAP_FIX_STATEMENT u w /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT w /\
     P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT w /\ P2C_REQ_THM_10_2_VIEW_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C1 eps1 en Lc Mb
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            x t H dl.
              &1 < C1 /\ &0 < eps1 /\ eps1 <= eps0 /\ &0 < en /\ en <= eps1 /\
              &0 < dl /\ &0 < Lc /\
              p2hn_hseq (C1,eps1,en,Lc,Mb) V x t H /\
              (!n. Lc <= rfs_vscalar (V n) (t n) (x n))
              ==> ?n e. rfs_evolving_neck (V n) dl (x n) (t n) (&2) e /\
                        IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set (H n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2HN_SEQ_NECK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sq"))) THEN
  X_CHOOSE_THEN `eH:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bh"))
    (INST_TYPE [`:A`,`:A`] P2HN_HSEQ_BALL_IN_HORN) THEN
  UNDISCH_TAC `P2C_REQ_THM_10_2_VIEW_STATEMENT (u:A->bool)` THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP P2HN_R_LOWER_NEAR th) THEN
    MP_TAC(REWRITE_RULE[P2C_REQ_THM_10_2_VIEW_STATEMENT] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e102:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t102"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `eR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rl"))) THEN
  UNDISCH_TAC `P2C_THM_11_1_VIEW_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2C_THM_11_1_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e111:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t111"))) THEN
  X_CHOOSE_THEN `eP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hp"))
    (INST_TYPE [`:A`,`:A`] P2HN_HORN_POINT) THEN
  EXISTS_TAC `min eS (min eH (min e102 (min eR (min e111 eP))))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC
   [`C1:real`; `eps1:real`; `en:real`; `Lc:real`; `Mb:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `H:num->real^3->A`; `dl:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  (* A-balls in the horns *)
  USE_THEN "bh" (MP_TAC o SPECL [`C1:real`; `eps1:real`; `en:real`; `Lc:real`; `Mb:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `H:num->real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "hb") THEN
  UNDISCH_TAC `p2hn_hseq (C1,eps1,en,Lc,Mb) V (x:num->A) t H` THEN REWRITE_TAC[p2hn_hseq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "Qinf"))) THEN
  SUBGOAL_THEN `(!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) /\ rfs_pinched (V n) /\
                     (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {}) /\
                     (!s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s))) /\
                (!n. p3_horn (V n) (t n) en ((H:num->real^3->A) n) /\ (x:num->A) n IN p3_horn_set (H n) /\
                     x n IN topspace (rfs_vtop (V n) (t n))) /\
                (!n y s. s <= t n /\ y IN topspace (rfs_vtop (V n) s) /\ Lc <= rfs_vscalar (V n) s y
                         ==> p3_canon_at (V n) C1 eps1 y s) /\
                (!n s. s < t n ==> compact_space (rfs_vtop (V n) s)) /\
                (!n c. compact_in (rfs_vtop (V n) (t n))
                         {y | y IN topspace (rfs_vtop (V n) (t n)) /\ rfs_vscalar (V n) (t n) y <= c})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN GEN_TAC THEN USE_THEN "per" (MP_TAC o SPEC `n:num`) THEN
    SIMP_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p3_horn ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) en ((H:num->real^3->A) n)` THEN
    REWRITE_TAC[p3_horn; mfd_param] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    UNDISCH_TAC `(x:num->A) n IN p3_horn_set ((H:num->real^3->A) n)` THEN
    REWRITE_TAC[p3_horn_set] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET s' ==> (x:A) IN IMAGE f s ==> IMAGE f s' SUBSET t ==> x IN t`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n y s. s <= t n /\ y IN topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s) /\
            &4 * rfs_vscalar (V n) (t n) ((x:num->A) n) <= rfs_vscalar (V n) s y
            ==> p3_canon_at (V n) C1 eps1 y s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Lc:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canon_at")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Lc:real`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      not(is_conj(snd(dest_forall(concl th)))))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?D N. &0 < D /\
              !n y. N <= n /\
                    y IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)
                           (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                    ==> rfs_vscalar (V n) (t n) y <= D * rfs_vscalar (V n) (t n) (x n)`
  (LABEL_TAC "ub") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "t102" (MP_TAC o SPECL [`eps1:real`; `C1:real`; `A:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))))) THEN
    USE_THEN "Qinf" (X_CHOOSE_TAC `N:num` o SPEC `D0:real`) THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "d" (MP_TAC o SPECL
     [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
      `(x:num->A) n`; `(t:num->real) n`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[REAL_LT_IMP_LE] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `D0:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?D1 N. &0 < D1 /\
              !n y. N <= n /\
                    y IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)
                           (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                    ==> rfs_vscalar (V n) (t n) (x n) <= D1 * rfs_vscalar (V n) (t n) y`
  (LABEL_TAC "lbd") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "rl" (MP_TAC o SPECL [`eps1:real`; `C1:real`; `A:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `Q1:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")))) THEN
    USE_THEN "Qinf" (X_CHOOSE_TAC `N:num` o SPEC `max Q1 (D1 * Lc)`) THEN
    MAP_EVERY EXISTS_TAC [`D1:real`; `N:num`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "d" (MP_TAC o SPECL
     [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
      `(x:num->A) n`; `(t:num->real) n`; `Lc:real`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `max Q1 (D1 * Lc)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` (LABEL_TAC "Qpos") THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `Lc:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. ?N. !n. N <= n
          ==> compact_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))
                (rfs_vtop (V n) (t n) closure_of
                 rfs_vball (V n) (t n) ((x:num->A) n)
                   (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))`
  (LABEL_TAC "cl") THENL
   [X_GEN_TAC `A:real` THEN
    USE_THEN "ub" (MP_TAC o SPEC `max A (&1)`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `N:num`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")))) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)
        (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))) SUBSET
      rfs_vball (V n) (t n) (x n) (max A (&1) * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))`
    ASSUME_TAC THENL
     [REWRITE_TAC[P2HN_VBALL_EQ] THEN MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_ARITH `A <= max A (&1)`] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN USE_THEN "Qpos" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `{y | y IN topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) /\
                     rfs_vscalar (V n) (t n) y <= D * rfs_vscalar (V n) (t n) ((x:num->A) n)}` THEN
    REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)
                       (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))` THEN
        REWRITE_TAC[P2HN_VBALL_EQ; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        USE_THEN "d" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_SIMP_TAC[P2HN_REGULAR_HAUSDORFF]]; 
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "canL" o check (fun th -> let vs,bod = strip_forall(concl th) in
    length vs = 3 && can (find_term ((=) `Lc:real`)) bod)) THEN
  FIRST_X_ASSUM(LABEL_TAC "cpt" o check (fun th -> let vs,bod = strip_forall(concl th) in
    length vs = 2 && can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) bod)) THEN
  FIRST_X_ASSUM(LABEL_TAC "cps" o check (fun th -> let vs,bod = strip_forall(concl th) in
    length vs = 2 && can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_space")) bod)) THEN
  FIRST_X_ASSUM(LABEL_TAC "can4" o check (fun th -> let vs,bod = strip_forall(concl th) in not(can (find_term ((=) `Lc:real`)) bod) &&
    length vs = 3 && can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canon_at")) bod)) THEN
  FIRST_X_ASSUM(LABEL_TAC "hn" o check (fun th -> let vs,bod = strip_forall(concl th) in
    length vs = 1 && is_conj bod && is_comb(lhand bod) && is_const(repeat rator (lhand bod)) &&
    fst(dest_const(repeat rator (lhand bod))) = "p3_horn")) THEN
  FIRST_X_ASSUM(LABEL_TAC "rg" o check (fun th -> let vs,bod = strip_forall(concl th) in
    length vs = 1 && is_conj bod && is_comb(lhand bod) && is_const(repeat rator (lhand bod)) &&
    fst(dest_const(repeat rator (lhand bod))) = "p2c_regular_view")) THEN
  SUBGOAL_THEN
   `!n A B y. A <= B /\
              (y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)
                         (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
              ==> y IN rfs_vball (V n) (t n) (x n) (B * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))) /\
                  y IN topspace (rfs_vtop (V n) (t n))`
  (LABEL_TAC "bm") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN SPEC_TAC(`y:A`,`y:A`) THEN REWRITE_TAC[GSYM SUBSET; P2HN_VBALL_EQ] THEN
      MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN USE_THEN "Qpos" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP P2HN_VBALL_TOPSPACE)];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_vblowup_seq (C1,eps1,pi / &6000,&1,&1)
                  (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                  (x:num->A) t`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2c_vblowup_seq; REAL_LT_01] THEN
    CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `A:real` THEN
    USE_THEN "hb" (MP_TAC o SPEC `max A (&1)`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
    USE_THEN "lbd" (MP_TAC o SPEC `max A (&1)`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `N2:num`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2")))) THEN
    USE_THEN "t102" (MP_TAC o SPECL [`eps1:real`; `C1:real`; `&5`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D5:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d5"))))) THEN
    USE_THEN "Qinf" (X_CHOOSE_THEN `N3:num` (LABEL_TAC "n3") o SPEC `D1 * max D0 Lc`) THEN
    EXISTS_TAC `MAX N1 (MAX N2 N3)` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN
    REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)
                 (max A (&1) * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))) /\
      y IN topspace (rfs_vtop (V n) (t n))`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "bm" MATCH_MP_TAC THEN EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `max D0 Lc < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (y:A)`
    ASSUME_TAC THENL
     [USE_THEN "n2" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "n3" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `D1 * max D0 Lc < D1 * rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (y:A)`
      MP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?e. rfs_strong_neck ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) en (y:A) (t n) e`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC P2HN_HORN_SET_NECK THEN EXISTS_TAC `(H:num->real^3->A) n` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "n1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!w s. s <= t n /\ w IN topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s) /\
            &4 * rfs_vscalar (V n) (t n) (y:A) <= rfs_vscalar (V n) s w
            ==> p3_canon_at (V n) C1 eps1 w s`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "canL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (y:A)
        (&5 * inv(sqrt(rfs_vscalar (V n) (t n) y))) SUBSET
      {w | w IN topspace (rfs_vtop (V n) (t n)) /\
           rfs_vscalar (V n) (t n) w <= D5 * rfs_vscalar (V n) (t n) y}`
    ASSUME_TAC THENL
     [USE_THEN "d5" (MP_TAC o SPECL
       [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
        `y:A`; `(t:num->real) n`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(LABEL_TAC "w5") THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `w:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP P2HN_VBALL_TOPSPACE);
        USE_THEN "w5" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "hp" (MP_TAC o SPECL
     [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
      `en:real`; `y:A`; `(t:num->real) n`; `e:real^3->A`;
      `{w | w IN topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) /\
            rfs_vscalar (V n) (t n) w <= D5 * rfs_vscalar (V n) (t n) (y:A)}`;
      `&1`; `&1`; `rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "t111" (MP_TAC o SPECL [`C1:real`; `eps1:real`; `pi / &6000`; `&1`; `&1`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `T1:real` (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC))))))) THEN
  FIRST_X_ASSUM(LABEL_TAC "lim11" o check (fun th -> can (find_term ((=) `K:real`)) (concl th))) THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                (!a. --T1 < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_const(repeat rator c) &&
      fst(dest_const(repeat rator c)) = "p3_flow_limit")) THEN
    REWRITE_TAC[p3_flow_limit] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `T1:real`]
    P2HN_UPTO_RIEMANNIAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "riem") THEN
  MP_TAC(ISPECL
   [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
    `(x:num->A) o (sub:num->num)`; `(t:num->real) o (sub:num->num)`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n))
           ((t:num->real) (sub n)) ((x:num->A) (sub n))`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`; `T1:real`; `abs K`]
    P2HN_Q0_FROM_LIMIT) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "rg" (MP_TAC o el 0 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view] o
        CONJUNCT1 o SPEC `(sub:num->num) n`) THEN
      DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      GEN_TAC THEN MATCH_MP_TAC P2HN_REGULAR_HAUSDORFF THEN ASM_REWRITE_TAC[];
      USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "lim11" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "lim11" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      MESON_TAC[REAL_ARITH `a <= K ==> a <= abs K`]];
    ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[o_THM] THEN DISCH_THEN(LABEL_TAC "q0") THEN
  SUBGOAL_THEN `p2hn_spk (C1,eps1,Lc,&6 * abs K + &1)
                  (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n))
                  (\n. (x:num->A) (sub n)) (\n. (t:num->real) (sub n))`
  (LABEL_TAC "spk") THENL
   [REWRITE_TAC[p2hn_spk] THEN BETA_TAC THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "cps" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "canL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `B:real` THEN USE_THEN "Qinf" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P2HN_SUBSEQ_GE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      USE_THEN "hb" (MP_TAC o SPEC `A:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
      USE_THEN "q0" (MP_TAC o SPEC `A:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
      EXISTS_TAC `MAX N1 N2` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN
      REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `?e. rfs_strong_neck ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)) en (y:A) ((t:num->real) (sub n)) e`
        MP_TAC THENL
         [MATCH_MP_TAC P2HN_HORN_SET_NECK THEN EXISTS_TAC `(H:num->real^3->A) ((sub:num->num) n)` THEN
          CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          USE_THEN "n1" (MP_TAC o SPEC `(sub:num->num) n`) THEN ANTS_TAC THENL
           [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P2HN_SUBSEQ_GE]; ALL_TAC] THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[rfs_strong_neck] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^3->A` THEN
        DISCH_TAC THEN MATCH_MP_TAC P2HN_REG_EVNECK_MONO THEN EXISTS_TAC `en:real` THEN ASM_REWRITE_TAC[];
        USE_THEN "n2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "lbd" (MP_TAC o SPEC `A:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2")))) THEN
    MAP_EVERY EXISTS_TAC [`D1:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "n2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P2HN_SUBSEQ_GE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_vblowup_seq (C1,eps1,pi / &6000,&1,&1)
                  (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n))
                  (\n. (x:num->A) (sub n)) (\n. (t:num->real) (sub n))`
  ASSUME_TAC THENL [MATCH_MP_TAC P2HN_VSEQ_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "sq" (MP_TAC o SPECL [`C1:real`; `eps1:real`; `&1`; `C1:real`; `eps1:real`; `Lc:real`;
    `&6 * abs K + &1`; `&1`; `en:real`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`;
    `\n. (x:num->A) ((sub:num->num) n)`;
    `\n. (t:num->real) ((sub:num->num) n)`; `\n. (H:num->real^3->A) ((sub:num->num) n)`; `dl:real`]) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `A:real` THEN USE_THEN "cl" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P2HN_SUBSEQ_GE];
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN USE_THEN "hb" (MP_TAC o SPEC `A:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P2HN_SUBSEQ_GE]];
    ALL_TAC] THEN
  BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `e:real^3->A`)) THEN
  MAP_EVERY EXISTS_TAC [`(sub:num->num) m`; `e:real^3->A`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The contradiction argument of MT                                          *)
(* Thm 11.31 (MT pp. 287-291).  P2HN_HIST_HSEQ: the facts of p2hn_hseq for   *)
(* one history (maximal extension at the horizon, the 2 eps-horn H, a point  *)
(* of the horn set).  P2HN_1131_CORE: for fixed C, eps, r0, the boundary     *)
(* radius rb and dl there is h > 0 such that every point of a 2 eps-horn     *)
(* with boundary in Omega_rb and R >= h^-2 is the centre of an evolving      *)
(* dl-neck of length 2 inside the horn; if not, a sequence with R(x n) ->    *)
(* infinity contradicts P2HN_SEQ_FROM_HSEQ.                                  *)
(* ========================================================================= *)

(* The horn set lies in the slice.                                           *)

let P2HN_HORN_SET_TOPSPACE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    th eps H.
     p3_horn V th eps H ==> p3_horn_set H SUBSET topspace (rfs_vtop V th)`,
  REWRITE_TAC[p3_horn; mfd_param] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  REWRITE_TAC[p3_horn_set] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET s'
                         ==> IMAGE (f:real^3->A) s' SUBSET t ==> IMAGE f s SUBSET t`) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* One history: the facts of p2hn_hseq for (4 C, Kc K eps, 2 eps, 2 r0^-2,   *)
(* rb^-2) and R at the horizon read off gl.                                  *)

let P2HN_HIST_HSEQ = prove
 (`!u:A->bool.
     P2C_THM_11_19_STATEMENT u /\ P2C_MAXEXT_REGULAR_STATEMENT u /\ P2C_LEMMA_11_30_STATEMENT u
     ==> ?K Kc eps0. &1 <= K /\ &2 <= Kc /\ &0 < eps0 /\
           !C eps (hs:(A)rfs_history) r0 gl rb H x.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
              rfs_pinched (rfs_view hs) /\
              (!k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k)) /\
              (!t y. &0 <= t /\ t < rfs_horizon hs /\ y IN topspace(rfs_top_at hs t) /\
                     inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t y
                     ==> p3_canon_at (rfs_view hs) C eps y t) /\
              rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
              p3_horn (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (&2 * eps) H /\
              IMAGE H (sphere(vec 0,&1)) SUBSET
                p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rb /\
              x IN p3_horn_set H
              ==> p2c_regular_view (p3_maxext hs (p3_omega hs) gl) /\
                  rfs_pinched (p3_maxext hs (p3_omega hs) gl) /\
                  (!s. s < &0 ==> rfs_vtop (p3_maxext hs (p3_omega hs) gl) s = discrete_topology {}) /\
                  (!s. apx_sphere_sep (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s)
                                      (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) s)) /\
                  p3_horn (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (&2 * eps) H /\
                  x IN p3_horn_set H /\
                  (!z. z IN sphere(vec 0,&1)
                       ==> rfs_vscalar (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (H z) <=
                           inv(rb pow 2)) /\
                  (!y s. s <= rfs_horizon hs /\
                         y IN topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s) /\
                         &2 * inv(r0 pow 2) <= rfs_vscalar (p3_maxext hs (p3_omega hs) gl) s y
                         ==> p3_canon_at (p3_maxext hs (p3_omega hs) gl) (&4 * C)
                                         (Kc * K * eps) y s) /\
                  (!s. s < rfs_horizon hs
                       ==> compact_space (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s)) /\
                  (!c. compact_in (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                         {y | y IN topspace (rfs_vtop (p3_maxext hs (p3_omega hs) gl)
                                                      (rfs_horizon hs)) /\
                              rfs_vscalar (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) y <= c}) /\
                  rfs_vscalar (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) x =
                  mfd_scalar (hs_atlas hs (hs_count hs)) gl x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_HIST_PACK) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hp"))))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `Kc:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                       `gl:A->real^3^3`; `rb:real`; `H:real^3->A`; `x:A`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "hp" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                                    `gl:A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:A) IN p3_omega (hs:(A)rfs_history)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_HORN_SET_TOPSPACE) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN p3_horn_set H` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (H:real^3->A) (sphere(vec 0,&1)) SUBSET
                 p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega (hs:(A)rfs_history))
                              (gl:A->real^3^3) rb` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; p3_omega_rho; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 * inv(r0 pow 2)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a < &2 * a`) THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* MT Thm 11.31, first statement, in the form used by the route: the         *)
(* threshold h exists for each (C, eps, r0, rb, dl).                         *)

let P2HN_1131_CORE = prove
 (`!u:A->bool.
     P2C_THM_11_1_VIEW_STATEMENT u (:real^3) /\ P2C_THM_11_8_VIEW_STATEMENT u (:real^3) /\
     P2C_REQ_CAP_FIX_STATEMENT u (:real^3) /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT (:real^3) /\
     P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\ P2C_REQ_THM_10_2_VIEW_STATEMENT u /\
     P2C_THM_11_19_STATEMENT u /\ P2C_MAXEXT_REGULAR_STATEMENT u /\ P2C_LEMMA_11_30_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps r0 rb dl.
             &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < r0 /\ &0 < rb /\ &0 < dl
             ==> ?h. &0 < h /\
                   !(hs:(A)rfs_history) gl H x.
                     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
                     (!k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k)) /\
                     (!t y. &0 <= t /\ t < rfs_horizon hs /\ y IN topspace(rfs_top_at hs t) /\
                            inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t y
                            ==> p3_canon_at (rfs_view hs) C eps y t) /\
                     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
                     p3_horn (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (&2 * eps) H /\
                     IMAGE H (sphere(vec 0,&1)) SUBSET
                       p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rb /\
                     x IN p3_horn_set H /\
                     inv(h pow 2) <= mfd_scalar (hs_atlas hs (hs_count hs)) gl x
                     ==> ?e. rfs_evolving_neck (p3_maxext hs (p3_omega hs) gl) dl x
                                               (rfs_horizon hs) (&2) e /\
                             IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set H`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2HN_HIST_HSEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `eH:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hh"))))))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `(:real^3)`] P2HN_SEQ_FROM_HSEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sf"))) THEN
  SUBGOAL_THEN `&0 < Kc * K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min eH (eF / (Kc * K))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `r0:real`; `rb:real`; `dl:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Kc * K * eps <= eF` ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= eF / (Kc * K)` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * inv(r0 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. &0 < inv(sqrt(&n + &1 + &2 * inv(r0 pow 2))) /\
        inv(inv(sqrt(&n + &1 + &2 * inv(r0 pow 2))) pow 2) = &n + &1 + &2 * inv(r0 pow 2)`
  (LABEL_TAC "hn") THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_INV; REAL_INV_INV] THEN MATCH_MP_TAC SQRT_POW_2 THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!P. ((!h:real. &0 < h ==> ~P h) ==> F) ==> ?h. &0 < h /\ P h`) THEN
  USE_THEN "hn" (fun hn -> DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP; SKOLEM_THM] o
    REWRITE_RULE[hn] o GEN `n:num` o SPEC `inv(sqrt(&n + &1 + &2 * inv(r0 pow 2)))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `hs:num->(A)rfs_history` (X_CHOOSE_THEN `gl:num->A->real^3^3`
    (X_CHOOSE_THEN `H:num->real^3->A` (X_CHOOSE_THEN `x:num->A` (LABEL_TAC "cx"))))) THEN
  USE_THEN "hh" (fun hh ->
    let th = SPECL [`C:real`; `eps:real`; `(hs:num->(A)rfs_history) n`; `r0:real`;
                    `(gl:num->A->real^3^3) n`; `rb:real`; `(H:num->real^3->A) n`; `(x:num->A) n`] hh in
    SUBGOAL_THEN (mk_forall(`n:num`, rand(concl th))) (LABEL_TAC "pk") THENL
     [GEN_TAC THEN MP_TAC th THEN ANTS_TAC THENL
       [USE_THEN "cx" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC]) THEN
  SUBGOAL_THEN `&2 <= Kc * K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kc * &1` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sf" (MP_TAC o SPECL [`&4 * C`; `Kc * K * eps`; `&2 * eps`; `&2 * inv(r0 pow 2)`;
     `inv(rb pow 2)`;
     `\n. p3_maxext ((hs:num->(A)rfs_history) n) (p3_omega (hs n)) ((gl:num->A->real^3^3) n)`;
     `x:num->A`; `\n. rfs_horizon ((hs:num->(A)rfs_history) n)`; `H:num->real^3->A`; `dl:real`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2hn_hseq] THEN BETA_TAC THEN USE_THEN "pk" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT];
      X_GEN_TAC `B:real` THEN MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "cx" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1 o SPEC `n:num`) THEN
      SUBGOAL_THEN `&N <= &n` MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN
      USE_THEN "cx" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1 o SPEC `n:num`) THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `e:real^3->A`)) THEN
  USE_THEN "cx" (MP_TAC o CONJUNCT2 o SPEC `n:num`) THEN REWRITE_TAC[] THEN
  EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The last statement of MT Thm 11.31                                        *)
(* (MT p. 291): a point y with R(y) = h^-2 whose neck sphere cuts off an     *)
(* end of the horn disjoint from Omega_rho.  In the horn chart H the neck    *)
(* sphere is a topological 2-sphere; by Jordan-Brouwer (HOL Light            *)
(* JORDAN_INSIDE_OUTSIDE_GEN) it has an inside and an outside, and a neck    *)
(* sphere in a horn of necks encloses the unit ball (otherwise its inside    *)
(* would be a compact side, P2HN_NECK_SIDE_NONCOMPACT_GEN).  Choosing the    *)
(* chart point w beyond every chart point with R <= th/2 and R(H w) = th     *)
(* (P2HN_HORN_CHOOSE_W), the outside of the neck sphere at H w carries       *)
(* R > th/4: a lower level point there would carry a neck sphere             *)
(* enclosing the sphere at H w (P2HN_HORN_FAR_SIDE).  The neck at y is       *)
(* reversed if needed so that e(2 basis 1) lies on the far side.             *)
(* ========================================================================= *)

(* The cylinder flow is invariant under the inversion of R^3 (all times).    *)

let P2HN_INVERSION_CYL = prove
 (`!t y:real^3.
        ~(y = vec 0)
        ==> mpullback (\z:real^3. inv(norm z pow 2) % z) (cylinder_flow t) y =
            cylinder_flow t y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPEC `y:real^3` RFB_INVERSION_HAS_DERIVATIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)] THEN
                       ASSUME_TAC th) THEN
  SUBGOAL_THEN `!w x:real^3. cylinder_flow t w ** x =
                 (&2 / norm w pow 2) % ((&1 - t) % x + (t / norm w pow 2 * (w dot x)) % w)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                MATRIX_VECTOR_MUL_LID] THEN
    SUBGOAL_THEN `((lambda i j. (w:real^3)$i * w$j):real^3^3) ** x = (w dot x) % w`
    SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_3; FORALL_3; SUM_3; dot;
               VECTOR_MUL_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_ASSOC]];
    ALL_TAC] THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) RFB_CONGRUENCE_DOT (lhand w))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`\z:real^3. inv(norm z pow 2) % z`; `at(y:real^3)`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` MP_TAC THENL [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; NORM_POW_2;
              REAL_POW_INV] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* Evolving necks of a regular view can be reversed (apx_rev).               *)

let P2HN_EVNECK_REV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t len (e:real^3->A).
     p2c_regular_view V /\ rfs_evolving_neck V eps x t len e
     ==> rfs_evolving_neck V eps x t len (apx_rev e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. --len < s /\ s <= &0
        ==> smooth_manifold_atlas (rfs_vtop V (t + s / rfs_vscalar V t x))
                                  (rfs_vatlas V (t + s / rfs_vscalar V t x)) /\
            riemannian_metric (rfs_vatlas V (t + s / rfs_vscalar V t x))
                              (rfs_vmetric V (t + s / rfs_vscalar V t x)) /\
            mfd_param (rfs_vtop V (t + s / rfs_vscalar V t x))
                      (rfs_vatlas V (t + s / rfs_vscalar V t (x:A))) (rfs_neck_dom eps)
                      (e:real^3->A)`
  (LABEL_TAC "sl") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `eps:real`; `x:A`; `t:real`; `len:real`; `e:real^3->A`; `s:real`]
      P2B9_REGULAR_NECK_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^3->A`; `eps:real`] APX_REV_IMAGE_DOM) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2BN_EVOLVING_NECK_ALT] o check (fun th ->
    let c = concl th in is_comb c && is_const(repeat rator c) &&
    fst(dest_const(repeat rator c)) = "rfs_evolving_neck")) THEN
  STRIP_TAC THEN
  USE_THEN "sl" (MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      let c = concl th in is_comb c && is_const(repeat rator c) &&
      fst(dest_const(repeat rator c)) = "rfs_neck")) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `iv = \z:real^3. inv(norm z pow 2) % z` THEN
  SUBGOAL_THEN `apx_rev (e:real^3->A) = e o iv` SUBST_ALL_TAC THENL
   [EXPAND_TAC "iv" THEN REWRITE_TAC[apx_rev; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom eps) (iv:real^3->real^3) iv`
  ASSUME_TAC THENL
   [EXPAND_TAC "iv" THEN REWRITE_TAC[REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM] THEN
    MP_TAC(INST_TYPE [`:3`,`:N`] (SPECL [`exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
                  SMT_DIFFEO_INVERSION_ANNULUS)) THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_EXP_NEG; REAL_INV_INV; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_EXP_POS_LT] THEN
    SUBGOAL_THEN `&0 < inv eps * inv(sqrt(&2))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[P2BN_EVOLVING_NECK_ALT] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps (x:A)
                    (apx_rev (e:real^3->A))` MP_TAC THENL
     [MATCH_MP_TAC APX_REV_NECK THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "iv" THEN REWRITE_TAC[apx_rev; o_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar V t (x:A)` ASSUME_TAC THENL
   [REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      let c = concl th in is_comb c && is_const(repeat rator c) &&
      fst(dest_const(repeat rator c)) = "rfs_neck")) THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_comb c &&
    is_const(repeat rator c) && fst(dest_const(repeat rator c)) = "rfs_close_fam")) THEN
  REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `s' = t + s / rfs_vscalar V t (x:A)` THEN
  SUBGOAL_THEN `(iv:real^3->real^3) y IN rfs_neck_dom eps` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom eps) (iv:real^3->real^3) iv` THEN
    REWRITE_TAC[diffeomorphism_on] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                (\y. rfs_vscalar V t (x:A) %%
                     rfs_pullback (rfs_vatlas V s') (e:real^3->A) (rfs_vmetric V s') y)
                ((iv:real^3->real^3) y)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(iv:real^3->real^3) y`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MP_TAC(ISPECL [`rfs_kreg eps`; `rfs_neck_dom eps`; `rfs_neck_dom eps`; `iv:real^3->real^3`;
                 `iv:real^3->real^3`; `cylinder_flow s`;
                 `\y. rfs_vscalar V t (x:A) %%
                      rfs_pullback (rfs_vatlas V s') (e:real^3->A) (rfs_vmetric V s') y`;
                 `y:real^3`] LCK_DIST2_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
  ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "iv" THEN ASM_SIMP_TAC[P2HN_INVERSION_CYL]; ALL_TAC] THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `rfs_neck_dom eps`; `iv:real^3->real^3`;
                 `iv:real^3->real^3`; `w:real^3`] APX_RFS_PULLBACK_PRECOMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

(* The horn-chart preimage of a neck sphere inside the open horn is a        *)
(* compact topological 2-sphere.                                             *)

let P2HN_HORN_SPHERE_PRE = prove
 (`!top atlas (H:real^3->A) (e:real^3->A) U.
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     mfd_param top atlas U e /\ sphere(vec 0,&1) SUBSET U /\
     IMAGE e (sphere(vec 0,&1)) SUBSET IMAGE H {y | &1 < norm y}
     ==> ?sg. sg SUBSET {y | &1 < norm y} /\ compact sg /\
              sg homeomorphic sphere(vec 0:real^3,&1) /\
              IMAGE H sg = IMAGE e (sphere(vec 0,&1)) /\
              (!z. &1 / &2 < norm z /\ H z IN IMAGE e (sphere(vec 0,&1)) ==> z IN sg)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `{y:real^3 | &1 / &2 < norm y}`; `H:real^3->A`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `H':A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:real^3->bool`; `e:real^3->A`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1)
                  ==> (e:real^3->A) x IN IMAGE (H:real^3->A) {y | &1 / &2 < norm y} /\
                      &1 < norm((H':A->real^3)(e x)) /\ H(H'(e x)) = e x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE (H:real^3->A) {y | &1 < norm y}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^3) IN {y | &1 / &2 < norm y}` ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(H':A->real^3) ((H:real^3->A) w) = w` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE ((H':A->real^3) o (e:real^3->A)) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `((H':A->real^3) o (e:real^3->A)) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),euclidean)
                    ((H':A->real^3) o (e:real^3->A))` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology top (IMAGE (H:real^3->A) {y | &1 / &2 < norm y})` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `subtopology euclidean (sphere(vec 0:real^3,&1)) =
                      subtopology (subtopology euclidean U) (sphere(vec 0,&1))` SUBST1_TAC THENL
         [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
    EXISTS_TAC `(H':A->real^3) o (e:real^3->A)` THEN ASM_REWRITE_TAC[COMPACT_SPHERE] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `U:real^3->bool`; `e:real^3->A`] MFD_PARAM_INJ) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(H:real^3->A) z IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE; o_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* The image of an open connected set of the chart whose closure adds only   *)
(* the sphere is a component of the complement of the image sphere.          *)

let P2HN_HORN_IMAGE_COMPONENT = prove
 (`!top atlas (H:real^3->A) sg O0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
     sg SUBSET {y | &1 < norm y} /\
     open O0 /\ connected O0 /\ ~(O0 = {}) /\ O0 SUBSET {y | &1 < norm y} /\
     DISJOINT O0 sg /\ closed (O0 UNION sg)
     ==> IMAGE H O0 IN
           connected_components_of (subtopology top (topspace top DIFF IMAGE H sg)) /\
         top closure_of (IMAGE H O0) SUBSET IMAGE H (O0 UNION sg)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(O0 UNION sg) SUBSET {y:real^3 | &1 / &2 < norm y} /\
                (O0 UNION sg) SUBSET {y:real^3 | &1 <= norm y}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(sg:real^3->bool) SUBSET {y | &1 < norm y}` THEN
    UNDISCH_TAC `(O0:real^3->bool) SUBSET {y | &1 < norm y}` THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[REAL_ARITH `&1 < x ==> &1 / &2 < x /\ &1 <= x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (H:real^3->A) (O0 UNION sg))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_HORN_CLOSED_IMAGE THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (H:real^3->A) O0) (IMAGE H sg)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `a:real^3 = b` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `{y:real^3 | &1 / &2 < norm y}`; `H:real^3->A`] MFD_PARAM_INJ) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `DISJOINT (O0:real^3->bool) sg` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (H:real^3->A) (O0 UNION sg) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `{y:real^3 | &1 / &2 < norm y}`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3H_CLOPEN_COMPONENT THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2HN_PARAM_IMAGE_CONNECTED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                              `{y:real^3 | &1 / &2 < norm y}`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `IMAGE (H:real^3->A) O0` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                              `{y:real^3 | &1 / &2 < norm y}`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
      EXISTS_TAC `IMAGE (H:real^3->A) (O0 UNION sg)` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]];
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

(* A neck sphere in a horn of necks encloses the unit ball in the horn       *)
(* chart.                                                                    *)

let P2HN_HORN_SPHERE_ENCLOSES = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) (H:real^3->A) eps x0 e sg.
       &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g /\
       apx_sphere_sep top atlas /\
       mfd_param top atlas {y | &1 / &2 < norm y} H /\
       (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
       (!y. &1 <= norm y ==> ?e. rfs_neck (top,atlas) g eps (H y) e) /\
       rfs_neck (top,atlas) g eps x0 e /\
       sg SUBSET {y | &1 < norm y} /\ compact sg /\ sg homeomorphic sphere(vec 0:real^3,&1) /\
       IMAGE H sg = IMAGE e (sphere(vec 0,&1))
       ==> cball(vec 0,&1) SUBSET inside sg`,
  X_CHOOSE_THEN `eN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_SIDE_NONCOMPACT_GEN) THEN
  EXISTS_TAC `eN:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `sg:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `DISJOINT (cball(vec 0:real^3,&1)) sg` ASSUME_TAC THENL
   [UNDISCH_TAC `(sg:real^3->bool) SUBSET {y | &1 < norm y}` THEN
    REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_CBALL_0; IN_ELIM_THM] THEN
    MESON_TAC[REAL_NOT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,&1) SUBSET outside sg` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN EXISTS_TAC `y:real^3` THEN CONJ_TAC THENL
     [REWRITE_TAC[connected_component] THEN EXISTS_TAC `cball(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[CONNECTED_CBALL] THEN ASM SET_TAC[];
      UNDISCH_TAC `inside sg UNION outside sg = (:real^3) DIFF sg` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside sg SUBSET {y:real^3 | &1 < norm y}` ASSUME_TAC THENL
   [UNDISCH_TAC `cball(vec 0:real^3,&1) SUBSET outside sg` THEN
    UNDISCH_TAC `inside sg INTER outside sg = {}:real^3->bool` THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_CBALL_0; IN_ELIM_THM] THEN
    MESON_TAC[REAL_NOT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(inside sg) = inside sg UNION (sg:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `H:real^3->A`;
                 `sg:real^3->bool`; `inside sg:real^3->bool`] P2HN_HORN_IMAGE_COMPONENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `inside sg UNION outside sg = (:real^3) DIFF sg` THEN SET_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhand(concl th) = `closure(inside sg):real^3->bool`)) THEN
      REWRITE_TAC[CLOSED_CLOSURE]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (H:real^3->A) (inside sg UNION sg))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `{y:real^3 | &1 / &2 < norm y}`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhand(concl th) = `closure(inside sg):real^3->bool`)) THEN
      ASM_SIMP_TAC[COMPACT_CLOSURE];
      UNDISCH_TAC `inside sg SUBSET {y:real^3 | &1 < norm y}` THEN
      UNDISCH_TAC `(sg:real^3->bool) SUBSET {y | &1 < norm y}` THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `&1 < x ==> &1 / &2 < x`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (H:real^3->A) sg SUBSET top closure_of (IMAGE H (inside sg))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `{y:real^3 | &1 / &2 < norm y}`; `H:real^3->A`] MFD_PARAM_MAPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `H':A->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (H:real^3->A)
                  ((subtopology euclidean {y:real^3 | &1 / &2 < norm y}) closure_of inside sg)` THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    SUBGOAL_THEN `{y:real^3 | &1 / &2 < norm y} INTER inside sg = inside sg` SUBST1_TAC THENL
     [UNDISCH_TAC `inside sg SUBSET {y:real^3 | &1 < norm y}` THEN
      REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `&1 < x ==> &1 / &2 < x`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(sg:real^3->bool) SUBSET {y | &1 < norm y}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[REAL_ARITH `&1 < x ==> &1 / &2 < x`];
    ALL_TAC] THEN
  USE_THEN "ns" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x0:A`; `e:real^3->A`; `IMAGE (H:real^3->A) (inside sg)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `IMAGE (H:real^3->A) sg`)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `p:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:A) IN IMAGE (H:real^3->A) (inside sg UNION sg)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(w:real^3) IN inside sg UNION sg` THEN
      UNDISCH_TAC `inside sg SUBSET {y:real^3 | &1 < norm y}` THEN
      UNDISCH_TAC `(sg:real^3->bool) SUBSET {y | &1 < norm y}` THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      MESON_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `~(sg:real^3->bool = {})` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `(sg:real^3->bool) homeomorphic sphere(vec 0:real^3,&1)` THEN
        ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `IMAGE (H:real^3->A) (inside sg UNION sg)` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]);;

(* R varies by at most ten per cent on an eps-neck (APX_NECK_CURV with alpha *)
(* = 1/10).                                                                  *)

let P2HN_NECK_R_RANGE = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x e p.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ p IN IMAGE e (rfs_neck_dom eps)
        ==> &9 / &10 * mfd_scalar atlas g x <= mfd_scalar atlas g p /\
            mfd_scalar atlas g p <= &11 / &10 * mfd_scalar atlas g x`,
  MP_TAC(SPEC `&1 / &10`
    (REWRITE_RULE[APX_NECK_CURV_STATEMENT] (ISPEC `(:A)` APX_NECK_CURV))) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 / &10`] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `p:A`] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "nc" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`]
                APX_PULLBACK_SCALAR_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
  UNDISCH_TAC `abs(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y) /
                   mfd_scalar atlas g x - &1) <= &1 / &10` THEN
  UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x` THEN
  SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y)`,`a:real`) THEN
  SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) x`,`b:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a / b - &1 = (a - b) / b` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `abs((a - b) / b) <= &1 / &10` THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < b ==> abs b = b`; REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* Intermediate values of a continuous real function on a connected set.     *)

let P2HN_CONNECTED_IVT = prove
 (`!top (f:A->real) c p q a.
     continuous_map (top,euclideanreal) f /\ connected_in top c /\
     p IN c /\ q IN c /\ f p <= a /\ a <= f q
     ==> ?r. r IN c /\ f r = a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `top:A topology`; `euclideanreal`; `c:A->bool`]
    CONNECTED_IN_CONTINUOUS_MAP_IMAGE) THEN
  ASM_REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL; is_realinterval] THEN
  DISCH_THEN(MP_TAC o SPECL [`(f:A->real) p`; `(f:A->real) q`; `a:real`]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* A connected set meeting the horn set and missing the boundary sphere lies *)
(* in the open horn.                                                         *)

let P2HN_CONNECTED_IN_HORN_OPEN = prove
 (`!top atlas (H:real^3->A) c.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
     connected_in top c /\ ~DISJOINT c (IMAGE H {y | &1 <= norm y}) /\
     DISJOINT c (IMAGE H (sphere(vec 0,&1)))
     ==> c SUBSET IMAGE H {y | &1 < norm y}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `H:real^3->A`;
                 `c:A->bool`] P2HN_CONNECTED_IN_HORN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:A) IN IMAGE (H:real^3->A) {y | &1 <= norm y}` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `DISJOINT c (IMAGE (H:real^3->A) (sphere(vec 0,&1)))` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The far side of the neck sphere at a chart point beyond all chart points  *)
(* with R <= th/2 is a component of the complement, lies in the open horn,   *)
(* contains a neighbourhood of infinity of the chart, and carries R > th/4.  *)

let P2HN_HORN_FAR_SIDE = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) (H:real^3->A) eps th e w.
       &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g /\
       apx_sphere_sep top atlas /\
       mfd_param top atlas {y | &1 / &2 < norm y} H /\
       (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
       (!y. &1 <= norm y ==> ?e. rfs_neck (top,atlas) g eps (H y) e) /\
       &0 < th /\
       (!z. norm z = &1 ==> mfd_scalar atlas g (H z) <= th / &8) /\
       &1 < norm w /\ mfd_scalar atlas g (H w) = th /\
       (!z. &1 <= norm z /\ mfd_scalar atlas g (H z) <= th / &2 ==> norm z < norm w) /\
       rfs_neck (top,atlas) g eps (H w) e
       ==> ?sg. sg SUBSET {y | &1 < norm y} /\ compact sg /\
                sg homeomorphic sphere(vec 0:real^3,&1) /\
                IMAGE H sg = IMAGE e (sphere(vec 0,&1)) /\
                cball(vec 0,&1) SUBSET inside sg /\
                outside sg SUBSET {y | &1 < norm y} /\
                (?R1. !z. R1 <= norm z ==> z IN outside sg) /\
                IMAGE H (outside sg) IN
                  connected_components_of
                    (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) /\
                (!p. p IN IMAGE H (outside sg) ==> th / &4 < mfd_scalar atlas g p)`,
  X_CHOOSE_THEN `eK:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kl"))
    (INST_TYPE [`:A`,`:A`] P2HN_HORN_SPHERE_ENCLOSES) THEN
  X_CHOOSE_THEN `eR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rr"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_R_RANGE) THEN
  EXISTS_TAC `min eK (min eR (&1 / &4))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `H:real^3->A`; `eps:real`; `th:real`; `e:real^3->A`; `w:real^3`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (mfd_scalar atlas (g:A->real^3^3))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x' e'. rfs_neck (top,atlas) (g:A->real^3^3) eps x' e' /\
            x' IN IMAGE (H:real^3->A) {y | &1 <= norm y} /\
            th / &8 < &9 / &10 * mfd_scalar atlas g x'
            ==> (!p. p IN IMAGE e' (sphere(vec 0,&1))
                     ==> &9 / &10 * mfd_scalar atlas g x' <= mfd_scalar atlas g p /\
                         mfd_scalar atlas g p <= &11 / &10 * mfd_scalar atlas g x') /\
                ?sg. sg SUBSET {y | &1 < norm y} /\ compact sg /\
                     sg homeomorphic sphere(vec 0:real^3,&1) /\
                     IMAGE H sg = IMAGE e' (sphere(vec 0,&1)) /\
                     (!z. &1 / &2 < norm z /\ H z IN IMAGE e' (sphere(vec 0,&1)) ==> z IN sg) /\
                     cball(vec 0,&1) SUBSET inside sg`
  (LABEL_TAC "pre") THENL
   [MAP_EVERY X_GEN_TAC [`x':A`; `e':real^3->A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
      REWRITE_TAC[P2HN_SPHERE_IN_ANNULUS] THEN MATCH_MP_TAC P2HN_NECK_DOM_COLLAR THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!p. p IN IMAGE (e':real^3->A) (sphere(vec 0,&1))
                      ==> &9 / &10 * mfd_scalar atlas (g:A->real^3^3) x' <= mfd_scalar atlas g p /\
                          mfd_scalar atlas g p <= &11 / &10 * mfd_scalar atlas g x'`
    ASSUME_TAC THENL
     [X_GEN_TAC `p:A` THEN DISCH_TAC THEN USE_THEN "rr" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`; `e':real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      let c = concl th in is_comb c && is_const(repeat rator c) &&
      fst(dest_const(repeat rator c)) = "rfs_neck")) THEN
    SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE (H:real^3->A) {y | &1 < norm y}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2HN_CONNECTED_IN_HORN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P2HN_PARAM_IMAGE_CONNECTED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
        ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x':A` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `p:A` THEN
        STRIP_TAC THEN
        UNDISCH_TAC `(p:A) IN IMAGE (H:real^3->A) (sphere(vec 0,&1))` THEN
        REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `p:A` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `&11 / &10`)) (concl th))) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `th / &8`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `H:real^3->A`;
                   `e':real^3->A`; `rfs_neck_dom eps`] P2HN_HORN_SPHERE_PRE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sg:real^3->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "kl" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `H:real^3->A`; `eps:real`; `x':A`; `e':real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "pre" (MP_TAC o SPECL [`(H:real^3->A) w`; `e:real^3->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Ry") (X_CHOOSE_THEN `sg:real^3->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `sg:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `sg:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `outside sg SUBSET {y:real^3 | &1 < norm y}` ASSUME_TAC THENL
   [UNDISCH_TAC `cball(vec 0:real^3,&1) SUBSET inside sg` THEN
    UNDISCH_TAC `inside sg INTER outside sg = {}:real^3->bool` THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_CBALL_0; IN_ELIM_THM] THEN
    MESON_TAC[REAL_NOT_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?R1. !z:real^3. R1 <= norm z ==> z IN outside sg` (LABEL_TAC "far") THENL
   [MP_TAC(ISPEC `sg:real^3->bool` COBOUNDED_OUTSIDE) THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^3` o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r + &1` THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(:real^3) DIFF outside sg SUBSET cball(vec 0,r)` THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN UNDISCH_TAC `r + &1 <= norm(z:real^3)` THEN
    MESON_TAC[REAL_ARITH `r + &1 <= x ==> ~(x <= r)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `H:real^3->A`;
                 `sg:real^3->bool`; `outside sg:real^3->bool`] P2HN_HORN_IMAGE_COMPONENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `inside sg UNION outside sg = (:real^3) DIFF sg` THEN SET_TAC[];
      SUBGOAL_THEN `outside sg UNION sg = closure(outside sg):real^3->bool` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER]; REWRITE_TAC[CLOSED_CLOSURE]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  USE_THEN "far" (X_CHOOSE_TAC `R1:real`) THEN
  SUBGOAL_THEN `?v:real^3. v IN outside sg /\
                           mfd_scalar atlas (g:A->real^3^3) ((H:real^3->A) v) = th / &4`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `zf:real^3 = (max R1 (norm(w:real^3)) + &1) % basis 1` THEN
    SUBGOAL_THEN `norm(zf:real^3) = max R1 (norm(w:real^3)) + &1` ASSUME_TAC THENL
     [EXPAND_TAC "zf" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      MP_TAC(ISPEC `w:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(zf:real^3) IN outside sg` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `th / &2 < mfd_scalar atlas (g:A->real^3^3) ((H:real^3->A) zf)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `zf:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `th / &2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `mfd_scalar atlas (g:A->real^3^3)`;
                   `IMAGE (H:real^3->A) (outside sg)`; `p:A`; `(H:real^3->A) zf`; `th / &4`]
      P2HN_CONNECTED_IVT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2HN_PARAM_IMAGE_CONNECTED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                              `{y:real^3 | &1 / &2 < norm y}`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `outside sg SUBSET {y:real^3 | &1 < norm y}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_ARITH `&1 < x ==> &1 / &2 < x`];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:A` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^3` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?eq. rfs_neck (top,atlas) (g:A->real^3^3) eps ((H:real^3->A) v) eq`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `outside sg SUBSET {y:real^3 | &1 < norm y}` THEN
    UNDISCH_TAC `(v:real^3) IN outside sg` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < norm(v:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `outside sg SUBSET {y:real^3 | &1 < norm y}` THEN
    UNDISCH_TAC `(v:real^3) IN outside sg` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "pre" (MP_TAC o SPECL [`(H:real^3->A) v`; `eq:real^3->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Rq") (X_CHOOSE_THEN `sq:real^3->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `sq:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `sq SUBSET ball(vec 0:real^3,norm(w:real^3))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `th / &2`)) (concl th))) THEN
    SUBGOAL_THEN `(H:real^3->A) z IN IMAGE (eq:real^3->A) (sphere(vec 0,&1))` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "Rq" (MP_TAC o SPEC `(H:real^3->A) z`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) ((H:real^3->A) v) = th / &4` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(sq:real^3->bool) SUBSET {y | &1 < norm y}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inside sq SUBSET ball(vec 0:real^3,norm(w:real^3))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN outside sq` MP_TAC THENL
     [MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
      EXISTS_TAC `(:real^3) DIFF ball(vec 0,norm(w:real^3))` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
        REWRITE_TAC[BOUNDED_BALL; CONVEX_BALL; DIMINDEX_3] THEN ARITH_TAC;
        MESON_TAC[BOUNDED_BALL; BOUNDED_UNION; NOT_BOUNDED_UNIV;
                  SET_RULE `(:real^3) = (UNIV DIFF s) UNION s`];
        UNDISCH_TAC `sq SUBSET ball(vec 0:real^3,norm(w:real^3))` THEN SET_TAC[]];
      UNDISCH_TAC `inside sq INTER outside sq = {}:real^3->bool` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (sg:real^3->bool) sq` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(H:real^3->A) z IN IMAGE (e:real^3->A) (sphere(vec 0,&1)) /\
                  (H:real^3->A) z IN IMAGE (eq:real^3->A) (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "Ry" (MP_TAC o SPEC `(H:real^3->A) z`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "Rq" (MP_TAC o SPEC `(H:real^3->A) z`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) ((H:real^3->A) v) = th / &4` THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) ((H:real^3->A) w) = th` THEN
    UNDISCH_TAC `&0 < th` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(sq:real^3->bool) /\ connected(inside sg UNION sg:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_CONNECTEDNESS th]) o check (fun th ->
        can (find_term (fun t -> t = `sq:real^3->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "homeomorphic")) (concl th))) THEN
      SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH];
      SUBGOAL_THEN `inside sg UNION sg = closure(inside sg):real^3->bool` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER];
        MATCH_MP_TAC CONNECTED_CLOSURE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN sq` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      let c = concl th in is_comb c && is_const(repeat rator c) &&
      fst(dest_const(repeat rator c)) = "rfs_neck" && rand c = `eq:real^3->A`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sq SUBSET outside(sg:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN EXISTS_TAC `v:real^3` THEN
    ASM_REWRITE_TAC[connected_component] THEN EXISTS_TAC `sq:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside sg UNION sg SUBSET inside(sq:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN EXISTS_TAC `vec 0:real^3` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[connected_component] THEN EXISTS_TAC `inside sg UNION sg:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `sq SUBSET outside(sg:real^3->bool)` THEN
        UNDISCH_TAC `inside sg INTER outside sg = {}:real^3->bool` THEN
        UNDISCH_TAC `inside sg UNION outside sg = (:real^3) DIFF sg` THEN SET_TAC[];
        REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        UNDISCH_TAC `cball(vec 0:real^3,&1) SUBSET inside sg` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC];
      UNDISCH_TAC `cball(vec 0:real^3,&1) SUBSET inside sq` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN sg` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `sg:real^3->bool`)) (concl th) &&
      can (find_term (fun t -> t = `e:real^3->A`)) (concl th))) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      let c = concl th in is_comb c && is_const(repeat rator c) &&
      fst(dest_const(repeat rator c)) = "rfs_neck" && rand c = `e:real^3->A`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN ball(vec 0,norm(w:real^3))` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_BALL_0; REAL_LT_REFL]]);;

(* The choice of the chart point w: R(H w) = th and every chart point with R *)
(* <= th/2 is closer to the origin.                                          *)

let P2HN_HORN_CHOOSE_W = prove
 (`!top atlas (H:real^3->A) (R:A->real) th.
     mfd_param top atlas {y | &1 / &2 < norm y} H /\
     (!K. compact_in top K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
     continuous_map (top,euclideanreal) R /\
     (!c. compact_in top {p | p IN topspace top /\ R p <= c}) /\
     &0 < th /\ (!z. norm z = &1 ==> R(H z) <= th / &8)
     ==> ?w. &1 < norm w /\ R(H w) = th /\
             (!z. &1 <= norm z /\ R(H z) <= th / &2 ==> norm z < norm w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `{y:real^3 | &1 / &2 < norm y}`; `H:real^3->A`] MFD_PARAM_MAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean {y:real^3 | &1 / &2 < norm y},euclideanreal)
                  ((R:A->real) o (H:real^3->A))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. bounded {z:real^3 | &1 <= norm z /\ (R:A->real)((H:real^3->A) z) <= c}`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `{y:real^3 | &1 <= norm y /\
                  (H:real^3->A) y IN {p | p IN topspace top /\ (R:A->real) p <= c}}` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th -> is_comb(concl th) &&
      is_const(repeat rator (concl th)) && fst(dest_const(repeat rator (concl th))) = "open_in" &&
      can (find_term (fun t -> t = `H:real^3->A`)) (concl th))) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Z2 = {z:real^3 | &1 <= norm z /\ (R:A->real)((H:real^3->A) z) <= th / &2}` THEN
  SUBGOAL_THEN `compact (Z2:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [EXPAND_TAC "Z2" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(R:A->real) o (H:real^3->A)`;
                   `subtopology euclidean {y:real^3 | &1 / &2 < norm y}`; `euclideanreal`;
                   `{x:real | x <= th / &2}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE; CLOSED_IN_CLOSED;
                    TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `Z2 = t INTER {z:real^3 | &1 <= norm z}` SUBST1_TAC THENL
     [EXPAND_TAC "Z2" THEN
      UNDISCH_TAC `{x:real^3 | &1 / &2 < norm x /\ (R:A->real) ((H:real^3->A) x) <= th / &2} =
                   {y | &1 / &2 < norm y} INTER t` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      MESON_TAC[REAL_ARITH `&1 <= x ==> &1 / &2 < x`];
      MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{z:real^3 | &1 <= norm z} = (:real^3) DIFF ball(vec 0,&1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_BALL_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_UNIV; OPEN_BALL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Z2:real^3->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^3` THEN EXPAND_TAC "Z2" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `th / &8` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`norm:real^3->real`; `Z2:real^3->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z3:real^3` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "mx"))) THEN
  EXPAND_TAC "Z2" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[BOUNDED_POS] o SPEC `th:real` o check (fun th ->
    is_forall(concl th) && is_comb(snd(dest_forall(concl th))) &&
    fst(dest_const(rator(snd(dest_forall(concl th))))) = "bounded")) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bB"))) THEN
  ABBREV_TAC `S = max (norm(z3:real^3)) B + &1` THEN
  ABBREV_TAC `q:real^3 = (S / norm(z3:real^3)) % z3` THEN
  SUBGOAL_THEN `&0 < norm(z3:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN segment[z3,q]
                  ==> norm(z3:real^3) <= norm x /\ (~(x = z3) ==> norm z3 < norm x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^3 = ((&1 - u) + u * S / norm(z3:real^3)) % z3` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "q" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(((&1 - u) + u * S / norm(z3:real^3)) % z3) = (&1 - u) * norm z3 + u * S`
    SUBST1_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN
      SUBGOAL_THEN `&0 <= (&1 - u) + u * S / norm(z3:real^3)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
        EXPAND_TAC "S" THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      UNDISCH_TAC `&0 < norm(z3:real^3)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(z3:real^3) < S` ASSUME_TAC THENL [EXPAND_TAC "S" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= u * (S - n) ==> n <= (&1 - u) * n + u * S`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `u = &0` THENL
     [ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO; REAL_ADD_RID; VECTOR_MUL_LID;
                      VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < u * (S - n) ==> n < (&1 - u) * n + u * S`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(q:real^3) = S` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL [EXPAND_TAC "S" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_DIV] THEN
    UNDISCH_TAC `&0 < norm(z3:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | &1 / &2 < norm y}`;
                 `(R:A->real) o (H:real^3->A)`; `segment[z3:real^3,q]`; `z3:real^3`; `q:real^3`;
                 `th:real`] P2HN_CONNECTED_IVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ENDS_IN_SEGMENT; o_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN; CONNECTED_SEGMENT] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `segment[z3:real^3,q]`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "bB" (MP_TAC o SPEC `q:real^3`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(X_CHOOSE_THEN `r:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `segment[z3:real^3,q]`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r:real^3 = z3` THENL
   [UNDISCH_TAC `(R:A->real) ((H:real^3->A) r) = th` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `r:real^3` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  USE_THEN "mx" (MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [EXPAND_TAC "Z2" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ASM_REAL_ARITH_TAC]);;

(* The neck domain contains the annulus from 1/3 to 3 when eps <= 1/4.       *)

let P2HN_NECK_DOM_COLLAR3 = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
         ==> (annulus (&1 / &3) (&3):real^3->bool) SUBSET rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom] THEN
  ABBREV_TAC `t = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&2 <= t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SUBGOAL_THEN `sqrt(&2) <= &2 /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &1 / &4` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= exp t /\ exp(--t) <= &1 / &3` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBST1_TAC(REAL_ARITH `&1 / &3 = inv(&3)`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* Reversal fixes the central sphere.                                        *)

let P2HN_REV_IMAGE_SPHERE = prove
 (`!e:real^3->A. IMAGE (apx_rev e) (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1))`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x:real^3. x IN s ==> (f:real^3->A) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  REWRITE_TAC[IN_SPHERE_0; apx_rev] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID]);;

(* A component of the complement of a neck sphere that contains a collar     *)
(* half contains the point at radius 2 (resp. 1/2) of that side.             *)

let P2HN_NECK_PLUS_POINT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) c.
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &4 /\
     c IN connected_components_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
     ==> (IMAGE e (annulus (&1) (&2)) SUBSET c ==> e(&2 % basis 1) IN c) /\
         (IMAGE e (annulus (&1 / &2) (&1)) SUBSET c ==> e(&1 / &2 % basis 1) IN c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  MP_TAC(SPEC `eps:real` P2HN_NECK_DOM_COLLAR3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. t SUBSET annulus (&1 / &3) (&3) /\ connected t /\ DISJOINT t (sphere(vec 0,&1)) /\
        IMAGE (e:real^3->A) (t INTER annulus (&1 / &2) (&2)) SUBSET c /\
        ~(t INTER annulus (&1 / &2) (&2) = {})
        ==> IMAGE e t SUBSET c`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology top (topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1)))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2HN_PARAM_IMAGE_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `t:real^3->bool`;
                     `sphere(vec 0:real^3,&1)`] P2HN_PARAM_IMAGE_DISJOINT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `annulus (&1 / &3) (&3):real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; annulus; IN_SPHERE_0; IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `t:real^3->bool`]
        MFD_PARAM_IMAGE_SUBSET) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]];
      UNDISCH_TAC `~((t:real^3->bool) INTER annulus (&1 / &2) (&2) = {})` THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (t INTER annulus (&1 / &2) (&2)) SUBSET c` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus (&1) (&3)) SUBSET c` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[P2HN_ANNULUS_CONNECTED] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_SPHERE_0;
                    IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (e:real^3->A) (annulus (&1) (&2))` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `&3 / &2 % basis 1:real^3` THEN
        SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC];
    SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus (&1 / &3) (&1)) SUBSET c` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[P2HN_ANNULUS_CONNECTED] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_SPHERE_0;
                    IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `&3 / &4 % basis 1:real^3` THEN
        SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC]]);;

(* The y-clause of MT Thm 11.31 for a regular view at one time.              *)

let P2HN_YCLAUSE_VIEW = prove
 (`?eps0. &0 < eps0 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      ta en H th dl.
       &0 < en /\ en <= eps0 /\ p2c_regular_view V /\
       apx_sphere_sep (rfs_vtop V ta) (rfs_vatlas V ta) /\
       p3_horn V ta en H /\
       (!c. compact_in (rfs_vtop V ta)
              {p | p IN topspace (rfs_vtop V ta) /\ rfs_vscalar V ta p <= c}) /\
       &0 < th /\ (!z. norm z = &1 ==> rfs_vscalar V ta (H z) <= th / &8) /\
       &0 < dl /\ dl <= en /\
       (!x. x IN p3_horn_set H /\ rfs_vscalar V ta x = th
            ==> ?e. rfs_evolving_neck V dl x ta (&2) e /\
                    IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set H)
       ==> ?y e R1. y IN p3_horn_set H /\ rfs_vscalar V ta y = th /\
                    rfs_evolving_neck V dl y ta (&2) e /\
                    IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set H /\
                    (!z. R1 <= norm z ==> H z IN p3_horn_end (rfs_vtop V ta) H e) /\
                    (!p. p IN p3_horn_end (rfs_vtop V ta) H e ==> th / &4 < rfs_vscalar V ta p) /\
                    connected_component_of
                      (subtopology (rfs_vtop V ta)
                                   (topspace (rfs_vtop V ta) DIFF IMAGE e (sphere(vec 0,&1))))
                      (e(&2 % basis 1)) SUBSET IMAGE H {z | &1 < norm z}`,
  X_CHOOSE_THEN `eF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fs"))
    (INST_TYPE [`:A`,`:A`] P2HN_HORN_FAR_SIDE) THEN
  EXISTS_TAC `min eF (&1 / &4)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `ta:real`; `en:real`; `H:real^3->A`; `th:real`; `dl:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_HORN_SET_TOPSPACE) THEN DISCH_TAC THEN
  UNDISCH_TAC `p3_horn (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta en H` THEN
  REWRITE_TAC[p3_horn] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "hnk") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `hausdorff_space (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta) /\
                smooth_manifold_atlas (rfs_vtop V ta) (rfs_vatlas V ta) /\
                riemannian_metric (rfs_vatlas V ta) (rfs_vmetric V ta)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN
    DISCH_THEN(MP_TAC o SPEC `ta:real` o el 0 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(H:real^3->A) (basis 1)` THEN
    UNDISCH_TAC `p3_horn_set (H:real^3->A) SUBSET topspace (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[p3_horn_set] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    SIMP_TAC[IN_ELIM_THM; NORM_BASIS; DIMINDEX_3; ARITH; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. &1 <= norm y
                    ==> ?e. rfs_neck (rfs_vtop V ta,rfs_vatlas V ta) (rfs_vmetric V ta) en
                              ((H:real^3->A) y) e`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "hnk" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[P2HN_STRONG_NECK_SLICE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                 `H:real^3->A`;
                 `rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                 `th:real`] P2HN_HORN_CHOOSE_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta =
                  mfd_scalar (rfs_vatlas V ta) (rfs_vmetric V ta)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; P2BN_RFS_VSCALAR];
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(H:real^3->A) w IN p3_horn_set H` ASSUME_TAC THENL
   [REWRITE_TAC[p3_horn_set] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(H:real^3->A) w` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop V ta,rfs_vatlas V ta) (rfs_vmetric V ta) en
                  ((H:real^3->A) w) (e0:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_evolving_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) dl ((H:real^3->A) w) ta (&2) e0` THEN
    REWRITE_TAC[P2BN_EVOLVING_NECK_ALT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "fs" (MP_TAC o SPECL
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
    `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
    `H:real^3->A`; `en:real`; `th:real`; `e0:real^3->A`; `w:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM P2BN_RFS_VSCALAR] THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `sg:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (H:real^3->A) sg SUBSET
                (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta)
                closure_of IMAGE H (outside sg)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `{y:real^3 | &1 / &2 < norm y}`; `H:real^3->A`] MFD_PARAM_MAPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `H':A->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (H:real^3->A)
                  ((subtopology euclidean {y:real^3 | &1 / &2 < norm y}) closure_of outside sg)` THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    SUBGOAL_THEN `{y:real^3 | &1 / &2 < norm y} INTER outside sg = outside sg` SUBST1_TAC THENL
     [UNDISCH_TAC `outside sg SUBSET {y:real^3 | &1 < norm y}` THEN
      REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `&1 < x ==> &1 / &2 < x`];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(sg:real^3->bool) SUBSET {y | &1 < norm y}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[REAL_ARITH `&1 < x ==> &1 / &2 < x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart (rfs_vtop V ta) (rfs_vatlas V ta) (e0:real^3->A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `en:real`; `(H:real^3->A) w`; `e0:real^3->A`] P2HN_NECK_CHART_OF_NECK) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                 `e0:real^3->A`; `IMAGE (H:real^3->A) (outside sg)`] P2HN_SIDE_COLLAR_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `IMAGE (H:real^3->A) sg`)) THEN
    SUBGOAL_THEN `~(sg:real^3->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(sg:real^3->bool) homeomorphic sphere(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `?e. rfs_evolving_neck V dl ((H:real^3->A) w) ta (&2) e /\
                    IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set H /\
                    IMAGE e (sphere(vec 0,&1)) = IMAGE (e0:real^3->A) (sphere(vec 0,&1)) /\
                    e(&2 % basis 1) IN IMAGE H (outside sg)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta`;
                   `en:real`; `(H:real^3->A) w`; `e0:real^3->A`;
                   `IMAGE (H:real^3->A) (outside sg)`] P2HN_NECK_PLUS_POINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [EXISTS_TAC `apx_rev (e0:real^3->A)` THEN
      ASM_SIMP_TAC[P2HN_EVNECK_REV; APX_REV_IMAGE_DOM; P2HN_REV_IMAGE_SPHERE] THEN
      REWRITE_TAC[apx_rev] THEN
      SUBGOAL_THEN `inv(norm(&2 % basis 1:real^3) pow 2) % (&2 % basis 1:real^3) =
                    &1 / &2 % basis 1` SUBST1_TAC THENL
       [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; VECTOR_MUL_ASSOC; REAL_ABS_NUM] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `e0:real^3->A` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(H:real^3->A) w`; `e:real^3->A`; `R1:real`] THEN
  ASM_REWRITE_TAC[p3_horn_end] THEN
  ABBREV_TAC `S0 = IMAGE (e0:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `cp = IMAGE (H:real^3->A) (outside sg)` THEN
  ABBREV_TAC `top0 = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ta` THEN
  SUBGOAL_THEN `connected_in top0 (cp:A->bool) /\ cp SUBSET topspace top0 DIFF (S0:A->bool)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF o check (fun th ->
      not(is_forall(concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_components_of"))
          (concl th))) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET o check (fun th ->
      not(is_forall(concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_components_of"))
          (concl th))) THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cp SUBSET p3_horn_set (H:real^3->A)` ASSUME_TAC THENL
   [EXPAND_TAC "cp" THEN REWRITE_TAC[p3_horn_set] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `outside sg SUBSET {y:real^3 | &1 < norm y}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) (&2 % basis 1) IN topspace top0 DIFF S0 /\
                e (&2 % basis 1) IN p3_horn_set (H:real^3->A) DIFF S0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(e:real^3->A) (&2 % basis 1) IN cp` THEN
    UNDISCH_TAC `cp SUBSET p3_horn_set (H:real^3->A)` THEN
    UNDISCH_TAC `cp SUBSET topspace top0 DIFF (S0:A->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cp SUBSET connected_component_of
                  (subtopology top0 (p3_horn_set (H:real^3->A) DIFF S0)) ((e:real^3->A)(&2 % basis 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    UNDISCH_TAC `cp SUBSET p3_horn_set (H:real^3->A)` THEN
    UNDISCH_TAC `cp SUBSET topspace top0 DIFF (S0:A->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tp:A topology x:A s. x IN topspace tp /\ s = connected_component_of tp x
                    ==> connected_in tp s /\ s SUBSET topspace tp /\ x IN s`
  (LABEL_TAC "cc") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF;
      CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:A->bool. connected_in top0 s /\ s SUBSET topspace top0 DIFF S0 /\
                            (e:real^3->A)(&2 % basis 1) IN s ==> s SUBSET cp`
  (LABEL_TAC "mx") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology top0 (topspace top0 DIFF (S0:A->bool))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    UNDISCH_TAC `(e:real^3->A) (&2 % basis 1) IN cp` THEN
    UNDISCH_TAC `(e:real^3->A) (&2 % basis 1) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `cp SUBSET connected_component_of
                  (subtopology top0 (p3_horn_set (H:real^3->A) DIFF S0)) ((e:real^3->A)(&2 % basis 1))` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "cp" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:A) IN cp` ASSUME_TAC THENL
     [USE_THEN "cc" (MP_TAC o SPECL [`subtopology top0 (p3_horn_set (H:real^3->A) DIFF S0)`;
        `(e:real^3->A)(&2 % basis 1)`;
        `connected_component_of (subtopology top0 (p3_horn_set (H:real^3->A) DIFF S0))
           ((e:real^3->A)(&2 % basis 1))`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
        UNDISCH_TAC `(e:real^3->A) (&2 % basis 1) IN topspace top0 DIFF S0` THEN
        UNDISCH_TAC `(e:real^3->A) (&2 % basis 1) IN p3_horn_set (H:real^3->A) DIFF S0` THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN STRIP_TAC THEN
      USE_THEN "mx" (MP_TAC o SPEC `connected_component_of (subtopology top0 (p3_horn_set (H:real^3->A) DIFF S0))
           ((e:real^3->A)(&2 % basis 1))`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `connected_component_of (subtopology top0 (p3_horn_set (H:real^3->A) DIFF S0))
           ((e:real^3->A)(&2 % basis 1)) SUBSET topspace top0 INTER (p3_horn_set H DIFF S0)` THEN
        SET_TAC[];
        UNDISCH_TAC `(p:A) IN connected_component_of (subtopology top0 (p3_horn_set (H:real^3->A) DIFF S0))
           ((e:real^3->A)(&2 % basis 1))` THEN SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `th / &4`)) (concl th))) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cp:A->bool` THEN CONJ_TAC THENL
     [USE_THEN "cc" (MP_TAC o SPECL [`subtopology top0 (topspace top0 DIFF (S0:A->bool))`;
        `(e:real^3->A)(&2 % basis 1)`;
        `connected_component_of (subtopology top0 (topspace top0 DIFF (S0:A->bool)))
           ((e:real^3->A)(&2 % basis 1))`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
        UNDISCH_TAC `(e:real^3->A) (&2 % basis 1) IN topspace top0 DIFF S0` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN STRIP_TAC THEN
      USE_THEN "mx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `connected_component_of (subtopology top0 (topspace top0 DIFF (S0:A->bool)))
           ((e:real^3->A)(&2 % basis 1)) SUBSET topspace top0 INTER (topspace top0 DIFF S0)` THEN
      SET_TAC[];
      EXPAND_TAC "cp" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The route of MT Thm 11.31.  The                                           *)
(* function hf is chosen from P2HN_1131_CORE (Skolemized at C, eps) with     *)
(* the extra caps hf <= rho dl / 2 and hf <= rho / (16 C); clause (i) is     *)
(* the core shortened to length 1 and dl, the y-clause is                    *)
(* P2HN_YCLAUSE_VIEW at the horizon of the maximal extension with            *)
(* th = hf(dl r0, dl)^-2 and the neck size min dl (2 eps).                   *)
(* ========================================================================= *)

let P2HN_THM_11_31_ROUTE = prove
 (`!u:A->bool. P2C_THM_11_31_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_THM_11_31_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2HN_1131_CORE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "core"))) THEN
  MP_TAC(SPEC `u:A->bool` P2HN_HIST_PACK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `eH:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hp"))))))) THEN
  X_CHOOSE_THEN `eY:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "yc"))
    (INST_TYPE [`:A`,`:A`] P2HN_YCLAUSE_VIEW) THEN
  REWRITE_TAC[P2C_THM_11_31_STATEMENT] THEN
  EXISTS_TAC `min eC (min eH (min (eY / &2) (&1 / &8)))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`] THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  USE_THEN "core" (fun th -> MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
    (REWRITE_RULE[ASSUME `&1 < C`; ASSUME `&0 < eps`; ASSUME `eps <= eC`]
      (SPECL [`C:real`; `eps:real`] th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `hc:real->real->real->real` (LABEL_TAC "hc")) THEN
  EXISTS_TAC `\rho dl. if &0 < rho /\ &0 < dl /\ dl < &1
                       then min (hc (rho / dl) (rho / (&2 * C)) (min dl (&2 * eps)))
                                (min (rho * dl) (rho / (&16 * C))) / &2
                       else min (rho * dl) (rho / (&2 * C)) / &2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3_hfun] THEN BETA_TAC THEN MAP_EVERY X_GEN_TAC [`rho:real`; `dl:real`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < rho * dl /\ &0 < rho / (&2 * C) /\ &0 < rho / (&16 * C) /\
                  rho / (&16 * C) <= rho / (&2 * C)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [USE_THEN "hc" (MP_TAC o SPECL [`rho / dl`; `rho / (&2 * C)`; `min dl (&2 * eps)`]) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[];
          REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `r0:real`; `gl:A->real^3^3`; `dl:real`;
                       `H:real^3->A`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `hv = (\rho dl. if &0 < rho /\ &0 < dl /\ dl < &1
                       then min (hc (rho / dl) (rho / (&2 * C)) (min dl (&2 * eps)))
                                (min (rho * dl) (rho / (&16 * C))) / &2
                       else min (rho * dl) (rho / (&2 * C)) / &2) (dl * r0) dl` THEN
  SUBGOAL_THEN `&0 < dl * r0 /\ (dl * r0) / dl = r0 /\ &0 < (dl * r0) / (&2 * C) /\
                &0 < min dl (&2 * eps) /\ &0 < (dl * r0) * dl /\ &0 < (dl * r0) / (&16 * C)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < dl * r0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < dl` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "hc" (MP_TAC o SPECL [`r0:real`; `(dl * r0) / (&2 * C)`; `min dl (&2 * eps)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cor")) THEN
  SUBGOAL_THEN `&0 < hv /\ hv <= hc r0 ((dl * r0) / (&2 * C)) (min dl (&2 * eps)) /\
                hv <= ((dl * r0) * dl) / &2 /\ hv <= ((dl * r0) / (&16 * C)) / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hv" THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < (dl * r0) * dl` THEN UNDISCH_TAC `&0 < (dl * r0) / (&16 * C)` THEN
    UNDISCH_TAC `&0 < (hc:real->real->real->real) r0 ((dl * r0) / (&2 * C)) (min dl (&2 * eps))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && is_var(rand(concl th)) &&
    fst(dest_var(rand(concl th))) = "hv")) THEN
  USE_THEN "cor" (X_CHOOSE_THEN `ef:(A)rfs_history->(A->real^3^3)->(real^3->A)->A->real^3->A`
    (LABEL_TAC "ef")) THEN
  USE_THEN "hp" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                                 `gl:A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sepT")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cptT")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "topT") (LABEL_TAC "RT"))))))))) THEN
  SUBGOAL_THEN `p3_horn_set (H:real^3->A) SUBSET p3_omega hs` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2HN_HORN_SET_TOPSPACE o check (fun th ->
      let c = concl th in is_comb c && is_const(repeat rator c) &&
      fst(dest_const(repeat rator c)) = "p3_horn")) THEN
    USE_THEN "topT" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN p3_horn_set H /\
                      inv(hc r0 ((dl * r0) / (&2 * C)) (min dl (&2 * eps)) pow 2) <=
                      mfd_scalar (hs_atlas hs (hs_count hs)) gl x
                      ==> rfs_evolving_neck (p3_maxext hs (p3_omega hs) gl)
                            (min dl (&2 * eps)) x (rfs_horizon hs) (&2)
                            (ef hs gl H x) /\
                          IMAGE (ef hs gl H x) (rfs_neck_dom (min dl (&2 * eps))) SUBSET
                          p3_horn_set H`
  (LABEL_TAC "nk") THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "ef" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(dl * r0) / (&2 * C) = dl * r0 / (&2 * C)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(hc r0 ((dl * r0) / (&2 * C)) (min dl (&2 * eps)) pow 2) <= inv(hv pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(hv pow 2)` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    EXISTS_TAC `(ef:(A)rfs_history->(A->real^3^3)->(real^3->A)->A->real^3->A) hs gl H x` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[rfs_strong_neck] THEN MATCH_MP_TAC P2HN_REG_EVNECK_MONO THEN
      EXISTS_TAC `min dl (&2 * eps)` THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2HN_EVNECK_SHORTEN THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((ef:(A)rfs_history->(A->real^3^3)->(real^3->A)->A->real^3->A) hs gl H x)
                        (rfs_neck_dom (min dl (&2 * eps)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_NECK_DOM_MONO THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hv <= ((dl * r0) / (&2 * C)) / &16 /\ hv <= (dl * r0) / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `((dl * r0) / (&16 * C)) / &2 = ((dl * r0) / (&2 * C)) / &16`
       (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
      SUBGOAL_THEN `~(C = &0)` MP_TAC THENL
       [UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      SUBGOAL_THEN `(dl * r0) * dl <= dl * r0` MP_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        UNDISCH_TAC `&0 < dl * r0` THEN UNDISCH_TAC `dl < &1` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `hv <= ((dl * r0) * dl) / &2` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * hv pow 2 <= ((dl * r0) / (&2 * C)) pow 2 /\
                &4 * hv pow 2 <= (dl * r0) pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x. (x / &16) pow 2 = x pow 2 / &256 /\ (x / &2) pow 2 = x pow 2 / &4`
    (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`2`; `hv:real`; `((dl * r0) / (&2 * C)) / &16`] REAL_POW_LE2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `!x. (x / &16) pow 2 = x pow 2 / &256` (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MP_TAC(SPEC `(dl * r0) / (&2 * C)` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      MP_TAC(SPECL [`2`; `hv:real`; `(dl * r0) / &2`] REAL_POW_LE2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `!x. (x / &2) pow 2 = x pow 2 / &4` (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < hv pow 2 /\ &0 < ((dl * r0) / (&2 * C)) pow 2 /\ &0 < (dl * r0) pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(((dl * r0) / (&2 * C)) pow 2) <= inv(hv pow 2) / &8 /\
                inv((dl * r0) pow 2) <= inv(hv pow 2) / &4 /\ &0 < inv(hv pow 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `&0 < hv pow 2` THEN
      UNDISCH_TAC `&8 * hv pow 2 <= ((dl * r0) / (&2 * C)) pow 2` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `&0 < hv pow 2` THEN
      UNDISCH_TAC `&4 * hv pow 2 <= (dl * r0) pow 2` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "yc" (MP_TAC o SPECL
   [`p3_maxext (hs:(A)rfs_history) (p3_omega hs) (gl:A->real^3^3)`; `rfs_horizon (hs:(A)rfs_history)`;
    `&2 * eps`; `H:real^3->A`; `inv(hv pow 2)`; `min dl (&2 * eps)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `eps <= eY / &2` THEN REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (H:real^3->A) (sphere(vec 0,&1)) SUBSET
                   p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) (gl:A->real^3^3)
                                (dl * r0 / (&2 * C))` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; p3_omega_rho; IN_ELIM_THM; IN_SPHERE_0] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "RT" (fun th -> ASM_SIMP_TAC[th]) THEN
      SUBGOAL_THEN `dl * r0 / (&2 * C) = (dl * r0) / (&2 * C)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(((dl * r0) / (&2 * C)) pow 2)` THEN
      ASM_REWRITE_TAC[];
      REAL_ARITH_TAC;
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      EXISTS_TAC `(ef:(A)rfs_history->(A->real^3^3)->(real^3->A)->A->real^3->A) hs gl H x` THEN
      USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN p3_omega hs` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN p3_horn_set H` THEN
        UNDISCH_TAC `p3_horn_set (H:real^3->A) SUBSET p3_omega hs` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "RT" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP th (ASSUME `(x:A) IN p3_omega hs`)])) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `R1:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`y:A`; `e:real^3->A`; `R1:real`] THEN
  SUBGOAL_THEN `(y:A) IN p3_omega hs` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN p3_horn_set H` THEN
    UNDISCH_TAC `p3_horn_set (H:real^3->A) SUBSET p3_omega hs` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `p3_omega(hs:(A)rfs_history)`; `gl:A->real^3^3`]
    P2HN_MAXEXT_HORIZON) THEN
  DISCH_THEN(fun th -> let th1 = CONJUNCT1 th in
    RULE_ASSUM_TAC(REWRITE_RULE[th1]) THEN ASSUME_TAC th1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "RT" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(y:A) IN p3_omega hs`))]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2HN_REG_EVNECK_MONO THEN EXISTS_TAC `min dl (&2 * eps)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom (min dl (&2 * eps)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_NECK_DOM_MONO THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; p3_omega_rho; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:A) IN p3_omega hs` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:A) IN p3_horn_end (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) H e` THEN
      REWRITE_TAC[p3_horn_end] THEN
      MP_TAC(ISPECL [`subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
                        (p3_horn_set (H:real^3->A) DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1)))`;
                     `(e:real^3->A)(&2 % basis 1)`] CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `inv(hv pow 2) / &4`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "RT" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(p:A) IN p3_omega hs`)]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv((dl * r0) pow 2)` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `subtopology (hs_top hs (hs_count hs)) (p3_omega hs DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))) =
                  subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
                    (p3_omega hs DIFF IMAGE e (sphere(vec 0,&1)))` SUBST1_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN SET_TAC[];
      ASM_REWRITE_TAC[]]] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_component_of")) (concl th) &&
    can (find_term (aconv `IMAGE (H:real^3->A) {z | &1 < norm z}`)) (concl th))) THEN
  USE_THEN "topT" (fun th -> REWRITE_TAC[th]));;

