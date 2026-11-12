(* ========================================================================= *)
(* Unit pc_p2b_cone6: steps (A) and (B) of the blow-up of MT Sec 10.6.  A    *)
(* point x of a regular view that is the centre of an evolving neck, all of  *)
(* whose points in the rescaled unit ball are neck centres with scalar       *)
(* curvature at most C R(x), gives after rescaling by R(x) the hypotheses of *)
(* P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT with r1 = 1: compact closure of the *)
(* unit ball, persistence on (-len/C,0], the bound K1 C on Rm there, and a   *)
(* volume lower bound (P2BK_NECK_REQN_HYPS, a general R1/R2-from-neck-data   *)
(* lemma).                                                                   *)
(* ========================================================================= *)

needs "src/pc_p2b_neckbd.ml";;
needs "src/pc_p2b_vscale.ml";;
needs "src/pc_p2b_cscale.ml";;
needs "src/pc_rfa_shiscale.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Views.  Persistence at a time, monotonicity in the lower end, the         *)
(* identity diffeos of a regular view carry parametrizations of the time-0   *)
(* slice to earlier slices, balls of views, the slices of a view rescaled at *)
(* time 0, and compact closures of sets inside a compact parametrized image. *)
(* ------------------------------------------------------------------------- *)

let P2BK_PERSISTS_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s.
     rfs_persists V W a b /\ a < s /\ s <= b
     ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
         open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas] THEN MESON_TAC[]);;

let P2BK_DIV_LZERO = prove
 (`!x. &0 / x = &0`,
  REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let P2BK_INV_LE_EQ = prove
 (`!a b. &0 < a ==> (inv a <= b <=> &1 <= b * a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv a = &1 / a` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

let P2BK_PERSISTS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a a' b.
     rfs_persists V W a b /\ a <= a' ==> rfs_persists V W a' b`,
  REWRITE_TAC[P2BN_PERSISTS_ALT] THEN MESON_TAC[REAL_LET_TRANS]);;

let P2BK_VBALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t x r.
     rfs_vball V t x r = mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2BK_RV0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    Q s x r.
     rfs_vtop (p2b_rescale_view V (&0) Q) s = rfs_vtop V (s / Q) /\
     rfs_vatlas (p2b_rescale_view V (&0) Q) s = rfs_vatlas V (s / Q) /\
     rfs_vmetric (p2b_rescale_view V (&0) Q) s = (\y. Q %% rfs_vmetric V (s / Q) y) /\
     rfs_vball (p2b_rescale_view V (&0) Q) s x r =
     mfd_ball (rfs_vtop V (s / Q),rfs_vatlas V (s / Q)) (\y. Q %% rfs_vmetric V (s / Q) y) x r`,
  REWRITE_TAC[P2BK_VBALL; P2BK_VS_PARTS; REAL_ADD_LID]);;

let P2BK_COMPACT_CLOSURE_IN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) k W.
     hausdorff_space top /\ mfd_param top atlas s e /\ compact k /\ k SUBSET s /\
     W SUBSET IMAGE e k
     ==> compact_in top (top closure_of W)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact_in top (IMAGE (e:real^N->A) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `IMAGE (e:real^N->A) k` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
  ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN]);;

let P2BK_ARITH_TIME = prove
 (`!len C Q Ry s.
     &0 < len /\ &1 <= C /\ &0 < Q /\ &0 < Ry /\ Ry <= C * Q /\ --len / C < s
     ==> --len / Ry < s / Q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(C * Q) <= inv Ry` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(--len / C) / Q < s / Q` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(--len / C) / Q = --(len * inv(C * Q))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `len * inv(C * Q) <= len * inv Ry` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2BK_VIEW_PARAM_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a s (e:real^3->A) t.
     p2c_regular_view V /\ rfs_persists V W a (&0) /\ a < t /\ t <= &0 /\
     mfd_param (rfs_vtop V (&0)) (rfs_vatlas V (&0)) s e /\ IMAGE e s SUBSET W
     ==> mfd_param (rfs_vtop V t) (rfs_vatlas V t) s e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_diffeo (rfs_vtop V t) (rfs_vatlas V t) W
                           (rfs_vtop V (&0)) (rfs_vatlas V (&0)) W (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view
                  (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                 `s:real^3->bool`; `e:real^3->A`; `W:A->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`] MFD_PARAM_COMPOSE_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN
    SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[P2BK_PERSISTS_AT; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* One neck.  For an eps-neck at x of a slice, the unit ball of the metric   *)
(* rescaled by R(x) lies in the compact core of the neck, so its closure is  *)
(* compact and (for eps small) it has volume at least pi/750 min(1,1/sqrt K) *)
(* ^ 3 when |Rm|(x) <= K R(x); for an evolving neck in a regular view the    *)
(* rescaled unit ball persists on (a/R(x),0] for -len <= a < 0, and |Rm| at  *)
(* the centre is at most K1 R(x) back to time -len/R(x) (P2BN_EVNECK_RM).    *)
(* ------------------------------------------------------------------------- *)

let P2BK_NECK_BALL_CORE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A).
     hausdorff_space top /\ riemannian_metric atlas g /\ &0 < eps /\ eps <= &1 / &10 /\
     rfs_neck (top,atlas) g eps x e
     ==> mfd_scalar atlas (\z. mfd_scalar atlas g x %% g z) x = &1 /\
         mfd_ball (top,atlas) (\z. mfd_scalar atlas g x %% g z) x (&1) SUBSET
         IMAGE e (cball(vec 0,exp(&3)) DIFF ball(vec 0,exp(--(&3))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  SUBGOAL_THEN `mfd_scalar atlas (\z. mfd_scalar atlas g x %% (g:A->real^3^3) z) x = &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `mfd_scalar atlas (g:A->real^3^3) x`; `x:A`] P2BCS_SCALAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_DIV_REFL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BN_NECK_BALL_IN THEN
  EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[REAL_LT_01; SQRT_1; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL; P2BCS_NECK_CMUL] THEN REAL_ARITH_TAC);;

let P2BK_NECK_BALL_COMPACT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A).
     hausdorff_space top /\ riemannian_metric atlas g /\ &0 < eps /\ eps <= &1 / &10 /\
     rfs_neck (top,atlas) g eps x e
     ==> compact_in top
           (top closure_of mfd_ball (top,atlas) (\z. mfd_scalar atlas g x %% g z) x (&1))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BK_COMPACT_CLOSURE_IN) THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`;
                        `e:real^3->A`;
                        `cball(vec 0:real^3,exp(&3)) DIFF ball(vec 0,exp(--(&3)))`] THEN
  MP_TAC(SPEC `eps:real` P2BN_NECK_CORE_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`] P2BK_NECK_BALL_CORE) THEN
    ASM_SIMP_TAC[]]);;

let P2BK_NECK_BALL_VOL = prove
 (`?eps1. &0 < eps1 /\ eps1 <= &1 / &10 /\
     !top atlas (g:A->real^3^3) eps x (e:real^3->A) K.
        hausdorff_space top /\ riemannian_metric atlas g /\ &0 < eps /\ eps <= eps1 /\
        rfs_neck (top,atlas) g eps x e /\ &0 < K /\
        mfd_rm_norm atlas g x <= K * mfd_scalar atlas g x
        ==> ?v. mfd_has_volume (top,atlas) (\z. mfd_scalar atlas g x %% g z)
                  (mfd_ball (top,atlas) (\z. mfd_scalar atlas g x %% g z) x (&1)) v /\
                pi / &750 * min (&1) (inv(sqrt K)) pow 3 <= v`,
  X_CHOOSE_THEN `eps2:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] P2BN_NECK_BALL_VOLUME) THEN
  EXISTS_TAC `min eps2 (&1 / &10)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`eps:real`; `e:real^3->A`] THEN
  ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL; P2BCS_NECK_CMUL; REAL_LT_01] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `mfd_scalar atlas (g:A->real^3^3) x`; `x:A`;
                   `K * mfd_scalar atlas (g:A->real^3^3) x`] RFA_MFD_RM_NORM_CMUL_LE) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `(K * mfd_scalar atlas (g:A->real^3^3) x) / mfd_scalar atlas g x = K`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x` THEN CONV_TAC REAL_FIELD;
      SIMP_TAC[]];
    MATCH_MP_TAC P2BK_NECK_BALL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `e:real^3->A`] THEN ASM_REWRITE_TAC[]]);;

let P2BK_NECK_PERSIST_BALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x len e a.
     p2c_regular_view V /\ &0 < eps /\ eps <= &1 / &10 /\
     rfs_evolving_neck V eps x (&0) len e /\ --len <= a /\ a < &0
     ==> rfs_persists V
           (mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0))
                     (\z. rfs_vscalar V (&0) x %% rfs_vmetric V (&0) z) x (&1))
           (a / rfs_vscalar V (&0) x) (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR] THEN
  INTRO_TAC "reg eps eps1 (neck len pers close) a1 a2" THEN
  USE_THEN "neck" (STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  SUBGOAL_THEN `hausdorff_space (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) /\
                riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "reg" (MP_TAC o SPEC `&0` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(x:A) IN topspace (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))` THEN
      SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BK_NECK_BALL_CORE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2BN_NECK_CORE_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                    (rfs_vmetric V (&0)) x` THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas V (&0))
                  (\z. R %% rfs_vmetric (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC P2BN_PERSISTS_COVER THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO];
    MAP_EVERY X_GEN_TAC [`N:A->bool`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "reg" (MP_TAC o SPECL [`N:A->bool`; `a / R`; `&0`; `s:real`] o
                    el 3 o CONJUNCTS o REWRITE_RULE[p2c_regular_view]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[mfd_diffeo];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL; REAL_LT_01];
    MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(w:A) IN mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0))
                  (\z. R %% rfs_vmetric (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) z)
                  x (&1)`;
        `mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0))
                  (\z. R %% rfs_vmetric (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) z)
                  x (&1) SUBSET
         IMAGE (e:real^3->A) (cball(vec 0,exp(&3)) DIFF ball(vec 0,exp(--(&3))))`;
        `cball(vec 0:real^3,exp(&3)) DIFF ball(vec 0,exp(--(&3))) SUBSET rfs_neck_dom eps`] THEN
      SET_TAC[];
      REWRITE_TAC[P2BN_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "pers" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a / R` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div; REAL_ARITH `&0 - x * y = --x * y`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]]]);;

let P2BK_NECK_RM_AT = prove
 (`?K1. &0 < K1 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      eps y len e u.
        p2c_regular_view V /\ &0 < eps /\ eps <= &1 / &4 /\
        rfs_evolving_neck V eps y (&0) len e /\
        --len / rfs_vscalar V (&0) y < u /\ u <= &0
        ==> smooth_manifold_atlas (rfs_vtop V u) (rfs_vatlas V u) /\
            riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u) /\
            y IN topspace (rfs_vtop V u) /\
            mfd_rm_norm (rfs_vatlas V u) (rfs_vmetric V u) y <= K1 * rfs_vscalar V (&0) y`,
  X_CHOOSE_THEN `K1:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] P2BN_EVNECK_RM) THEN
  EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "reg eps eps1 evn u1 u2" THEN
  USE_THEN "evn" (STRIP_ASSUME_TAC o REWRITE_RULE[P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  SUBGOAL_THEN `&0 - len / rfs_vscalar V (&0) y < u /\
                &0 < rfs_vscalar (V:(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) y`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
    UNDISCH_TAC `--len / rfs_vscalar (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) y < u` THEN
    REWRITE_TAC[P2BN_RFS_VSCALAR; real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop V u) (rfs_vatlas V u) /\
                open_in (rfs_vtop V u)
                        (IMAGE (e:real^3->A) (rfs_neck_dom eps))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `&0 - len / rfs_vscalar (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) y < u` THEN
    ASM_REWRITE_TAC[P2BN_RFS_VSCALAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace (rfs_vtop V u)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u:A->real^3^3)`
  ASSUME_TAC THENL
   [USE_THEN "reg" (MP_TAC o SPEC `u:real` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(y:A) IN topspace (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)` THEN
      SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)`;
                                `eps:real`; `y:A`; `&0`; `len:real`; `e:real^3->A`;
                                `u * rfs_vscalar (V:(real->A topology)#
                                       (real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) (&0) y`]) THEN
  SUBGOAL_THEN `&0 + (u * rfs_vscalar V (&0) (y:A)) / rfs_vscalar V (&0) y = u`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < rfs_vscalar (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) y` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `--len / rfs_vscalar (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) y < u` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2BK_VIEW_PARAM_AT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                          `&0 - len / rfs_vscalar (V:(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&0) y`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; P2BN_PERSISTS_ALT] THEN CONJ_TAC THENL
     [REWRITE_TAC[P2BN_RFS_VSCALAR] THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `rfs_neck (rfs_vtop V (&0),rfs_vatlas V (&0))
                     (rfs_vmetric (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                     eps y (e:real^3->A)` THEN
      SIMP_TAC[rfs_neck]]]);;

(* ------------------------------------------------------------------------- *)
(* The R1/R2 hypotheses of P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT from neck   *)
(* data.  If x is the centre of an evolving eps-neck of length len in a      *)
(* regular view and every point y of the unit ball of R(x) g(0) about x is   *)
(* the centre of such a neck with R(y) <= C R(x), then the view rescaled by  *)
(* R(x) at time 0 has: compact closure of the unit ball about x, its         *)
(* persistence on (-len/C,0], |Rm| <= K1 C there, and volume at least pi/750 *)
(* min(1,1/sqrt K1)^3 at time 0.  General: reusable for any family of necks  *)
(* with a scalar curvature ratio bound.                                      *)
(* ------------------------------------------------------------------------- *)

let P2BK_NECK_REQN_HYPS = prove
 (`?eps1 K1. &0 < eps1 /\ &0 < K1 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      eps x len e C.
        p2c_regular_view V /\ &0 < eps /\ eps <= eps1 /\ &1 <= C /\
        rfs_evolving_neck V eps x (&0) len e /\
        (!y. y IN mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0))
                           (\z. rfs_vscalar V (&0) x %% rfs_vmetric V (&0) z) x (&1)
             ==> (?e'. rfs_evolving_neck V eps y (&0) len e') /\
                 rfs_vscalar V (&0) y <= C * rfs_vscalar V (&0) x)
        ==> p2c_regular_view (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) /\
            x IN topspace (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0)) /\
            compact_in (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0))
              (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0) closure_of
               rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0) x (&1)) /\
            rfs_persists (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x))
              (rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0) x (&1))
              (--len / C) (&0) /\
            (!s y. --len / C < s /\ s <= &0 /\
                   y IN rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0) x (&1)
                   ==> mfd_rm_norm
                         (rfs_vatlas (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) s)
                         (rfs_vmetric (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) s) y
                       <= K1 * C) /\
            (?v. mfd_has_volume
                   (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0),
                    rfs_vatlas (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0))
                   (rfs_vmetric (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0))
                   (rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) x)) (&0) x (&1))
                   v /\
                 pi / &750 * min (&1) (inv(sqrt K1)) pow 3 <= v)`,
  X_CHOOSE_THEN `eps2:real` STRIP_ASSUME_TAC P2BK_NECK_BALL_VOL THEN
  X_CHOOSE_THEN `K1:real` STRIP_ASSUME_TAC P2BK_NECK_RM_AT THEN
  MAP_EVERY EXISTS_TAC [`eps2:real`; `K1:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "reg eps eps1 C evn nbhd" THEN
  REWRITE_TAC[P2BK_RV0; P2BK_DIV_LZERO] THEN
  USE_THEN "evn" (STRIP_ASSUME_TAC o REWRITE_RULE[P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  SUBGOAL_THEN `&0 < rfs_vscalar V (&0) (x:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2BN_RFS_VSCALAR]; ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (rfs_vtop V (&0)) /\
                riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0):A->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "reg" (MP_TAC o SPEC `&0` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(x:A) IN topspace (rfs_vtop V (&0))` THEN SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ &0 < C` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BK_REGULAR_VIEW_RESCALE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`rfs_vtop V (&0):A topology`; `rfs_vatlas V (&0):((A->bool)#(A->real^3))->bool`;
                   `rfs_vmetric V (&0):A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`]
                  P2BK_NECK_BALL_COMPACT) THEN
    ASM_REWRITE_TAC[P2BN_RFS_VSCALAR];
    ASM_SIMP_TAC[P2BK_PERSISTS_RESCALE; P2BK_DIV_LZERO; REAL_ADD_LID] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`;
                   `eps:real`; `x:A`; `len:real`; `e:real^3->A`; `--len / C`]
                  P2BK_NECK_PERSIST_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= len * (C - &1) ==> --len * C <= --len`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "nbhd" (MP_TAC o SPEC `y:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e':real^3->A`) ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < rfs_vscalar V (&0) (y:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_evolving_neck V eps (y:A) (&0) len (e':real^3->A)` THEN
      REWRITE_TAC[P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR] THEN
      MESON_TAC[P2BN_NECK_CENTRE_FACTS];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL
      [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `eps:real`; `y:A`; `len:real`; `e':real^3->A`; `s / rfs_vscalar V (&0) (x:A)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2BK_ARITH_TIME THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]];
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(K1 * rfs_vscalar V (&0) (y:A)) / rfs_vscalar V (&0) (x:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN
      EXISTS_TAC `rfs_vtop V (s / rfs_vscalar V (&0) (x:A)):A topology` THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH; ETA_AX];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    FIRST_ASSUM(MP_TAC o SPECL
      [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `eps:real`; `x:A`; `len:real`; `e:real^3->A`; `&0`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_has_volume")) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_rm_norm (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (x:A) <=
                 K1 * rfs_vscalar V (&0) x` THEN
    REWRITE_TAC[P2BN_RFS_VSCALAR]]);;

