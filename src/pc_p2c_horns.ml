(* ========================================================================= *)
(* Unit pc_p2c_horns (Part 2C): common tools for MT Lemma 11.30 and Thm      *)
(* 11.31 (strong delta-necks deep in 2 eps-horns), and the route             *)
(* P2HN_LEMMA_11_30_ROUTE of MT Lemma 11.30.  Contents: necks lie in balls;  *)
(* eps-monotonicity of evolving necks; monotonicity of canonical             *)
(* neighbourhoods (C, eps) to (2C, K eps); pinching of the maximal           *)
(* extension; base-point transfer of evolving necks along p3_flow_limit;     *)
(* typed end structure (from APX_A25_NC_ENDS); the core of MT Lemma 11.30 in *)
(* the maximal extension; the route P2HN_LEMMA_11_30_ROUTE.  Neck            *)
(* noncollapsing and neck balls are in pc_p2b_neckbd (P2BN_NECK_NONCOLL,     *)
(* P2BN_NECK_BALL_IN).                                                       *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_p2b_capfix.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p3_c17vol.ml";;
needs "src/pc_p3_c17curv.ml";;
needs "src/pc_p3e_limscal.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_lim_close.ml";;
needs "src/pc_rfs_evmono.ml";;
needs "src/pc_rfs_limpinch.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_lim_restrict.ml";;
needs "src/pc_apx_ncreq.ml";;
needs "src/pc_p2b_neckbd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Necks lie in balls of radius about R^(-1/2)/eps about their centres (from *)
(* MT Lemma A.2, APX_NECK_DIST), and evolving necks are monotone in eps in a *)
(* regular view (a wrapper of RFS_EVOLVING_NECK_EPS_MONO).                   *)
(* ========================================================================= *)

(* The s-coordinate facts of the neck domain (P2BN_NECK_DOM_SVAL,            *)
(* P2BN_SPHERE_SVAL, P2BN_SPHERE_IN_NECK_DOM) and the noncollapsing of neck  *)
(* centres are in the shared unit pc_p2b_neckbd.                             *)

(* sqrt 2 times pi is below 5 (sqrt 2 < 3/2, pi < 10/3).                     *)

let P2HN_SQRT2_PI_LT5 = prove
 (`sqrt(&2) * pi < &5`,
  SUBGOAL_THEN `sqrt(&2) < &3 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `pi < &10 / &3` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN
    REWRITE_TAC[REAL_ARITH `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(&3 / &2) * (&10 / &3)` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]);;

(* An eps-neck centred at x lies in the ball of radius                       *)
(* 2 (1/eps + 5) R(x)^(-1/2) about x.                                         *)

let P2HN_NECK_IN_BALL = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x e.
        &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x (e:real^3->A)
        ==> IMAGE e (rfs_neck_dom eps) SUBSET
            mfd_ball (top,atlas) g x
              (&2 * (inv eps + &5) * inv(sqrt(mfd_scalar atlas g x)))`,
  MP_TAC(SPEC `&1` (REWRITE_RULE[APX_NECK_DIST_STATEMENT] (ISPEC `(:A)` APX_NECK_DIST))) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nd"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x /\
                x IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "nd" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `g:A->real^3^3`; `eps:real`; `(e:real^3->A) z`; `e:real^3->A`;
                                 `z:real^3`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P2BN_SPHERE_IN_NECK_DOM]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BN_SPHERE_SVAL] THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 + &1) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) z))) *
              (abs(&0 - apx_sval (y:real^3)) + sqrt(&2) * pi)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval (y:real^3)) < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BN_NECK_DOM_SVAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC P2HN_SQRT2_PI_LT5 THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs(&0 - a) = abs a`] THEN
  SUBGOAL_THEN
   `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) z))) * (abs(apx_sval (y:real^3)) + sqrt(&2) * pi) <
    inv(sqrt(mfd_scalar atlas g (e z))) * (inv eps + &5)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Persistence of open subsets of a persisting set in a regular view, and    *)
(* eps-monotonicity of evolving necks.                                       *)
(* ------------------------------------------------------------------------- *)

let P2HN_PERSIST_OPEN_SUB = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W W' a b.
     p2c_regular_view V /\ rfs_persists V W a b /\ W' SUBSET W /\
     open_in (rfs_vtop V b) W'
     ==> rfs_persists V W' a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P2BN_PERSISTS_ALT] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real` (REWRITE_RULE[P2BN_PERSISTS_ALT]
    (ASSUME `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W a b`))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) s) (rfs_vatlas V s) W
               (rfs_vtop V b) (rfs_vatlas V b) W (\y:A. y) (\y. y)`
  MP_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]);;

(* Evolving necks in a regular view are monotone in eps: the slice clause of *)
(* RFS_EVOLVING_NECK_EPS_MONO (pc_rfs_evmono) from P2B9_REGULAR_NECK_SLICE.  *)

let P2HN_REG_EVNECK_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps eps' x t a e.
     p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\ eps <= eps'
     ==> rfs_evolving_neck V eps' x t a e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFS_EVOLVING_NECK_EPS_MONO THEN
  EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`; `s:real`] P2B9_REGULAR_NECK_SLICE) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Monotonicity of caps and of strong canonical neighbourhoods from (C, eps) *)
(* to (C', eps') with 2C <= C' and K eps <= eps' <= eps0, K the cap factor   *)
(* of the cap transfer                                                       *)
(* P2BF_CAP_FIX_GEN (re-centring of the end necks), applied with the         *)
(* identity map.  The cap needs a compact closure: automatic in a compact    *)
(* slice (all history slices are compact), and in the slice Omega at the     *)
(* singular time it follows from the ratio clause and properness.  Necks:    *)
(* P2HN_REG_EVNECK_MONO; components: P2B_RFS_C_COMPONENT_MONO_C, P2HN_ROUND_MONO. *)
(* ========================================================================= *)

(* rfs_mclose is monotone in eps for Riemannian metrics.                     *)

let P2HN_MCLOSE_MONO = prove
 (`!top atlas (g0:A->real^3^3) g W eps eps'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     riemannian_metric atlas g /\ W SUBSET topspace top /\
     &0 < eps /\ eps <= eps' /\ rfs_mclose (rfs_kreg eps) eps atlas W g0 g
     ==> rfs_mclose (rfs_kreg eps') eps' atlas W g0 g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_mclose] THEN STRIP_TAC THEN
  EXISTS_TAC `d:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN topspace (top:A topology)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg eps)
                (metric_local (atlas:((A->bool)#(A->real^3))->bool) (chart_at atlas x)
                   (g0:A->real^3^3))
                (metric_local atlas (chart_at atlas x) g) (SND(chart_at atlas x) x)` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC LCK_DIST_MONO THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                     (FST(chart_at atlas x))` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g0:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]]);;

(* eps-round components are monotone in eps.                                 *)

let P2HN_ROUND_MONO = prove
 (`!top atlas (g:A->real^3^3) eps eps' U.
     riemannian_metric atlas g /\ &0 < eps /\ eps <= eps' /\
     rfs_round_component (top,atlas) g eps U
     ==> rfs_round_component (top,atlas) g eps' U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_round_component] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`q:real`; `g1:A->real^3^3`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2HN_MCLOSE_MONO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN
  ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]);;

(* The C^2 bound of a Riemannian metric on a compact set (preferred charts). *)

let P2HN_RMD2_COMPACT_KR = prove
 (`!top atlas (g:A->real^N^N) K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?Kr. !y l. y IN K /\ l <= 2
                    ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas y) g)
                                          (SND(chart_at atlas y) y) <= Kr`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `K:A->bool`] P2B9S_RMD2_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B0:real` (LABEL_TAC "b0")) THEN
  MP_TAC(ISPECL [`1`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `K:A->bool`] P2B9S_RMD2_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "b1")) THEN
  MP_TAC(ISPECL [`2`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `K:A->bool`] P2B9S_RMD2_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "b2")) THEN
  EXISTS_TAC `max B0 (max B1 B2)` THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `l:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`; `y:A`]
                RFA_RMD2_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "b0" (MP_TAC o C MP (ASSUME `(y:A) IN K`) o SPEC `y:A`) THEN
  USE_THEN "b1" (MP_TAC o C MP (ASSUME `(y:A) IN K`) o SPEC `y:A`) THEN
  USE_THEN "b2" (MP_TAC o C MP (ASSUME `(y:A) IN K`) o SPEC `y:A`) THEN
  SUBGOAL_THEN `l = 0 \/ l = 1 \/ l = 2` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The closeness of a metric to its own pullback by the identity is 0.        *)

let P2HN_MCLOSE_ID = prove
 (`!top atlas (g:A->real^3^3) U c delta.
     smooth_manifold_atlas top atlas /\ U SUBSET topspace top /\ &0 < delta
     ==> rfs_mclose (rfs_kreg delta) delta atlas U
           (\y. c %% g y)
           (\y. c %% mfd_pullback_metric atlas atlas (\y:A. y) g y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `z IN topspace (top:A topology)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `z:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (z:A)))
                       (FST(chart_at atlas z))
        ==> metric_local atlas (chart_at atlas z)
              (\y:A. c %% mfd_pullback_metric atlas atlas (\y:A. y) (g:A->real^3^3) y) w =
            metric_local atlas (chart_at atlas z) (\y:A. c %% g y) w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) (z:A)`;
                   `\y:A. c %% mfd_pullback_metric atlas atlas (\y:A. y) (g:A->real^3^3) y`;
                   `\y:A. c %% (g:A->real^3^3) y`] PDE_METRIC_LOCAL_CONG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC P2CF_PULLBACK_ID THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg delta)
                (metric_local atlas (chart_at atlas z) (\y:A. c %% (g:A->real^3^3) y))
                (metric_local atlas (chart_at atlas z) (\y:A. c %% g y))
                (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (z:A)) z)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[P2BL_LCK_DIST2_REFL]] THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (z:A)))
                     (FST(chart_at atlas z))` THEN
  ASM_SIMP_TAC[]);;

(* Caps with compact closure are monotone in (C, eps) up to the cap factor  *)
(* K; the new cap lies inside the old one.                                  *)

let P2HN_CAP_MONO = prove
 (`?K eps0. &1 <= K /\ &0 < eps0 /\
     !C eps C' eps' top atlas (g:A->real^3^3) U Y x.
        &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\ eps' <= eps0 /\
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_in top (top closure_of U) /\
        rfs_cap (top,atlas) g C eps U Y /\ x IN Y
        ==> ?U' Y'. U' SUBSET U /\ rfs_cap (top,atlas) g C' eps' U' Y' /\ x IN Y'`,
  X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))))
    (INST_TYPE [`:A`,`:B`] P2BF_CAP_FIX_GEN) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `U:A->bool`; `Y:A->bool`; `x:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\
                (!y. y IN U ==> &0 < mfd_scalar atlas (g:A->real^3^3) y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
    REWRITE_TAC[rfs_cap] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_CAP_CORE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `C:real`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\z:A. mfd_scalar atlas (g:A->real^3^3) x %% g z`;
                 `top closure_of (U:A->bool)`] P2HN_RMD2_COMPACT_KR) THEN
  ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kr:real` (LABEL_TAC "kr")) THEN
  USE_THEN "fix" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `x:A`; `U:A->bool`; `Y:A->bool`; `\y:A. y`; `\y:A. y`]) THEN
  SUBGOAL_THEN
   `rfs_mclose (rfs_kreg delta) delta atlas (U:A->bool)
      (\y. mfd_scalar atlas (g:A->real^3^3) x %% g y)
      (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas (\y:A. y) g y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_MCLOSE_ID THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID] THEN ASM_SIMP_TAC[MFD_DIFFEO_ID] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:A`; `l:num`] THEN STRIP_TAC THEN
    USE_THEN "kr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CLOSURE_OF_SUBSET) THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y':A->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`U':A->bool`; `Y':A->bool`] THEN ASM_REWRITE_TAC[]]);;

(* Strong canonical neighbourhoods in a regular view at a time with compact  *)
(* slice: (C, eps) gives (C', eps') for 2C <= C', K eps <= eps' <= eps0.     *)

let P2HN_CANON_MONO = prove
 (`?K eps0. &1 <= K /\ &0 < eps0 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      C eps C' eps' x t.
        &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\ eps' <= eps0 /\
        p2c_regular_view V /\ compact_space (rfs_vtop V t) /\ p3_canon_at V C eps x t
        ==> p3_canon_at V C' eps' x t`,
  X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cap"))))
    P2HN_CAP_MONO THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `eps:real`; `C':real`;
                       `eps':real`; `x:A`; `t:real`] THEN
  REWRITE_TAC[p3_canon_at; rfs_vtop] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_TAC `U:A->bool`)))))))) THEN
  SUBGOAL_THEN `eps <= eps'` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 * eps <= K * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C <= C'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x IN topspace((TM:real->A topology) t)
                ==> hausdorff_space (TM t) /\ smooth_manifold_atlas (TM t) (AT t) /\
                    riemannian_metric (AT t) ((G:real->A->real^3^3) t)`
  (LABEL_TAC "slice") THENL
   [DISCH_TAC THEN USE_THEN "reg" MP_TAC THEN
    REWRITE_TAC[p2c_regular_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_strong_canonical]) THEN
  STRIP_TAC THENL
   [(* strong neck *)
    EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps')` THEN
    REWRITE_TAC[rfs_strong_canonical] THEN DISJ1_TAC THEN
    EXISTS_TAC `e:real^3->A` THEN REWRITE_TAC[rfs_strong_neck] THEN
    MATCH_MP_TAC P2HN_REG_EVNECK_MONO THEN EXISTS_TAC `eps:real` THEN
    ASM_REWRITE_TAC[GSYM rfs_strong_neck];
    (* cap *)
    SUBGOAL_THEN `(x:A) IN topspace((TM:real->A topology) t)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(TM:real->A topology) t`; `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                     `(G:real->A->real^3^3) t`; `C:real`; `eps:real`; `U:A->bool`;
                     `Y:A->bool`] P2B_CAP_CORE_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_cap ((TM:real->A topology) t,
                            (AT:real->((A->bool)#(A->real^3))->bool) t)
                           ((G:real->A->real^3^3) t) C eps U Y` THEN
      REWRITE_TAC[rfs_cap] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "slice" (MP_TAC o C MP (ASSUME `(x:A) IN topspace((TM:real->A topology) t)`)) THEN
    STRIP_TAC THEN
    USE_THEN "cap" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `C':real`; `eps':real`; `(TM:real->A topology) t`;
       `(AT:real->((A->bool)#(A->real^3))->bool) t`; `(G:real->A->real^3^3) t`;
       `U:A->bool`; `Y:A->bool`; `x:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y':A->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `U':A->bool` THEN REWRITE_TAC[rfs_strong_canonical] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `Y':A->bool` THEN ASM_REWRITE_TAC[];
    (* C-component *)
    SUBGOAL_THEN `(x:A) IN topspace((TM:real->A topology) t)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_c_component ((TM:real->A topology) t,
                                    (AT:real->((A->bool)#(A->real^3))->bool) t)
                                   ((G:real->A->real^3^3) t) C U` THEN
      REWRITE_TAC[rfs_c_component] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "slice" (MP_TAC o C MP (ASSUME `(x:A) IN topspace((TM:real->A topology) t)`)) THEN
    STRIP_TAC THEN
    EXISTS_TAC `U:A->bool` THEN REWRITE_TAC[rfs_strong_canonical] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B_RFS_C_COMPONENT_MONO_C THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN ASM_REWRITE_TAC[];
    (* round component *)
    SUBGOAL_THEN `(x:A) IN topspace((TM:real->A topology) t)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_round_component ((TM:real->A topology) t,
                                        (AT:real->((A->bool)#(A->real^3))->bool) t)
                                       ((G:real->A->real^3^3) t) eps U` THEN
      REWRITE_TAC[rfs_round_component] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "slice" (MP_TAC o C MP (ASSUME `(x:A) IN topspace((TM:real->A topology) t)`)) THEN
    STRIP_TAC THEN
    EXISTS_TAC `U:A->bool` THEN REWRITE_TAC[rfs_strong_canonical] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2HN_ROUND_MONO THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The maximal extension at the singular                                     *)
(* time.  The restriction of a limit metric gl to (Om, restrict_atlas) is a  *)
(* limit metric again, so the scalar curvature and the least sectional      *)
(* curvature of the restricted limit metric equal those of gl in the full   *)
(* atlas (gl is only a metric on Om, so MFD_SCALAR_RESTRICT does not        *)
(* apply); with RFS_PINCHED_AT_LIMIT (pc_rfs_limpinch) the maximal          *)
(* extension of a pinched history is pinched.                               *)
(* ========================================================================= *)

(* Limits from the left are unique.                                          *)

(* The left half-line net at ts is not trivial.                              *)


(* Left limits in epsilon-delta form are limits along that net.              *)



(* Two families of plane functions that are uniformly close have close      *)
(* infima over the planes.                                                   *)



(* Curvatures at a point converge to those of the limit metric (full atlas, *)
(* uniformly in the plane); the sectional curvatures of gl are bounded.      *)


(* The least sectional curvature converges.                                  *)


(* The restriction of a limit metric to Om is a limit metric of the         *)
(* restricted family on the manifold (Om, restrict_atlas).                   *)

(* For a limit metric the scalar curvature and the least sectional curvature *)
(* of the restricted metric agree with those in the full atlas on Om.        *)

(* The pinching inequalities pass to the limit metric at ts > 0.             *)


(* The last stage of a history and its Ricci flow up to the horizon.         *)

let P2HN_LAST_STAGE = prove
 (`!hs:(A)rfs_history.
     rfs_history_ok hs
     ==> hs_time hs (hs_count hs) < rfs_horizon hs /\
         &0 <= hs_time hs (hs_count hs) /\
         hausdorff_space (hs_top hs (hs_count hs)) /\
         compact_space (hs_top hs (hs_count hs)) /\
         smooth_manifold_atlas (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
         (!t. hs_time hs (hs_count hs) < t /\ t < rfs_horizon hs
              ==> riemannian_metric (hs_atlas hs (hs_count hs))
                                    (hs_metric hs (hs_count hs) t))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (MP_TAC o SPEC `hs_count(hs:(A)rfs_history)`)
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `hs_count(hs:(A)rfs_history)`) (K ALL_TAC)))) THEN
  REWRITE_TAC[LE_REFL; GSYM rfs_horizon; ricci_flow_from; ricci_flow_on] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* The maximal extension of a pinched history by a limit metric is pinched.  *)

let P2HN_PINCH_MAXEXT = prove
 (`!(hs:(A)rfs_history) Om gl.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     open_in (hs_top hs (hs_count hs)) Om /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs)) Om
       (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
     ==> rfs_pinched (p3_maxext hs Om gl)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` P2HN_LAST_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  REWRITE_TAC[p3_maxext; rfs_view; rfs_pinched] THEN BETA_TAC THEN
  DISCH_THEN(LABEL_TAC "PH") THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
  ASM_CASES_TAC `t = rfs_horizon(hs:(A)rfs_history)` THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "PH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d0. &0 < d0 /\
         !s. rfs_horizon hs - d0 < s /\ s < rfs_horizon hs
             ==> riemannian_metric (hs_atlas hs (hs_count(hs:(A)rfs_history)))
                                   (hs_metric hs (hs_count hs) s) /\
                 rfs_pinched_at (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s)
                                s (x:A)`
  (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `rfs_horizon hs - hs_time hs (hs_count(hs:(A)rfs_history))` THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`; `s:real`]
                  APX_RFS_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LE_REFL; GSYM rfs_horizon] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "PH" (MP_TAC o SPECL [`s:real`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_pinched_at (restrict_atlas (hs_atlas hs (hs_count(hs:(A)rfs_history))) Om)
      (restrict_metric (hs_atlas hs (hs_count hs)) Om gl) (rfs_horizon hs) (x:A) <=>
    rfs_pinched_at (hs_atlas hs (hs_count hs)) gl (rfs_horizon hs) x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                   `hs_atlas hs (hs_count(hs:(A)rfs_history))`; `Om:A->bool`;
                   `rfs_horizon(hs:(A)rfs_history)`;
                   `hs_metric hs (hs_count(hs:(A)rfs_history))`;
                   `gl:A->real^3^3`; `x:A`] LIM_RESTRICT_CURV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[rfs_pinched_at];
    ALL_TAC] THEN
  MATCH_MP_TAC RFS_PINCHED_AT_LIMIT THEN
  MAP_EVERY EXISTS_TAC [`hs_top hs (hs_count(hs:(A)rfs_history))`; `Om:A->bool`;
                        `hs_metric hs (hs_count(hs:(A)rfs_history))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Base-point transfer of evolving necks                                     *)
(* along p3_flow_limit.  If the limit flow (as the flow view on (-Tl, 0])   *)
(* has an evolving eps-neck of length a at (xl, 0) whose window fits in     *)
(* (-Tl, 0] and whose image has compact closure, then for every L in        *)
(* [1, a) the approximants V n have evolving eps-necks of length L at       *)
(* (x n, t n) for all large n (P2B_NECK_OPEN_L with the closeness of        *)
(* P2BL_FLOW_LIMIT_CLOSE at scale R = R_l(xl, 0)).                          *)
(* ========================================================================= *)

let P2HN_FLOW_LIMIT_NECK = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl Tl eps a L (e:real^3->B).
     p3_flow_limit V x t Q (top,atlas) g xl Tl /\
     (!k s. ~(topspace(rfs_vtop (V k) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)) /\
     p2c_regular_view (rfs_flow_view (top,atlas) {s | --Tl < s /\ s <= &0} g) /\
     &0 < eps /\ eps < &1 / &4 /\ &1 <= L /\ L < a /\
     rfs_evolving_neck (rfs_flow_view (top,atlas) {s | --Tl < s /\ s <= &0} g) eps xl (&0) a e /\
     a / rfs_vscalar (rfs_flow_view (top,atlas) {s | --Tl < s /\ s <= &0} g) (&0) xl < Tl /\
     compact_in top (top closure_of IMAGE e (rfs_neck_dom eps))
     ==> ?N. !n. N <= n ==> ?e'. rfs_evolving_neck (V n) eps (x n) (t n) L e'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sl") STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `VL = rfs_flow_view (top,atlas) {s | --Tl < s /\ s <= &0}
                     (g:real->B->real^3^3)` THEN
  ABBREV_TAC `RL = rfs_vscalar (VL:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                    (real->B->real^3^3)) (&0) (xl:B)` THEN
  ABBREV_TAC `W = IMAGE (e:real^3->B) (rfs_neck_dom eps)` THEN
  SUBGOAL_THEN `&0 < Tl` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit (V:num->(real->A topology)#
                                 (real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) x t Q
                               (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                               (g:real->B->real^3^3) (xl:B) Tl` THEN
    SIMP_TAC[p3_flow_limit];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) eps (xl:B) (e:real^3->B)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_evolving_neck (VL:(real->B topology)#
                                     (real->((B->bool)#(B->real^3))->bool)#
                                     (real->B->real^3^3)) eps xl (&0) a e` THEN
    EXPAND_TAC "VL" THEN REWRITE_TAC[rfs_flow_view; rfs_evolving_neck] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_NEG_LT0];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) (xl:B) = RL` ASSUME_TAC THENL
   [EXPAND_TAC "RL" THEN EXPAND_TAC "VL" THEN
    REWRITE_TAC[rfs_flow_view; rfs_vscalar];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < RL /\ open_in top (W:B->bool) /\ (xl:B) IN W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) eps (xl:B)
                          (e:real^3->B)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      EXPAND_TAC "W" THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "W" THEN
      UNDISCH_TAC `(xl:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
      MP_TAC(GEN `y:real^3` (MP (SPECL [`eps:real`; `y:real^3`]
                                       (REWRITE_RULE[IMP_CONJ] P2BN_SPHERE_IN_NECK_DOM))
                                 (ASSUME `&0 < eps`))) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a / RL` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the neck of the limit opens to length L under delta-closeness *)
  MP_TAC(ISPECL [`VL:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                     (real->B->real^3^3)`;
                 `eps:real`; `xl:B`; `&0`; `a:real`; `L:real`; `e:real^3->B`]
          (REWRITE_RULE[P2B_NECK_OPEN_L_STATEMENT]
            (ISPECL [`(:B)`; `(:A)`] P2B_NECK_OPEN_L))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "op"))) THEN
  (* the closeness of the approximants *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                 `xl:B`; `Tl:real`] P2BL_FLOW_LIMIT_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  USE_THEN "cl" (MP_TAC o SPECL [`top closure_of (W:B->bool)`; `W:B->bool`; `--(a / RL)`;
                                 `delta:real`; `RL:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. (t:num->real) n + (s / RL) / (Q:num->real) n = t n + s / (RL * Q n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Q:num->real) n` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit (V:num->(real->A topology)#
                                 (real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) x t Q
                               (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                               (g:real->B->real^3^3) (xl:B) Tl` THEN
    SIMP_TAC[p3_flow_limit];
    ALL_TAC] THEN
  (* the closeness at each rescaled time of the window *)
  SUBGOAL_THEN
   `!s. --a < s /\ s <= &0
        ==> (?psi. mfd_diffeo top atlas W
                     (rfs_vtop ((V:num->(real->A topology)#
                                 (real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) n) ((t:num->real) n + s / (RL * Q n)))
                     (rfs_vatlas (V n) (t n + s / (RL * Q n)))
                     (IMAGE ((phi:num->B->A) n) W) (phi n) psi) /\
            rfs_mclose (rfs_kreg delta) delta atlas (W:B->bool)
              (\y. RL %% (g:real->B->real^3^3) (s / RL) y)
              (\y. (RL * Q n) %%
                   mfd_pullback_metric atlas (rfs_vatlas (V n) (t n + s / (RL * Q n)))
                     (phi n) (rfs_vmetric (V n) (t n + s / (RL * Q n))) y)`
  (LABEL_TAC "win") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `--(a / RL) <= s / RL /\ s / RL <= &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `--(a / RL) = --a / RL` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]];
      ALL_TAC] THEN
    USE_THEN "k0" (MP_TAC o C MP (ASSUME `k0 <= n:num`) o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o C MP (CONJ (ASSUME `--(a / RL) <= s / RL`) (ASSUME `s / RL <= &0`)) o
               SPEC `s / RL`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:num->B->A) n xl = (x:num->A) n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  USE_THEN "op" (MP_TAC o SPECL
    [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
          (real->A->real^3^3)) n`;
     `(t:num->real) n`; `RL * (Q:num->real) n`; `(phi:num->B->A) n`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [(* the slices of V n in the window are Riemannian manifolds *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "sl" MATCH_MP_TAC THEN
    USE_THEN "win" (MP_TAC o C MP (CONJ (ASSUME `--a < s`) (ASSUME `s <= &0`)) o
                    SPEC `s:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `psi:A->B` o CONJUNCT1) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(xl:B) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the view closeness *)
  REWRITE_TAC[p3_view_close] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--Tl < s / RL /\ s / RL <= &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `--(a / RL)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `--(a / RL) = --a / RL` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  EXPAND_TAC "VL" THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM; REAL_ADD_LID] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "win" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The end structure of MT Lemma 11.30 with                                  *)
(* typed canonical neighbourhoods (necks NK, (C,eps)-caps, C-components and  *)
(* ec-round components), from APX_A25_NC_ENDS (pc_apx_ncreq): a component   *)
(* that contains a point of a C-component or of an ec-round component is    *)
(* that compact component (no horns); otherwise A.25 applies as it stands.  *)
(* ========================================================================= *)

let P2HN_COMPONENT_EQ = prove
 (`!top (c:A->bool) d x.
     c IN connected_components_of top /\ d IN connected_components_of top /\
     x IN c /\ x IN d ==> c = d`,
  MESON_TAC[CONNECTED_COMPONENTS_OF_DISJOINT; IN_DISJOINT]);;

let P2HN_ENDS_TYPED = prove
 (`!u:A->bool.
     APX_A25_NC_ENDS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps ec top atlas (g:A->real^3^3) NK L W.
              &1 <= C /\ &0 < eps /\ eps <= eps0 /\ &0 < L /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              W IN connected_components_of top /\
              (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
              (?x. x IN W /\ mfd_scalar atlas g x <= L) /\
              (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
              (!x. x IN W /\ L < mfd_scalar atlas g x
                   ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y) \/
                       (?U. x IN U /\ rfs_c_component (top,atlas) g C U) \/
                       (?U. x IN U /\ rfs_round_component (top,atlas) g ec U))
              ==> ?(J:num->bool) (H:num->real^3->A) K.
                    FINITE J /\ compact_in top K /\ K SUBSET W /\
                    W = K UNION UNIONS {IMAGE (H j) {y | &1 <= norm y} | j IN J} /\
                    (!j. j IN J
                         ==> mfd_param top atlas {y | &1 / &2 < norm y} (H j) /\
                             IMAGE (H j) {y | &1 / &2 < norm y} SUBSET W /\
                             (!K'. compact_in top K'
                                   ==> bounded {y | &1 <= norm y /\ H j y IN K'}) /\
                             (!y. &1 <= norm y
                                  ==> C * L < mfd_scalar atlas g (H j y) /\
                                      ?e. NK (H j y) e) /\
                             (!y. norm y = &1 ==> mfd_scalar atlas g (H j y) <= &2 * C * L) /\
                             (?x e. NK x e /\
                                    IMAGE e (sphere(vec 0,&1)) =
                                    IMAGE (H j) (sphere(vec 0,&1)))) /\
                    (!i j. i IN J /\ j IN J /\ ~(i = j)
                           ==> DISJOINT (IMAGE (H i) {y | &1 <= norm y})
                                        (IMAGE (H j) {y | &1 <= norm y}))`,
  GEN_TAC THEN REWRITE_TAC[APX_A25_NC_ENDS_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A25"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `ec:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `NK:A->(real^3->A)->bool`; `L:real`; `W:A->bool`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC
   `?x U. x IN W /\ L < mfd_scalar atlas (g:A->real^3^3) x /\ x IN U /\
          (rfs_c_component (top,atlas) g C U \/ rfs_round_component (top,atlas) g ec U)`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x1:A` (X_CHOOSE_THEN `U1:A->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cr")))))) THEN
    SUBGOAL_THEN `U1 IN connected_components_of (top:A topology) /\ compact_in top U1`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "cr" MP_TAC THEN REWRITE_TAC[rfs_c_component; rfs_round_component] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `W:A->bool = U1` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC P2HN_COMPONENT_EQ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `x1:A`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`{}:num->bool`; `\j:num y:real^3. (x1:A)`; `U1:A->bool`] THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; SUBSET_REFL] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "A25" MATCH_MP_TAC THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_round_component"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* The core of MT Lemma 11.30 in the maximal extension.  Hypotheses: the     *)
(* history facts, Omega open, a limit metric gl whose scalar curvature is    *)
(* proper on Omega, and typed canonical neighbourhoods at the singular time  *)
(* (strong 2 eps-necks; (2C, Kc eps)-caps, 2C-components, Kc eps-round       *)
(* components, Kc >= 2), as Thm 11.19 in its typed form provides.  Each      *)
(* component meeting Omega_rho is a compact set plus finitely many 2         *)
(* eps-horns (P2HN_ENDS_TYPED with C_A = 2C, eps_A = Kc eps, L = rho^-2);    *)
(* there are finitely many such components.                                  *)
(* ========================================================================= *)

(* Finitely many components of a locally connected space meet a compact set. *)

let P2HN_FINITE_COMPONENTS_MEETING = prove
 (`!top (k:A->bool).
     locally_connected_space top /\ compact_in top k
     ==> FINITE {c | c IN connected_components_of top /\ ~(c INTER k = {})}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
  DISCH_THEN(MP_TAC o SPEC `connected_components_of (top:A topology)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE];
      REWRITE_TAC[UNIONS_CONNECTED_COMPONENTS_OF] THEN ASM_MESON_TAC[compact_in]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `c:A->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `~(c INTER k:A->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?d. d IN V /\ (z:A) IN d` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c:A->bool = d` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC P2HN_COMPONENT_EQ THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `z:A`] THEN ASM SET_TAC[]);;

(* The slice of the maximal extension at the singular time.                  *)

let P2HN_MAXEXT_SLICE = prove
 (`!(hs:(A)rfs_history) gl.
     rfs_history_ok hs /\
     apx_sphere_sep (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
     open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
     ==> rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) =
         subtopology (hs_top hs (hs_count hs)) (p3_omega hs) /\
         rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) =
         restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs) /\
         rfs_vmetric (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) =
         restrict_metric (hs_atlas hs (hs_count hs)) (p3_omega hs) gl /\
         topspace(subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) = p3_omega hs /\
         hausdorff_space (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\
         smooth_manifold_atlas (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
           (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) /\
         riemannian_metric (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs))
           (restrict_metric (hs_atlas hs (hs_count hs)) (p3_omega hs) gl) /\
         apx_sphere_sep (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
           (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) /\
         locally_connected_space (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\
         (!x. x IN p3_omega hs
              ==> mfd_scalar (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs))
                    (restrict_metric (hs_atlas hs (hs_count hs)) (p3_omega hs) gl) x =
                  mfd_scalar (hs_atlas hs (hs_count hs)) gl x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` P2HN_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  SUBGOAL_THEN `smooth_manifold_atlas
                  (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
                  (restrict_atlas (hs_atlas hs (hs_count(hs:(A)rfs_history))) (p3_omega hs))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> can (find_term ((=) `p3_omega:(A)rfs_history->A->bool`)) (concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in"))
                           (concl th))) THEN
    SET_TAC[];
    MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LIM_RESTRICT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`hs_top hs (hs_count(hs:(A)rfs_history))`; `rfs_horizon(hs:(A)rfs_history)`;
                          `hs_metric hs (hs_count(hs:(A)rfs_history))`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `(:A)` APX_SEP_OPEN) THEN REWRITE_TAC[APX_SEP_OPEN_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] GEO_MANIFOLD_LOCALLY_PATH_CONNECTED) THEN
    EXISTS_TAC `restrict_atlas (hs_atlas hs (hs_count(hs:(A)rfs_history))) (p3_omega hs)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                   `hs_atlas hs (hs_count(hs:(A)rfs_history))`; `p3_omega(hs:(A)rfs_history)`;
                   `rfs_horizon(hs:(A)rfs_history)`; `hs_metric hs (hs_count(hs:(A)rfs_history))`;
                   `gl:A->real^3^3`; `x:A`] LIM_RESTRICT_CURV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `rfs_horizon hs - hs_time hs (hs_count(hs:(A)rfs_history))` THEN
      ASM_REWRITE_TAC[REAL_SUB_LT] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

(* The slice part of an evolving neck, for any view.                        *)

let P2HN_EVNECK_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t len e.
     rfs_evolving_neck V eps x t len e
     ==> rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps x e`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_evolving_neck; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  SIMP_TAC[]);;

(* Packing finitely many finite families indexed by a finite set of sets.   *)

let P2HN_PACK_FAMILIES = prove
 (`!(CW:(A->bool)->bool) (JJ:(A->bool)->num->bool) (HH:(A->bool)->num->B).
     FINITE CW /\ (!W. W IN CW ==> FINITE (JJ W))
     ==> ?(J:num->bool) (H:num->B) (w:num->(A->bool)) (jj:num->num).
           FINITE J /\
           (!k. k IN J ==> w k IN CW /\ jj k IN JJ (w k) /\ H k = HH (w k) (jj k)) /\
           (!W j. W IN CW /\ j IN JJ W ==> ?k. k IN J /\ w k = W /\ jj k = j) /\
           (!k k'. k IN J /\ k' IN J /\ w k = w k' /\ jj k = jj k' ==> k = k')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMBERS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ix:num->bool` (X_CHOOSE_THEN `f:num->(A->bool)`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`{NUMPAIR i j | i IN Ix /\ j IN (JJ:(A->bool)->num->bool) (f i)}`;
    `\k. (HH:(A->bool)->num->B) (f (NUMFST k)) (NUMSND k)`;
    `\k. (f:num->(A->bool)) (NUMFST k)`; `NUMSND`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[NUMPAIR_DEST] THEN ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `?i. i IN Ix /\ (f:num->(A->bool)) i = W` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `NUMPAIR i j` THEN REWRITE_TAC[IN_ELIM_THM; NUMPAIR_DEST] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i':num` (X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC))
        MP_TAC)) THEN
    ASM_REWRITE_TAC[NUMPAIR_DEST; NUMPAIR_INJ] THEN ASM_MESON_TAC[]]);;

(* Arithmetic for the levels of Lemma 11.30.                                 *)

let P2HN_ARITH_LEVELS = prove
 (`!C L rho. &1 < C /\ &0 < rho /\ L = inv(rho pow 2)
             ==> L < (&2 * C) * L /\
                 &2 * (&2 * C) * L <= inv((rho / (&2 * C)) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv((rho / (&2 * C)) pow 2) = (&4 * C pow 2) * L` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `&1 < C` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * L < x ==> L < x`) THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `&2 * (&2 * C) * L = (&4 * C) * L`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `(&4 * C) * &1 <= (&4 * C) * C` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* Lemma 11.30 for one slice (top, atlas, Om, gl) of a view V at time Th.    *)

let P2HN_1130_ASSEMBLE = prove
 (`!u:A->bool.
     APX_A25_NC_ENDS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !(top:A topology) atlas Om (gl:A->real^3^3)
            (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            Th Kc C eps r0 rho.
              rfs_vtop V Th = subtopology top Om /\
              rfs_vatlas V Th = restrict_atlas atlas Om /\
              rfs_vmetric V Th = restrict_metric atlas Om gl /\
              topspace(subtopology top Om) = Om /\
              hausdorff_space (subtopology top Om) /\
              riemannian_metric (restrict_atlas atlas Om) (restrict_metric atlas Om gl) /\
              apx_sphere_sep (subtopology top Om) (restrict_atlas atlas Om) /\
              locally_connected_space (subtopology top Om) /\
              (!x. x IN Om
                   ==> mfd_scalar (restrict_atlas atlas Om) (restrict_metric atlas Om gl) x =
                       mfd_scalar atlas gl x) /\
              (!c. compact_in top {x | x IN Om /\ mfd_scalar atlas gl x <= c}) /\
              (!x. x IN Om /\ inv(r0 pow 2) < mfd_scalar atlas gl x
                   ==> (?e. rfs_strong_neck V (&2 * eps) x Th e) \/
                       (?U Y. rfs_cap (subtopology top Om,restrict_atlas atlas Om)
                                      (restrict_metric atlas Om gl) (&2 * C) (Kc * eps) U Y /\
                              x IN Y) \/
                       (?U. x IN U /\
                            rfs_c_component (subtopology top Om,restrict_atlas atlas Om)
                                            (restrict_metric atlas Om gl) (&2 * C) U) \/
                       (?U. x IN U /\
                            rfs_round_component (subtopology top Om,restrict_atlas atlas Om)
                                                (restrict_metric atlas Om gl) (Kc * eps) U)) /\
              &2 <= Kc /\ &1 < C /\ &0 < eps /\ Kc * eps <= eps0 /\ &0 < rho /\ rho < r0
              ==> ?(J:num->bool) H K.
                    FINITE J /\
                    FINITE {U | U IN connected_components_of (subtopology top Om) /\
                                ~(U INTER p3_omega_rho atlas Om gl rho = {})} /\
                    (!j. j IN J
                         ==> p3_horn V Th (&2 * eps) (H j) /\
                             DISJOINT (p3_horn_set (H j)) (p3_omega_rho atlas Om gl rho) /\
                             IMAGE (H j) (sphere(vec 0,&1)) SUBSET
                             p3_omega_rho atlas Om gl (rho / (&2 * C))) /\
                    (!i j. i IN J /\ j IN J /\ ~(i = j)
                           ==> DISJOINT (p3_horn_set (H i)) (p3_horn_set (H j))) /\
                    compact_in top K /\
                    UNIONS {U | U IN connected_components_of (subtopology top Om) /\
                                ~(U INTER p3_omega_rho atlas Om gl rho = {})} =
                    K UNION UNIONS {p3_horn_set (H j) | j IN J}`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_ENDS_TYPED) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ends"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Om:A->bool`;
                       `gl:A->real^3^3`;
                       `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`;
                       `Th:real`; `Kc:real`; `C:real`; `eps:real`; `r0:real`; `rho:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `TO = subtopology (top:A topology) Om` THEN
  ABBREV_TAC `AO = restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) Om` THEN
  ABBREV_TAC `GO = restrict_metric (atlas:((A->bool)#(A->real^3))->bool) Om gl` THEN
  ABBREV_TAC `Orho = p3_omega_rho (atlas:((A->bool)#(A->real^3))->bool) Om gl rho` THEN
  SUBGOAL_THEN `!x:A. x IN Orho <=> x IN Om /\
                          mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (gl:A->real^3^3) x <=
                          inv(rho pow 2)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Orho" THEN REWRITE_TAC[p3_omega_rho; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!W:A->bool. W IN connected_components_of (TO:A topology) ==> W SUBSET Om`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* sublevel sets of components are compact in the slice *)
  SUBGOAL_THEN
   `!W c. W IN connected_components_of TO
          ==> compact_in (TO:A topology)
                {x:A | x IN W /\
                       mfd_scalar (AO:((A->bool)#(A->real^3))->bool) (GO:A->real^3^3) x <= c}`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{x:A | x IN W /\
                         mfd_scalar (AO:((A->bool)#(A->real^3))->bool) (GO:A->real^3^3) x <= c} =
                  W INTER {x | x IN Om /\
                               mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                 (gl:A->real^3^3) x <= c}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
      ASM_CASES_TAC `(x:A) IN W` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN Om` ASSUME_TAC THENL
       [SUBGOAL_THEN `(W:A->bool) SUBSET Om` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:A) IN W` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER_COMPACT_IN THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "TO" THEN REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (TO:A topology) (Orho:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "TO" THEN REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `Orho = {x:A | x IN Om /\
                               mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                 (gl:A->real^3^3) x <= inv(rho pow 2)}`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `CW = {U | U IN connected_components_of (TO:A topology) /\
                        ~(U INTER Orho:A->bool = {})}` THEN
  SUBGOAL_THEN `FINITE (CW:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "CW" THEN MATCH_MP_TAC P2HN_FINITE_COMPONENTS_MEETING THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the per-component structure *)
  SUBGOAL_THEN
   `!W. W IN CW
        ==> ?(J:num->bool) (H:num->real^3->A) K.
              FINITE J /\ compact_in TO K /\ K SUBSET W /\
              W = K UNION UNIONS {p3_horn_set (H j) | j IN J} /\
              (!j. j IN J
                   ==> p3_horn V Th (&2 * eps) (H j) /\
                       p3_horn_set (H j) SUBSET W /\
                       DISJOINT (p3_horn_set (H j)) Orho /\
                       IMAGE (H j) (sphere(vec 0,&1)) SUBSET
                       p3_omega_rho atlas Om gl (rho / (&2 * C))) /\
              (!i j. i IN J /\ j IN J /\ ~(i = j)
                     ==> DISJOINT (p3_horn_set (H i)) (p3_horn_set (H j)))`
  MP_TAC THENL
   [X_GEN_TAC `W:A->bool` THEN EXPAND_TAC "CW" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(W:A->bool) SUBSET Om` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &2 * C /\ &0 < Kc * eps /\ &0 < inv(rho pow 2) /\
                  &2 * eps <= Kc * eps /\ inv(r0 pow 2) < inv(rho pow 2)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!c. compact_in (TO:A topology)
                         {x:A | x IN W /\
                                mfd_scalar (AO:((A->bool)#(A->real^3))->bool)
                                  (GO:A->real^3^3) x <= c}`
    ASSUME_TAC THENL
     [GEN_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?x:A. x IN W /\
                        mfd_scalar (AO:((A->bool)#(A->real^3))->bool) (GO:A->real^3^3) x <=
                        inv(rho pow 2)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `~(W INTER Orho:A->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN Om` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN W` THEN UNDISCH_TAC `(W:A->bool) SUBSET Om` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN UNDISCH_TAC `(x:A) IN Orho` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x e. rfs_strong_neck V (&2 * eps) x Th e
            ==> rfs_neck (TO,AO) (GO:A->real^3^3) (Kc * eps) (x:A) (e:real^3->A)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[rfs_strong_neck] THEN
      DISCH_THEN(MP_TAC o MATCH_MP P2HN_EVNECK_SLICE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `&2 * eps` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:A. x IN W /\ inv(rho pow 2) < mfd_scalar (AO:((A->bool)#(A->real^3))->bool)
                                                   (GO:A->real^3^3) x
            ==> (?e. rfs_strong_neck V (&2 * eps) x Th e) \/
                (?U Y. rfs_cap (TO,AO) GO (&2 * C) (Kc * eps) U Y /\ x IN Y) \/
                (?U. x IN U /\ rfs_c_component (TO,AO) GO (&2 * C) U) \/
                (?U. x IN U /\ rfs_round_component (TO,AO) GO (Kc * eps) U)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN Om` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN W` THEN UNDISCH_TAC `(W:A->bool) SUBSET Om` THEN SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_round_component"))
            (concl th) &&
        can (find_term ((=) `r0:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `inv(rho pow 2) < mfd_scalar (AO:((A->bool)#(A->real^3))->bool)
                                                 (GO:A->real^3^3) x` THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "ends" (MP_TAC o SPECL
      [`&2 * C`; `Kc * eps`; `Kc * eps`; `TO:A topology`;
       `AO:((A->bool)#(A->real^3))->bool`; `GO:A->real^3^3`;
       `\x e. rfs_strong_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&2 * eps) x Th e`;
       `inv(rho pow 2)`; `W:A->bool`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `J:num->bool` (X_CHOOSE_THEN `H:num->real^3->A`
      (X_CHOOSE_THEN `K:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
          (CONJUNCTS_THEN2 (LABEL_TAC "hj") (LABEL_TAC "dj"))))))))) THEN
    MAP_EVERY EXISTS_TAC [`J:num->bool`; `H:num->real^3->A`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[p3_horn_set] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "hj" (MP_TAC o C MP (ASSUME `(j:num) IN J`) o SPEC `j:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pts")
        (CONJUNCTS_THEN2 (LABEL_TAC "sph") ASSUME_TAC))))) THEN
    MP_TAC(SPECL [`C:real`; `inv(rho pow 2)`; `rho:real`] P2HN_ARITH_LEVELS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!y:real^3. &1 / &2 < norm y ==> (H:num->real^3->A) j y IN Om`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(H:num->real^3->A) j y IN W` MP_TAC THENL
       [UNDISCH_TAC `&1 / &2 < norm(y:real^3)` THEN
        UNDISCH_TAC `IMAGE ((H:num->real^3->A) j) {y | &1 / &2 < norm y} SUBSET W` THEN
        SET_TAC[];
        UNDISCH_TAC `(W:A->bool) SUBSET Om` THEN SET_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [(* the horn *)
      REWRITE_TAC[p3_horn] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "pts" (MP_TAC o C MP (ASSUME `&1 <= norm(y:real^3)`) o SPEC `y:real^3`) THEN
      SIMP_TAC[];
      (* inside W *)
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((H:num->real^3->A) j) {y | &1 / &2 < norm y}` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      (* disjoint from Omega_rho *)
      REWRITE_TAC[SET_RULE `!(f:real^3->A) s t.
                    DISJOINT (IMAGE f s) t <=> !y. y IN s ==> ~(f y IN t)`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(H:num->real^3->A) j y IN Om` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "pts" (MP_TAC o CONJUNCT1 o C MP (ASSUME `&1 <= norm(y:real^3)`) o
                      SPEC `y:real^3`) THEN
      SUBGOAL_THEN `mfd_scalar (AO:((A->bool)#(A->real^3))->bool) (GO:A->real^3^3)
                      ((H:num->real^3->A) j y) =
                    mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (gl:A->real^3^3) (H j y)`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      (* the inner sphere in Omega_(rho/2C) *)
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; p3_omega_rho; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(H:num->real^3->A) j y IN Om` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "sph" (MP_TAC o C MP (ASSUME `norm(y:real^3) = &1`) o SPEC `y:real^3`) THEN
      SUBGOAL_THEN `mfd_scalar (AO:((A->bool)#(A->real^3))->bool) (GO:A->real^3^3)
                      ((H:num->real^3->A) j y) =
                    mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (gl:A->real^3^3) (H j y)`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `JJ:(A->bool)->num->bool` (X_CHOOSE_THEN
    `HH:(A->bool)->num->real^3->A` (X_CHOOSE_THEN `KK:(A->bool)->A->bool`
    (LABEL_TAC "per")))) THEN
  MP_TAC(ISPECL [`CW:(A->bool)->bool`; `JJ:(A->bool)->num->bool`;
                 `HH:(A->bool)->num->real^3->A`] P2HN_PACK_FAMILIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `W:A->bool` THEN DISCH_TAC THEN
    USE_THEN "per" (MP_TAC o C MP (ASSUME `(W:A->bool) IN CW`) o SPEC `W:A->bool`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num->bool` (X_CHOOSE_THEN `H:num->real^3->A`
    (X_CHOOSE_THEN `w:num->(A->bool)` (X_CHOOSE_THEN `jj:num->num`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "P1")
        (CONJUNCTS_THEN2 (LABEL_TAC "P2") (LABEL_TAC "P3")))))))) THEN
  SUBGOAL_THEN
   `!k. k IN J
        ==> (w:num->(A->bool)) k IN CW /\
            (jj:num->num) k IN (JJ:(A->bool)->num->bool) (w k) /\
            (H:num->real^3->A) k = (HH:(A->bool)->num->real^3->A) (w k) (jj k) /\
            p3_horn V Th (&2 * eps) (H k) /\
            p3_horn_set (H k) SUBSET w k /\
            DISJOINT (p3_horn_set (H k)) Orho /\
            IMAGE (H k) (sphere(vec 0,&1)) SUBSET
            p3_omega_rho atlas Om gl (rho / (&2 * C))`
  (LABEL_TAC "kf") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "P1" (MP_TAC o C MP (ASSUME `(k:num) IN J`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "per" (MP_TAC o C MP (ASSUME `(w:num->(A->bool)) k IN CW`) o
                    SPEC `(w:num->(A->bool)) k`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `(jj:num->num) k IN JJ ((w:num->(A->bool)) k)`) o
               SPEC `(jj:num->num) k`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`J:num->bool`; `H:num->real^3->A`;
                        `UNIONS (IMAGE (KK:(A->bool)->A->bool) CW)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the horns *)
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "kf" (MP_TAC o C MP (ASSUME `(k:num) IN J`) o SPEC `k:num`) THEN SIMP_TAC[];
    (* pairwise disjoint *)
    MAP_EVERY X_GEN_TAC [`k:num`; `k':num`] THEN STRIP_TAC THEN
    USE_THEN "kf" (MP_TAC o C MP (ASSUME `(k:num) IN J`) o SPEC `k:num`) THEN
    USE_THEN "kf" (MP_TAC o C MP (ASSUME `(k':num) IN J`) o SPEC `k':num`) THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `(w:num->(A->bool)) k = w k'` THENL
     [SUBGOAL_THEN `~((jj:num->num) k = jj k')` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(k:num = k')` THEN REWRITE_TAC[] THEN
        USE_THEN "P3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(jj:num->num) k' IN (JJ:(A->bool)->num->bool) ((w:num->(A->bool)) k')` THEN
      UNDISCH_TAC `(H:num->real^3->A) k' =
                   (HH:(A->bool)->num->real^3->A) ((w:num->(A->bool)) k') ((jj:num->num) k')` THEN
      REWRITE_TAC[GSYM(ASSUME `(w:num->(A->bool)) k = w k'`)] THEN
      DISCH_TAC THEN DISCH_TAC THEN
      USE_THEN "per" (MP_TAC o C MP (ASSUME `(w:num->(A->bool)) k IN CW`) o
                      SPEC `(w:num->(A->bool)) k`) THEN
      DISCH_THEN(MP_TAC o SPECL [`(jj:num->num) k`; `(jj:num->num) k'`] o
                 CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBST1_TAC(SYM(ASSUME `(H:num->real^3->A) k =
                             (HH:(A->bool)->num->real^3->A) ((w:num->(A->bool)) k)
                               ((jj:num->num) k)`)) THEN
      SUBST1_TAC(SYM(ASSUME `(H:num->real^3->A) k' =
                             (HH:(A->bool)->num->real^3->A) ((w:num->(A->bool)) k)
                               ((jj:num->num) k')`)) THEN
      REWRITE_TAC[];
      SUBGOAL_THEN `DISJOINT ((w:num->(A->bool)) k) (w k')` MP_TAC THENL
       [MP_TAC(ISPECL [`TO:A topology`; `(w:num->(A->bool)) k`; `(w:num->(A->bool)) k'`]
                      CONNECTED_COMPONENTS_OF_DISJOINT) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `(w:num->(A->bool)) k IN CW` THEN
          UNDISCH_TAC `(w:num->(A->bool)) k' IN CW` THEN
          EXPAND_TAC "CW" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
          ASM_REWRITE_TAC[]];
        UNDISCH_TAC `p3_horn_set ((H:num->real^3->A) k) SUBSET (w:num->(A->bool)) k` THEN
        UNDISCH_TAC `p3_horn_set ((H:num->real^3->A) k') SUBSET (w:num->(A->bool)) k'` THEN
        SET_TAC[]]];
    (* the compact part *)
    SUBGOAL_THEN `compact_in (TO:A topology) (UNIONS (IMAGE (KK:(A->bool)->A->bool) CW))`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `W:A->bool` THEN DISCH_TAC THEN
      USE_THEN "per" (MP_TAC o C MP (ASSUME `(W:A->bool) IN CW`) o SPEC `W:A->bool`) THEN
      SIMP_TAC[];
      EXPAND_TAC "TO" THEN SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]];
    (* the union *)
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `z:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "per" (MP_TAC o C MP (ASSUME `(W:A->bool) IN CW`) o SPEC `W:A->bool`) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(fun th -> UNDISCH_TAC `(z:A) IN W` THEN
                            GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) ASSUME_TAC))) THENL
       [DISJ1_TAC THEN EXISTS_TAC `(KK:(A->bool)->A->bool) W` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN
        USE_THEN "P2" (MP_TAC o SPECL [`W:A->bool`; `j:num`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `p3_horn_set ((H:num->real^3->A) k)` THEN CONJ_TAC THENL
         [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
          USE_THEN "kf" (MP_TAC o C MP (ASSUME `(k:num) IN J`) o SPEC `k:num`) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(z:A) IN t` THEN ASM_REWRITE_TAC[]]];
      DISCH_THEN(DISJ_CASES_THEN2
        (X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
        (X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) ASSUME_TAC))) THENL
       [EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "per" (MP_TAC o C MP (ASSUME `(W:A->bool) IN CW`) o SPEC `W:A->bool`) THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        UNDISCH_TAC `(z:A) IN t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        EXISTS_TAC `(w:num->(A->bool)) k` THEN
        USE_THEN "kf" (MP_TAC o C MP (ASSUME `(k:num) IN J`) o SPEC `k:num`) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:A) IN t` THEN
        UNDISCH_TAC `t = p3_horn_set ((H:num->real^3->A) k)` THEN
        UNDISCH_TAC `p3_horn_set ((H:num->real^3->A) k) SUBSET (w:num->(A->bool)) k` THEN
        SET_TAC[]]]]);;

(* The core of MT Lemma 11.30.                                               *)

let P2HN_1130_CORE = prove
 (`!u:A->bool.
     APX_A25_NC_ENDS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !Kc C eps (hs:(A)rfs_history) r0 gl rho.
              &2 <= Kc /\ &1 < C /\ &0 < eps /\ Kc * eps <= eps0 /\ rfs_history_ok hs /\
              &0 < r0 /\
              apx_sphere_sep (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
              open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
              rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
              (!c. compact_in (hs_top hs (hs_count hs))
                     {x | x IN p3_omega hs /\
                          mfd_scalar (hs_atlas hs (hs_count hs)) gl x <= c}) /\
              (!x. x IN p3_omega hs /\
                   inv(r0 pow 2) < mfd_scalar (hs_atlas hs (hs_count hs)) gl x
                   ==> (?e. rfs_strong_neck (p3_maxext hs (p3_omega hs) gl) (&2 * eps) x
                                            (rfs_horizon hs) e) \/
                       (?U Y. rfs_cap (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs),
                                       rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                                      (rfs_vmetric (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                                      (&2 * C) (Kc * eps) U Y /\ x IN Y) \/
                       (?U. x IN U /\
                            rfs_c_component
                              (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs),
                               rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                              (rfs_vmetric (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                              (&2 * C) U) \/
                       (?U. x IN U /\
                            rfs_round_component
                              (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs),
                               rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                              (rfs_vmetric (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                              (Kc * eps) U)) /\
              &0 < rho /\ rho < r0
              ==> ?(J:num->bool) H K.
                    FINITE J /\
                    FINITE {U | U IN connected_components_of
                                     (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\
                                ~(U INTER p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs)
                                                       gl rho = {})} /\
                    (!j. j IN J
                         ==> p3_horn (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs)
                                     (&2 * eps) (H j) /\
                             DISJOINT (p3_horn_set (H j))
                                      (p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs)
                                                    gl rho) /\
                             IMAGE (H j) (sphere(vec 0,&1)) SUBSET
                             p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl
                                          (rho / (&2 * C))) /\
                    (!i j. i IN J /\ j IN J /\ ~(i = j)
                           ==> DISJOINT (p3_horn_set (H i)) (p3_horn_set (H j))) /\
                    compact_in (hs_top hs (hs_count hs)) K /\
                    UNIONS {U | U IN connected_components_of
                                     (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\
                                ~(U INTER p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs)
                                                       gl rho = {})} =
                    K UNION UNIONS {p3_horn_set (H j) | j IN J}`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2HN_1130_ASSEMBLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "as"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`Kc:real`; `C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                       `gl:A->real^3^3`; `rho:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`] P2HN_MAXEXT_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_round_component"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "as" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Kc:real`; `r0:real`] THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The route of MT Lemma 11.30.  The typed Thm 11.19 gives Omega open and    *)
(* the typed canonical neighbourhoods for EVERY limit metric gl; Lemma 11.21 *)
(* gives properness of R for SOME limit metric gl'.  Both are limits of the  *)
(* same slab metrics, so their scalar curvatures agree on Omega              *)
(* (P3E_LIMIT_SCALAR), and the properness transfers to the given gl.  Then   *)
(* P2HN_1130_CORE applies.  The route inputs APX_A21, APX_NO_CAP_IN_NECK and *)
(* APX_SEP_OPEN are not used.                                                *)
(* ========================================================================= *)

(* Two limit metrics of the last slab have the same scalar curvature on      *)
(* Omega.                                                                    *)

let P2HN_LIMIT_SCALAR_UNIQUE = prove
 (`!(hs:(A)rfs_history) gl gl' x.
     rfs_history_ok hs /\ open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl' /\
     x IN p3_omega hs
     ==> mfd_scalar (hs_atlas hs (hs_count hs)) gl x =
         mfd_scalar (hs_atlas hs (hs_count hs)) gl' x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` P2HN_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?d0. &0 < d0 /\
         !t. rfs_horizon(hs:(A)rfs_history) - d0 < t /\ t < rfs_horizon hs
             ==> riemannian_metric (hs_atlas hs (hs_count hs))
                                   (hs_metric hs (hs_count hs) t)`
  ASSUME_TAC THENL
   [EXISTS_TAC `rfs_horizon hs - hs_time hs (hs_count(hs:(A)rfs_history))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                 `p3_omega(hs:(A)rfs_history)`; `rfs_horizon(hs:(A)rfs_history)`;
                 `hs_metric hs (hs_count(hs:(A)rfs_history))`;
                 `gl:A->real^3^3`; `x:A`] P3E_LIMIT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L1") THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                 `p3_omega(hs:(A)rfs_history)`; `rfs_horizon(hs:(A)rfs_history)`;
                 `hs_metric hs (hs_count(hs:(A)rfs_history))`;
                 `gl':A->real^3^3`; `x:A`] P3E_LIMIT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L2") THEN
  ABBREV_TAC `a = mfd_scalar (hs_atlas hs (hs_count(hs:(A)rfs_history))) gl x` THEN
  ABBREV_TAC `b = mfd_scalar (hs_atlas hs (hs_count(hs:(A)rfs_history))) gl' x` THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(a - b)) ==> a = b`) THEN DISCH_TAC THEN
  USE_THEN "L1" (MP_TAC o SPEC `abs(a - b) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
  USE_THEN "L2" (MP_TAC o SPEC `abs(a - b) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
  ABBREV_TAC `t0 = rfs_horizon(hs:(A)rfs_history) - min d1 d2 / &2` THEN
  SUBGOAL_THEN
   `rfs_horizon(hs:(A)rfs_history) - d1 < t0 /\ rfs_horizon hs - d2 < t0 /\
    t0 < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "d1" (MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "d2" (MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Lemma 11.21's properness, for every limit metric.                         *)

let P2HN_LIMIT_PROPER_ANY = prove
 (`!(hs:(A)rfs_history) gl gl'.
     rfs_history_ok hs /\ open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl' /\
     (!c. compact_in (hs_top hs (hs_count hs))
            {x | x IN p3_omega hs /\ mfd_scalar (hs_atlas hs (hs_count hs)) gl' x <= c})
     ==> !c. compact_in (hs_top hs (hs_count hs))
               {x | x IN p3_omega hs /\ mfd_scalar (hs_atlas hs (hs_count hs)) gl x <= c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN p3_omega hs /\
         mfd_scalar (hs_atlas hs (hs_count(hs:(A)rfs_history))) gl x <= c} =
    {x | x IN p3_omega hs /\
         mfd_scalar (hs_atlas hs (hs_count(hs:(A)rfs_history))) gl' x <= c}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN p3_omega hs` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `gl':A->real^3^3`; `x:A`]
                  P2HN_LIMIT_SCALAR_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The route: P2C_LEMMA_11_30_ROUTE_STATEMENT.                               *)

let P2HN_LEMMA_11_30_ROUTE = prove
 (`!u:A->bool. P2C_LEMMA_11_30_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_LEMMA_11_30_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P2HN_1130_CORE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "core"))) THEN
  UNDISCH_TAC `P2C_THM_11_19_STATEMENT (u:A->bool)` THEN
  REWRITE_TAC[P2C_THM_11_19_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `e1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t1119"))))) THEN
  UNDISCH_TAC `P2C_LEMMA_11_21_STATEMENT (u:A->bool)` THEN
  REWRITE_TAC[P2C_LEMMA_11_21_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l1121"))) THEN
  REWRITE_TAC[P2C_LEMMA_11_30_STATEMENT] THEN
  SUBGOAL_THEN `&0 < Kc` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min e1 (min e2 (e3 / Kc))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                       `gl:A->real^3^3`; `rho:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Kc * eps <= e3` ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= e3 / Kc` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "t1119" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `gl:A->real^3^3`))) THEN
  ASM_REWRITE_TAC[p3_canon_typed] THEN DISCH_TAC THEN
  USE_THEN "l1121" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gl':A->real^3^3` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!c. compact_in (hs_top hs (hs_count hs))
          {x | x IN p3_omega hs /\
               mfd_scalar (hs_atlas hs (hs_count(hs:(A)rfs_history))) gl x <= c}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2HN_LIMIT_PROPER_ANY THEN EXISTS_TAC `gl':A->real^3^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "core" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Kc:real`; `r0:real`] THEN ASM_REWRITE_TAC[]);;

