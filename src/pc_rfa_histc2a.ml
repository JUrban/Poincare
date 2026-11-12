(* ========================================================================= *)
(* Unit pc_rfa_histc2a: the static part of R13 (P3_HIST_C2_BOUND_STATEMENT   *)
(* of pc_p3_route): on a (C,eps)-canonical neighbourhood U of x in any       *)
(* Riemannian 3-manifold, at every point y of an eps-neck, of an eps-round   *)
(* component, or of the end neck of a cap (U minus the closed core), the     *)
(* scale-invariant bound abs(nabla^l Rm)^2 <= K R(x)^(l+2), l <= 2, holds by *)
(* closeness to a model with parallel curvature (the cylinder, the round     *)
(* metric): P2C_DRM_BOUNDS and P2C_RMD_BOUNDS of pc_p2c_cdiff, read on the   *)
(* manifold through the neck parametrization (P2AP_PULLBACK_RMD_GEN of       *)
(* pc_p2a_par) or the preferred charts.  The closed cores of caps and the    *)
(* C-components need Shi's estimate (units pc_rfa_histc2b,c).                *)
(* ========================================================================= *)

needs "src/pc_rfa_c2base.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_lrg_base.ml";;
needs "src/pc_p2a_par.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* A metric field G that is C^4-close at y to a model G0 with                *)
(* parallel curvature and abs Rm(G0)^2 <= K has abs(nabla^l Rm(G))^2 <= C at *)
(* y for l <= 2 (the pattern of P2C_PT_DERIV: P2C_DRM_BOUNDS for l = 1, 2,   *)
(* LRG_RM_NEAR_BOUND for l = 0, the norm comparison LRG_LTNORM2_COMPARE).    *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_PAR_RMD = prove
 (`!K. ?C. &1 <= C /\
     !s (G0:real^3->real^3^3) G y.
       metric_field s G0 /\ metric_field s G /\ y IN s /\
       (!z u. z IN s ==> lnabla 4 G0 (lrm4 G0) z u = &0) /\
       ltnorm2 4 G0 (lrm4 G0) y <= K /\ lck_dist2 4 G0 G y <= inv C
       ==> !l. l <= 2 ==> lrm_deriv_norm2 l G y <= C`,
  GEN_TAC THEN
  X_CHOOSE_THEN `CD:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "drm"))
   (SPEC `K:real` (INST_TYPE [`:3`,`:N`] P2C_DRM_BOUNDS)) THEN
  X_CHOOSE_TAC `KN:real` (SPEC `K:real` LRG_RM_NEAR_BOUND) THEN
  EXISTS_TAC `max (&100) (max (&64 * CD) (max CD KN))` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `C = max (&100) (max (&64 * CD) (max CD KN))` THEN
  SUBGOAL_THEN `&100 <= C /\ &64 * CD <= C /\ CD <= C /\ KN <= C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `G0:real^3->real^3^3`; `G:real^3->real^3^3`;
                       `y:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = lck_dist2 4 (G0:real^3->real^3^3) G y` THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC P2C_LCK_DIST2_POS THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * d <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * inv C` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= &1 / &100 /\ CD * d <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&100 * d <= C * d /\ C * d <= &1 ==> d <= &1 / &100`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * d` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `4`; `s:real^3->bool`; `G0:real^3->real^3^3`; `G:real^3->real^3^3`;
                 `y:real^3`] LCK_DIST_MONO) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^3->bool`; `G0:real^3->real^3^3`; `G:real^3->real^3^3`;
                 `y:real^3`] P2C_LCK_DIST2_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* l = 0: LRG_RM_NEAR_BOUND *)
  SUBGOAL_THEN `lrm_deriv_norm2 0 (G:real^3->real^3^3) y <= C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `KN:real` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real^3->bool` THEN EXISTS_TAC `G0:real^3->real^3^3` THEN
    ASM_REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* l = 1, 2: P2C_DRM_BOUNDS and the norm comparison *)
  USE_THEN "drm" (MP_TAC o SPECL [`s:real^3->bool`; `G0:real^3->real^3^3`;
                                  `G:real^3->real^3^3`; `y:real^3`; `d:real`]) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "d" THEN
     REWRITE_TAC[p2c_hd] THEN
     MATCH_MP_TAC LRG_LCK_DIST2_TERM_LE THEN EXISTS_TAC `s:real^3->bool` THEN
     ASM_REWRITE_TAC[];
     STRIP_TAC]) THEN
  ABBREV_TAC `dl = sqrt(lck_dist2 2 (G0:real^3->real^3^3) G y)` THEN
  SUBGOAL_THEN `&0 <= dl /\ dl <= &1 / &10` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 / &100)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SQRT_UNIQUE THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `G0:real^3->real^3^3`; `G:real^3->real^3^3`;
                 `y:real^3`] P2C_METRIC_LAM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&1 - dl) /\ inv(&1 - dl) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `G:real^3->real^3^3`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^3->bool`; `G:real^3->real^3^3`;
                 `lrm4 (G:real^3->real^3^3)`] P2C_FIELD_D2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`5`; `s:real^3->bool`; `G:real^3->real^3^3`; `G0:real^3->real^3^3`;
                 `lnabla 4 G (lrm4 (G:real^3->real^3^3))`; `y:real^3`; `inv(&1 - dl)`]
                LRG_LTNORM2_COMPARE) THEN
  MP_TAC(ISPECL [`6`; `s:real^3->bool`; `G:real^3->real^3^3`; `G0:real^3->real^3^3`;
                 `lnabla 5 G (lnabla 4 G (lrm4 (G:real^3->real^3^3)))`; `y:real^3`;
                 `inv(&1 - dl)`] LRG_LTNORM2_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `inv(&1 - dl) pow 5 <= &64 /\ inv(&1 - dl) pow 6 <= &64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&2 pow 5`; EXISTS_TAC `&2 pow 6`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
       CONV_TAC REAL_RAT_REDUCE_CONV]);
    ALL_TAC] THEN
  ABBREV_TAC `D1 = ltnorm2 5 (G0:real^3->real^3^3) (lnabla 4 G (lrm4 G)) y` THEN
  ABBREV_TAC `D2 = ltnorm2 6 (G0:real^3->real^3^3) (lnabla 5 G (lnabla 4 G (lrm4 G))) y` THEN
  SUBGOAL_THEN `&0 <= D1 /\ &0 <= D2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D1"; "D2"] THEN CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&1 - dl) pow 5 * D1 <= C /\ inv(&1 - dl) pow 6 * D2 <= C`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&64 * CD * d` THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&64 * &1` THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);
    ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `l = 0 \/ l = 1 \/ l = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; num_CONV `1`; num_CONV `2`] THEN
  REWRITE_TAC[lnabla_iter; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;


(* ------------------------------------------------------------------------- *)
(* abs(nabla^l Rm)^2 under scaling and through parametrizations              *)
(* (rfa_rmd2 of the manifold at e v equals lrm_deriv_norm2 of the pullback   *)
(* at v: P2AP_PULLBACK_RMD_GEN of pc_p2a_par), and the                      *)
(* bound on eps-necks: rfa_rmd2 l (R(x) g) <= K at every point of the neck   *)
(* (the cylinder has parallel curvature, P2C_CYL_MODEL).                     *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_RMD2_CMUL = prove
 (`!top atlas (g:A->real^N^N) c l x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < c
     ==> rfa_rmd2 l atlas (\z. c %% g z) x = inv c pow (l + 2) * rfa_rmd2 l atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_rmd2; METRIC_LOCAL_CMUL] THEN
  MATCH_MP_TAC RFA_LRM_DERIV_NORM2_SCALE THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let RFA_HC2_NECK_RMD = prove
 (`?eps1 K. &0 < eps1 /\ &1 <= K /\
     !top atlas (g:A->real^3^3) eps x e v l.
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
       &0 < eps /\ eps <= eps1 /\ rfs_neck (top,atlas) g eps x e /\
       v IN rfs_neck_dom eps /\ l <= 2
       ==> rfa_rmd2 l atlas (\z. mfd_scalar atlas g x %% g z) (e v) <= K`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "par"))
    (SPEC `&4` RFA_HC2_PAR_RMD) THEN
  MAP_EVERY EXISTS_TAC [`min (&1 / &4) (inv C)`; `C:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `v:real^3`;
                       `l:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &4 /\ eps <= inv C` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  ABBREV_TAC `c = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `G = \y. c %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y` THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 4 (cylinder_flow (&0)) G v <= inv C` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2C_KREG_FOUR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`4`; `rfs_kreg eps`; `rfs_neck_dom eps`; `cylinder_flow (&0)`;
                   `G:real^3->real^3^3`; `v:real^3`] LCK_DIST_MONO) THEN
    ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN
    UNDISCH_TAC `!y. y IN rfs_neck_dom eps
                     ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                                   (G:real^3->real^3^3) y <= d` THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps pow 2 <= inv C` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps * &1` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `d < eps pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC P2C_CYL_MODEL THEN STRIP_TAC THEN
  USE_THEN "par" (MP_TAC o SPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
                                  `G:real^3->real^3^3`; `v:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[APX_NECK_CYL_FIELD] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 l (G:real^3->real^3^3) v =
                rfa_rmd2 l atlas (\z. c %% (g:A->real^3^3) z) ((e:real^3->A) v)`
  (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(e:real^3->A) v IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` THEN
    REWRITE_TAC[mfd_param; mfd_diffeo] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      can (find_term (fun t -> t = `top:A topology`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:real`; `l:num`; `(e:real^3->A) v`] RFA_HC2_RMD2_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "G" THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `c:real`; `l:num`; `v:real^3`] RFA_LRM_DERIV_NORM2_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2AP_PULLBACK_RMD_GEN THEN EXISTS_TAC `top:A topology` THEN
  EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Eps-round components.  In the preferred chart at y the                    *)
(* metric q g is C^4-close to g1, which has constant curvature 1 on the     *)
(* chart image of the component (P2C_COMPONENT_CONST_CURV, P2C_ROUND_MODEL:  *)
(* parallel Rm), so rfa_rmd2 l (q g) y <= C (RFA_HC2_PAR_RMD); R(x) >= 5 q   *)
(* (RFA_C2_ROUND_SCALAR_Q) gives the bound for R(x) g.                       *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_ROUND_RMD = prove
 (`?eps1 K. &0 < eps1 /\ &1 <= K /\
     !top atlas (g:A->real^3^3) eps U x y l.
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
       &0 < eps /\ eps <= eps1 /\ rfs_round_component (top,atlas) g eps U /\
       x IN U /\ y IN U /\ l <= 2
       ==> rfa_rmd2 l atlas (\z. mfd_scalar atlas g x %% g z) y <= K`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "par"))
    (SPEC `&36` RFA_HC2_PAR_RMD) THEN
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rq"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_ROUND_SCALAR_Q) THEN
  MAP_EVERY EXISTS_TAC [`min (&1 / &10) (min (inv C) (inv K1))`; `C:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`; `y:A`; `l:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ eps <= inv C /\ eps <= inv K1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_round_component]) THEN STRIP_TAC THEN
  (* R(x) and q *)
  REMOVE_THEN "rq" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `U:A->bool`; `q:real`; `g1:A->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&5 * q <= mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [SUBGOAL_THEN `K1 * eps <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1 * inv K1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&5 <= mfd_scalar atlas (g:A->real^3^3) x / q` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_mclose (rfs_kreg eps) eps atlas U (g1:A->real^3^3) (\x. q %% g x)` THEN
  REWRITE_TAC[rfs_mclose] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\ open_in top U` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `U:A->bool`] APX_COMPONENT_OPEN) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `phi:A->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `S = IMAGE (phi:A->real^3) (V INTER U)` THEN
  SUBGOAL_THEN `open(S:real^3->bool) /\ (phi:A->real^3) y IN S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `V:A->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas (V,phi) (g1:A->real^3^3)) /\
                metric_field S (metric_local atlas (V,phi) (g:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) V` THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [ALL_TAC; EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]) THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V,phi):(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas (V,phi) (\x. q %% (g:A->real^3^3) x) =
                (\z. q %% metric_local atlas (V,phi) g z)`
  SUBST_ALL_TAC THENL [REWRITE_TAC[METRIC_LOCAL_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `U:A->bool`; `V:A->bool`; `phi:A->real^3`] P2C_COMPONENT_CONST_CURV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `G1 = metric_local atlas (V,phi) (g1:A->real^3^3)` THEN
  ABBREV_TAC `Gg = metric_local atlas (V,phi) (g:A->real^3^3)` THEN
  ABBREV_TAC `yc = (phi:A->real^3) y` THEN
  SUBGOAL_THEN `metric_field S (\z. q %% (Gg:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`] P2C_ROUND_MODEL) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  (* closeness at yc *)
  SUBGOAL_THEN `lck_dist2 4 (G1:real^3->real^3^3) (\z. q %% Gg z) yc <= inv C` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2C_KREG_FOUR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`4`; `rfs_kreg eps`; `S:real^3->bool`; `G1:real^3->real^3^3`;
                   `\z. q %% (Gg:real^3->real^3^3) z`; `yc:real^3`] LCK_DIST_MONO) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps pow 2 <= inv C` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps * &1` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `d < eps pow 2` THEN UNDISCH_TAC
     `lck_dist2 (rfs_kreg eps) (G1:real^3->real^3^3) (\z. q %% Gg z) yc <= d` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "par" (MP_TAC o SPECL [`S:real^3->bool`; `G1:real^3->real^3^3`;
                                  `\z. q %% (Gg:real^3->real^3^3) z`; `yc:real^3`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `l:num`)] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Gg:real^3->real^3^3`; `q:real`; `l:num`; `yc:real^3`]
                RFA_LRM_DERIV_NORM2_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `R:real`; `l:num`; `y:A`] RFA_HC2_RMD2_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `rfa_rmd2 l atlas (g:A->real^3^3) y =
                lrm_deriv_norm2 l (Gg:real^3->real^3^3) (yc:real^3)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[rfa_rmd2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `l:num`; `y:A`] RFA_RMD2_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `D = lrm_deriv_norm2 l (Gg:real^3->real^3^3) yc` THEN
  SUBGOAL_THEN `inv R pow (l + 2) <= inv q pow (l + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv q pow (l + 2) * D` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The end neck of a cap.  A point y of the end neck e (centred              *)
(* at z in U) has rfa_rmd2 l (R(z) g) y <= K (RFA_HC2_NECK_RMD), and the     *)
(* ratio clause of the cap gives R(z) < C R(x), so rfa_rmd2 l (R(x) g) y <=  *)
(* C^4 K.                                                                     *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_RESCALE_RMD = prove
 (`!top atlas (g:A->real^3^3) a b M l y K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ &0 < a /\ &0 < b /\ b <= M * a /\ &1 <= M /\ &0 <= K /\ l <= 2 /\
     rfa_rmd2 l atlas (\z. b %% g z) y <= K
     ==> rfa_rmd2 l atlas (\z. a %% g z) y <= M pow 4 * K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `a:real`; `l:num`; `y:A`] RFA_HC2_RMD2_CMUL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `b:real`; `l:num`; `y:A`] RFA_HC2_RMD2_CMUL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST_ALL_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `l:num`; `y:A`] RFA_RMD2_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `D = rfa_rmd2 l atlas (g:A->real^3^3) y` THEN
  SUBGOAL_THEN `inv a pow (l + 2) * D = (b / a) pow (l + 2) * (inv b pow (l + 2) * D)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_INV] THEN
    UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b / a /\ b / a <= M` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M pow (l + 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let RFA_HC2_CAPEND_RMD = prove
 (`?eps1 K. &0 < eps1 /\ &1 <= K /\
     !top atlas (g:A->real^3^3) C eps U Y x z e y l.
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &1 < C /\
       &0 < eps /\ eps <= eps1 /\ rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
       rfs_neck (top,atlas) g eps z e /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
       y IN IMAGE e (rfs_neck_dom eps) /\ l <= 2
       ==> rfa_rmd2 l atlas (\w. mfd_scalar atlas g x %% g w) y <= C pow 4 * K`,
  X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk")))) (INST_TYPE [`:A`,`:A`] RFA_HC2_NECK_RMD) THEN
  MAP_EVERY EXISTS_TAC [`e1:real`; `K:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`] RFA_C2_RATIO_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN U` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `U:A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck_dom")) (concl th))) THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z (e:real^3->A)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) v IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `mfd_scalar atlas (g:A->real^3^3) z`;
                 `C:real`; `l:num`; `(e:real^3->A) v`; `K:real`] RFA_HC2_RESCALE_RMD) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[rfs_neck];
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    USE_THEN "nk" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The deep part of a canonical neighbourhood.  A curve from a               *)
(* closed set K to its complement has a last time t2 < 1 in K, and then     *)
(* gamma(t2) is in the frontier of K (RFA_HC2_LAST_TIME).  For a cap, the    *)
(* frontier of the closed core is in the central sphere of the boundary neck *)
(* e' (APX_BALL_CORE_TOP, APX_TWISTED_CORE_TOP), so a curve from the closed  *)
(* core leaving U crosses half of e' (APX_NECK_EXIT): its length is at least *)
(* sqrt(1 - eps) R(z')^(-1/2) / eps (RFA_HC2_CORE_EXIT), and the ball of     *)
(* radius 1/(2 sqrt(C R(x))) about a point of the closed core lies in U.     *)
(* The rest of a cap is its end neck (RFA_HC2_CAP_DATA).                     *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_AFFINE_CONT = prove
 (`!a c. &0 <= a /\ &0 <= c /\ a + c <= &1
         ==> continuous_map (subtopology euclideanreal (real_interval[&0,&1]),
                             subtopology euclideanreal (real_interval[&0,&1]))
                            (\s. a + c * s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real. a + c * s`; `&0`; `&1`; `&0`; `&1`] GRGD_REPARAM_CONTINUOUS) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL];
      MATCH_MP_TAC(REAL_ARITH `c * s <= c * &1 /\ a + c <= &1 ==> a + c * s <= &1`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ADD THEN REWRITE_TAC[REAL_DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_MUL_WITHIN THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_CONST; REAL_DIFFERENTIABLE_ID]]);;

let RFA_HC2_LAST_TIME = prove
 (`!top (gamma:real->A) K.
     continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) gamma /\
     closed_in top K /\ gamma(&0) IN K /\ ~(gamma(&1) IN K)
     ==> ?t2. &0 <= t2 /\ t2 < &1 /\ gamma t2 IN top frontier_of K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> (gamma:real->A) t IN topspace top`
  ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                                (gamma:real->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `(gamma:real->A) o (\s. &0 + -- &1 * s + &1)`;
                 `topspace top DIFF (K:A->bool)`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\s. &0 + -- &1 * s + &1) = (\s. &1 + -- &1 * s)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`\s:real. &1 + -- &1 * s`; `&0`; `&1`; `&0`; `&1`]
                    GRGD_REPARAM_CONTINUOUS) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_ADD THEN REWRITE_TAC[REAL_DIFFERENTIABLE_CONST] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_MUL_WITHIN THEN
      REWRITE_TAC[REAL_DIFFERENTIABLE_CONST; REAL_DIFFERENTIABLE_ID];
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      REWRITE_TAC[o_THM; IN_DIFF] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL];
      EXISTS_TAC `&1` THEN REWRITE_TAC[o_THM; IN_DIFF; IN_REAL_INTERVAL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM; IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "after"))))) THEN
  SUBGOAL_THEN `&0 + -- &1 * t1 + &1 = &1 - t1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) (&1 - t1) IN K` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 - t1 IN real_interval[&0,&1]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. &1 - t1 < u /\ u <= &1 ==> ~((gamma:real->A) u IN K)` (LABEL_TAC "out")
  THENL
   [REPEAT STRIP_TAC THEN USE_THEN "after" (MP_TAC o SPEC `&1 - u`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&0 + -- &1 * (&1 - u) + &1 = u`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `&1 - t1` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[frontier_of; CLOSURE_OF_CLOSED_IN; IN_DIFF] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `(gamma:real->A) o (\s. (&1 - t1) + t1 * s)`;
                 `top interior_of (K:A->bool)`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_HC2_AFFINE_CONT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[OPEN_IN_INTERIOR_OF];
      ASM_REWRITE_TAC[o_THM; REAL_MUL_RZERO; REAL_ADD_RID];
      EXISTS_TAC `&1` THEN REWRITE_TAC[o_THM; IN_REAL_INTERVAL; REAL_MUL_RID] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ARITH `(&1 - t1) + t1 = &1`] THEN
      MP_TAC(ISPECL [`top:A topology`; `K:A->bool`] INTERIOR_OF_SUBSET) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `t3 / &2`))))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "out" (MP_TAC o SPEC `(&1 - t1) + t1 * t3 / &2`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> a < a + x`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `t1 * s <= t1 * &1 ==> (&1 - t1) + t1 * s <= &1`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`top:A topology`; `K:A->bool`] INTERIOR_OF_SUBSET) THEN ASM SET_TAC[]]);;

let RFA_HC2_CAP_DATA = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     hausdorff_space top /\ rfs_cap (top,atlas) g C eps U Y
     ==> ?z e z' e'. rfs_neck (top,atlas) g eps z e /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
                     U DIFF top closure_of Y SUBSET IMAGE e (rfs_neck_dom eps) /\
                     rfs_neck (top,atlas) g eps z' e' /\
                     IMAGE e' (rfs_neck_dom eps) SUBSET U /\
                     closed_in top (top closure_of Y) /\ top closure_of Y SUBSET U /\
                     top frontier_of (top closure_of Y) SUBSET IMAGE e' (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`z:A`; `e:real^3->A`; `z':A`; `e':real^3->A`] THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`]
                  APX_BALL_CORE_TOP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_ball_chart top (atlas:((A->bool)#(A->real^3))->bool) (b:real^3->A)` THEN
      REWRITE_TAC[mfd_ball_chart];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (b:real^3->A) (ball(vec 0,&1)) SUBSET
                  top closure_of IMAGE b (ball(vec 0,&1))` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `cball(vec 0:real^3,&1) = ball(vec 0,&1) UNION sphere(vec 0,&1)`
    ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_REWRITE_TAC[IMAGE_UNION] THEN ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    MAP_EVERY EXISTS_TAC [`z:A`; `e:real^3->A`; `z':A`; `e':real^3->A`] THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`]
                  APX_TWISTED_CORE_TOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (p:real^3->A) (annulus (&1 / &2) (&2)) SUBSET
                  top closure_of IMAGE p (annulus (&1 / &2) (&2))` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (p:real^3->A) (sphere(vec 0,&1 / &2)) SUBSET
                  IMAGE p (sphere(vec 0,&2))` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `w:real^3` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      EXISTS_TAC `rfs_twist w` THEN ASM_SIMP_TAC[APX_TWIST_SPHERE] THEN
      UNDISCH_TAC `rfs_twisted_chart top (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A)` THEN
      REWRITE_TAC[rfs_twisted_chart] THEN
      DISCH_THEN(MP_TAC o SPECL [`w:real^3`; `rfs_twist w`] o CONJUNCT1) THEN
      ASM_SIMP_TAC[annulus; IN_ELIM_THM; APX_TWIST_SPHERE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
                  annulus (&1 / &2) (&2) UNION sphere(vec 0,&1 / &2) UNION sphere(vec 0,&2)`
    ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_REWRITE_TAC[IMAGE_UNION] THEN ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]]]);;

let RFA_HC2_CORE_EXIT = prove
 (`!top atlas (g:A->real^3^3) eps U K z' e' gamma.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < eps /\ eps < &1 /\ rfs_neck (top,atlas) g eps z' e' /\
     IMAGE e' (rfs_neck_dom eps) SUBSET U /\ closed_in top K /\ K SUBSET U /\
     top frontier_of K SUBSET IMAGE e' (sphere(vec 0,&1)) /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) IN K /\ ~(gamma(&1) IN U)
     ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z')) * inv eps <=
         mfd_length atlas g gamma (&0) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `K:A->bool`] RFA_HC2_LAST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve]; ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?v. v IN sphere(vec 0:real^3,&1) /\ (gamma:real->A) t2 = e' v`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `t2:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`; `v:real^3`; `gamma:real->A`;
                 `t2:real`; `&1`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval (v:real^3) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_SUB_RZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `t2:real`] MFD_LENGTH_POS_LE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_HC2_CAP_DEEP = prove
 (`!top atlas (g:A->real^3^3) C eps U Y x y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &1 < C /\ &0 < eps /\ eps <= &1 / &2 /\ rfs_cap (top,atlas) g C eps U Y /\
     x IN Y /\ y IN top closure_of Y
     ==> mfd_ball (top,atlas) g y (inv(&2 * sqrt(C * mfd_scalar atlas g x))) SUBSET U`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] RFA_HC2_CAP_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `e:real^3->A` (X_CHOOSE_THEN `z':A`
    (X_CHOOSE_THEN `e':real^3->A` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`] RFA_C2_RATIO_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z':A) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' (e':real^3->A)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z':A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) z'` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `Rx = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `Rz = mfd_scalar atlas (g:A->real^3^3) z'` THEN
  SUBGOAL_THEN `Rz <= C * Rx` ASSUME_TAC THENL
   [EXPAND_TAC "Rz" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * sqrt(C * Rx)) <= sqrt(&1 - eps) * inv(sqrt Rz) * inv eps`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt Rz /\ sqrt Rz <= sqrt(C * Rx) /\ &1 / &2 <= sqrt(&1 - eps) /\
                  &2 <= inv eps` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
         [CONV_TAC REAL_RAT_REDUCE_CONV;
          MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * sqrt Rz)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ &1 / &2 * y * &2 <= a * y * b ==> inv(&2) * y <= a * y * b`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(&1 - eps) * inv(sqrt Rz) * inv eps <=
                mfd_dist (top,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) y (w:A)`
  MP_TAC THENL
   [REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) (y:A) w` THEN
      REWRITE_TAC[mfd_joinable] THEN
      MESON_TAC[];
      REWRITE_TAC[GRGD_IN_LENGTHS] THEN X_GEN_TAC `L:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Rz" THEN
      MATCH_MP_TAC RFA_HC2_CORE_EXIT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `U:A->bool`; `top closure_of (Y:A->bool)`;
                            `e':real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let RFA_HC2_CCOMP_DEEP = prove
 (`!top atlas (g:A->real^N^N) U y r.
     smooth_manifold_atlas top atlas /\ U IN connected_components_of top /\ y IN U
     ==> mfd_ball (top,atlas) g y r SUBSET U`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
  X_GEN_TAC `w:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected_component_of top (y:A) w` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_CONNECTED_COMPONENT]; ALL_TAC] THEN
  UNDISCH_TAC `(U:A->bool) IN connected_components_of top` THEN
  REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y:A) IN U` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS]);;


(* ------------------------------------------------------------------------- *)
(* The static dichotomy.  At a point y of a (C,eps)-canonical                *)
(* neighbourhood U of x, either abs(nabla^l Rm)^2 of R(x) g is at most        *)
(* C^4 K (necks, round components, end necks of caps), or the ball of radius *)
(* 1/(2 sqrt(C R(x))) about y lies in U (closed cores of caps, C-components),*)
(* where R <= 2 C R(x) (RFA_C2_RATIO) and Shi's estimate applies.            *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_STATIC = prove
 (`?eps1 K. &0 < eps1 /\ &1 <= K /\
     !top atlas (g:A->real^3^3) C eps x U y l.
       hausdorff_space top /\ smooth_manifold_atlas top atlas /\
       riemannian_metric atlas g /\ &1 < C /\ &0 < eps /\ eps <= eps1 /\
       rfs_canonical_nbhd (top,atlas) g C eps x U /\ y IN U /\ l <= 2
       ==> rfa_rmd2 l atlas (\z. mfd_scalar atlas g x %% g z) y <= C pow 4 * K \/
           mfd_ball (top,atlas) g y (inv(&2 * sqrt(C * mfd_scalar atlas g x))) SUBSET U`,
  X_CHOOSE_THEN `en:real` (X_CHOOSE_THEN `Kn:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk")))) (INST_TYPE [`:A`,`:A`] RFA_HC2_NECK_RMD) THEN
  X_CHOOSE_THEN `er:real` (X_CHOOSE_THEN `Kd:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rd")))) (INST_TYPE [`:A`,`:A`] RFA_HC2_ROUND_RMD) THEN
  X_CHOOSE_THEN `ec:real` (X_CHOOSE_THEN `Kc:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ce")))) (INST_TYPE [`:A`,`:A`] RFA_HC2_CAPEND_RMD) THEN
  MAP_EVERY EXISTS_TAC [`min (&1 / &2) (min en (min er ec))`; `max Kn (max Kd Kc)`] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `C:real`; `eps:real`; `x:A`; `U:A->bool`; `y:A`;
                       `l:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &2 /\ eps <= en /\ eps <= er /\ eps <= ec` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!a. a <= max Kn (max Kd Kc) ==> a <= C pow 4 * max Kn (max Kd Kc)`
  (LABEL_TAC "up") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max Kn (max Kd Kc)` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_canonical_nbhd (top,atlas) (g:A->real^3^3) C eps x U` THEN
  REWRITE_TAC[rfs_canonical_nbhd] THEN STRIP_TAC THENL
   [(* neck *)
    DISJ1_TAC THEN USE_THEN "up" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:A) IN U` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kn:real` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    USE_THEN "nk" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN ASM_REWRITE_TAC[];
    (* cap *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] RFA_HC2_CAP_DATA) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `e:real^3->A` (X_CHOOSE_THEN `z':A`
      (X_CHOOSE_THEN `e':real^3->A` STRIP_ASSUME_TAC)))) THEN
    ASM_CASES_TAC `(y:A) IN top closure_of Y` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC RFA_HC2_CAP_DEEP THEN
      MAP_EVERY EXISTS_TAC [`eps:real`; `Y:A->bool`] THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C pow 4 * Kc` THEN CONJ_TAC THENL
       [USE_THEN "ce" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`; `U:A->bool`; `Y:A->bool`;
                              `z:A`; `e:real^3->A`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]];
    (* C-component *)
    DISJ2_TAC THEN MATCH_MP_TAC RFA_HC2_CCOMP_DEEP THEN
    ASM_MESON_TAC[rfs_c_component];
    (* round component *)
    DISJ1_TAC THEN USE_THEN "up" MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kd:real` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    USE_THEN "rd" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[]]);;

