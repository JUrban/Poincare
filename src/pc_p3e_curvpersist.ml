(* ========================================================================= *)
(* Unit pc_p3e_curvpersist: step S9 of the proof of MT Lemma 15.11: the      *)
(* uniform time t1 of the disappearing region in rfs_surgery_ok.  Points     *)
(* removed at a surgery either leave Omega (R -> infinity) or lie outside    *)
(* Omega_rho (R -> R(gl) > rho^-2); at canonical neighbourhoods              *)
(* |dR/dt| <= max C 2 R^2 (P2C_CANON_DERIV), so high curvature persists up   *)
(* to the surgery time, and compactness gives one t1.  Uses P3E_LIMIT_SCALAR *)
(* (pc_p3e_limscal), P2C_ODE_BACKWARD (pc_p2c_l112), P2C_CANON_DERIV         *)
(* (pc_p2c_cderiv), RFA_MFD_SCALAR_EVOLUTION and RFA_MFD_SCALAR_CHART        *)
(* (pc_rfa_scalar), APX_RFS_SLAB (pc_apx_event), MFD_SCALAR_CONTINUOUS       *)
(* (pc_apx_scal).                                                            *)
(* ========================================================================= *)

needs "src/pc_p3e_limscal.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_rfa_scalar.ml";;
needs "src/pc_apx_scal.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Persistence of high scalar curvature forward in time along a Ricci flow,  *)
(* S9(c).  The time derivative of R(x,.) is Lap R + 2|Ric|^2 in the form of  *)
(* rfs_scalar_lap and rfs_ric_norm2 (RFA_MFD_SCALAR_EVOLUTION                *)
(* with the chart bridge of its proof).  If R(x,a) > 2L and |Lap R +        *)
(* 2|Ric|^2| <= Cd R^2 wherever R >= L on [a,s], with 2 Cd (s - a) L <= 1,   *)
(* then R(x,s) > L: else the backward comparison P2C_ODE_BACKWARD from      *)
(* (x,s) gives R(x,a) <= 2L.                                                 *)
(* ------------------------------------------------------------------------- *)

let P3E_RFA_LAP_SCALAR = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) g x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> rfa_lap atlas g (mfd_scalar atlas g) x = rfs_scalar_lap atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_lap; rfs_scalar_lap] THEN
  MATCH_MP_TAC RFA_LLAP_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                 `chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) z`]
         RFA_MFD_SCALAR_CHART) THEN
  ASM_SIMP_TAC[]);;

let P3E_SCALAR_EVOL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a b g t x.
     ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
     ==> ((\s. mfd_scalar atlas (g s) x) has_real_derivative
          (rfs_scalar_lap atlas (g t) x + &2 * rfs_ric_norm2 atlas (g t) x)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^3^3) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `x:A`] P3E_RFA_LAP_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[rfs_ric_norm2; P2C_LRIC2_ETA] THEN
  MATCH_MP_TAC RFA_MFD_SCALAR_EVOLUTION THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[]);;

let P3E_FLOW_PERSIST = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a0 b0 g x Cd L a s.
     ricci_flow_on (top,atlas) a0 b0 g /\ x IN topspace top /\
     a0 < a /\ a <= s /\ s < b0 /\ &0 < Cd /\ &0 < L /\
     (!t. a <= t /\ t <= s /\ L <= mfd_scalar atlas (g t) x
          ==> abs(rfs_scalar_lap atlas (g t) x + &2 * rfs_ric_norm2 atlas (g t) x) <=
              Cd * mfd_scalar atlas (g t) x pow 2) /\
     &2 * Cd * (s - a) * L <= &1 /\ &2 * L < mfd_scalar atlas (g a) x
     ==> L < mfd_scalar atlas (g s) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. a <= u /\ u <= s
        ==> ((\u. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                             ((g:real->A->real^3^3) u) x) has_real_derivative
             (rfs_scalar_lap atlas (g u) x + &2 * rfs_ric_norm2 atlas (g u) x)) (atreal u)`
  (LABEL_TAC "DER") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_SCALAR_EVOL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a0:real`; `b0:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real = s` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Cd * (s - a) * L < &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) u) x)
    real_continuous_on real_interval[a,s]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `rfs_scalar_lap (atlas:((A->bool)#(A->real^3))->bool)
                  ((g:real->A->real^3^3) u) x +
                &2 * rfs_ric_norm2 atlas (g u) x` THEN
    USE_THEN "DER" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) x <= L
    ==> mfd_scalar atlas (g a) x <= &2 * L`
  MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\u. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) u) x`;
      `\u. rfs_scalar_lap (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) u) x +
           &2 * rfs_ric_norm2 atlas (g u) x`;
      `s:real`; `a:real`; `Cd:real`; `L:real`; `L:real`] P2C_ODE_BACKWARD) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THENL
       [USE_THEN "DER" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    SUBGOAL_THEN `&0 < &1 - Cd * (s - a) * L` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= L * (&1 - &2 * Cd * (s - a) * L)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The last slab of a history (the view at t in [T_n, horizon)               *)
(* is stage n), the canonical neighbourhood assumption at a point, and the  *)
(* derivative bound at canonical points of the last slab, S9(b): a point     *)
(* (x,t) with R(x,t) >= rp(t)^-2 has a strong canonical neighbourhood,       *)
(* hence a canonical neighbourhood in the slice, so |Lap R + 2|Ric|^2| <=    *)
(* max C 2 R^2 there (P2C_CANON_DERIV).                                      *)
(* ------------------------------------------------------------------------- *)

let P3E_LAST_SLAB_VIEW = prove
 (`!(hs:(A)rfs_history) t.
     rfs_history_ok hs /\ hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs
     ==> &0 <= t /\
         rfs_vtop (rfs_view hs) t = hs_top hs (hs_count hs) /\
         rfs_vatlas (rfs_view hs) t = hs_atlas hs (hs_count hs) /\
         rfs_vmetric (rfs_view hs) t = hs_metric hs (hs_count hs) t /\
         (!x. rfs_vscalar (rfs_view hs) t x =
              mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`; `t:real`]
    APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL; GSYM rfs_horizon]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
  UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t` THEN SIMP_TAC[rfs_live]);;

let P3E_LAST_SLAB_FLOW = prove
 (`!(hs:(A)rfs_history).
     rfs_history_ok hs
     ==> hs_time hs (hs_count hs) < rfs_horizon hs /\
         &0 <= hs_time hs (hs_count hs) /\
         hausdorff_space (hs_top hs (hs_count hs)) /\
         smooth_manifold_atlas (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
         compact_space (hs_top hs (hs_count hs)) /\
         ricci_flow_on (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                       (hs_time hs (hs_count hs)) (rfs_horizon hs)
                       (hs_metric hs (hs_count hs)) /\
         (!t. hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs
              ==> riemannian_metric (hs_atlas hs (hs_count hs))
                                    (hs_metric hs (hs_count hs) t))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `hs_count(hs:(A)rfs_history)` o CONJUNCT1 o CONJUNCT2 o
              CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  REWRITE_TAC[LE_REFL; GSYM rfs_horizon] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ricci_flow_from (hs_top (hs:(A)rfs_history) (hs_count hs),
                                hs_atlas hs (hs_count hs))
                               (hs_time hs (hs_count hs)) (rfs_horizon hs)
                               (hs_metric hs (hs_count hs))` THEN
  REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ricci_flow_on (hs_top (hs:(A)rfs_history) (hs_count hs),
                              hs_atlas hs (hs_count hs))
                             (hs_time hs (hs_count hs)) (rfs_horizon hs)
                             (hs_metric hs (hs_count hs))` THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_time (hs:(A)rfs_history) (hs_count hs)`]
      P3E_LAST_SLAB_VIEW) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t = hs_time (hs:(A)rfs_history) (hs_count hs)` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P3E_CANON_ASSUMPTION_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps rp t x.
     rfs_canonical_assumption V C eps rp /\ &0 <= t /\ x IN topspace(rfs_vtop V t) /\
     inv(rp t pow 2) <= rfs_vscalar V t x
     ==> ?U. rfs_strong_canonical V C eps x t U`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_canonical_assumption; rfs_vtop; rfs_vscalar] THEN
  MESON_TAC[]);;

let P3E_HIST_CANON_BOUND = prove
 (`?eps0. &0 < eps0 /\
     !(hs:(A)rfs_history) C eps rp t x.
       &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\
       rfs_canonical_assumption (rfs_view hs) C eps rp /\
       hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs /\
       x IN topspace(hs_top hs (hs_count hs)) /\
       inv(rp t pow 2) <=
       mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t) x
       ==> abs(rfs_scalar_lap (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t) x +
               &2 * rfs_ric_norm2 (hs_atlas hs (hs_count hs))
                                  (hs_metric hs (hs_count hs) t) x)
           <= max C (&2) *
              mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t) x
              pow 2`,
  MP_TAC(ISPEC `(:A)` P2C_CANON_DERIV) THEN REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CD"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` P3E_LAST_SLAB_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P3E_LAST_SLAB_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `C:real`; `eps:real`; `rp:real->real`;
                 `t:real`; `x:A`] P3E_CANON_ASSUMPTION_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `U:A->bool`) THEN
  SUBGOAL_THEN
   `rfs_canonical_nbhd (hs_top (hs:(A)rfs_history) (hs_count hs),hs_atlas hs (hs_count hs))
                       (hs_metric hs (hs_count hs) t) C eps x U`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_canonical (rfs_view (hs:(A)rfs_history)) C eps x t U` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]) THEN
    REWRITE_TAC[rfs_view; rfs_strong_canonical; rfs_canonical_nbhd; rfs_strong_neck;
                rfs_evolving_neck] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "CD" (MP_TAC o SPECL
    [`hs_top (hs:(A)rfs_history) (hs_count hs)`; `hs_atlas (hs:(A)rfs_history) (hs_count hs)`;
     `hs_metric (hs:(A)rfs_history) (hs_count hs) t`; `C:real`; `eps:real`; `x:A`;
     `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The uniform time t1 for a compact set of the last stage, S9(d).           *)
(* Lam = rp(T)^-2 at the horizon T.  If every y in the compact K has times   *)
(* s arbitrarily close to T (in the last slab) with R(y,s) > 2 Lam, then for *)
(* one t1 < T every (x,t) with x in K and t1 < t < T has a strong canonical  *)
(* neighbourhood: take s_y with T - s_y < d0 = min (T - T_n) (1/(2 Cd Lam)); *)
(* the sets R(.,s_y) > 2 Lam are open and cover K; a finite subcover gives   *)
(* t1 = max s_y; P3E_FLOW_PERSIST keeps R > Lam >= rp(t)^-2 after s_y.       *)
(* ------------------------------------------------------------------------- *)

let P3E_DISAPPEAR_T1 = prove
 (`?eps0. &0 < eps0 /\
     !(hs:(A)rfs_history) C eps rp K.
       &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\
       rfs_canonical_assumption (rfs_view hs) C eps rp /\
       (!t. &0 <= t ==> &0 < rp t) /\
       (!s t. &0 <= s /\ s <= t ==> rp t <= rp s) /\
       compact_in (hs_top hs (hs_count hs)) K /\
       (!y d. y IN K /\ &0 < d
              ==> ?s. rfs_horizon hs - d < s /\ hs_time hs (hs_count hs) <= s /\
                      s < rfs_horizon hs /\
                      &2 * inv(rp(rfs_horizon hs) pow 2) <
                      mfd_scalar (hs_atlas hs (hs_count hs))
                                 (hs_metric hs (hs_count hs) s) y)
       ==> ?t1. hs_time hs (hs_count hs) <= t1 /\ t1 < rfs_horizon hs /\
                !t x. t1 < t /\ t < rfs_horizon hs /\ x IN K
                      ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x t U`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CB"))
    P3E_HIST_CANON_BOUND THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `rp:real->real`;
                       `K:A->bool`] THEN
  ABBREV_TAC `Lam = inv(rp(rfs_horizon (hs:(A)rfs_history)) pow 2)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CA") (CONJUNCTS_THEN2 (LABEL_TAC "RP0")
    (CONJUNCTS_THEN2 (LABEL_TAC "RPM") (CONJUNCTS_THEN2 (LABEL_TAC "CPT")
     (LABEL_TAC "LARGE"))))))))) THEN
  (* the last slab *)
  MP_TAC(ISPEC `hs:(A)rfs_history` P3E_LAST_SLAB_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* Lam, Cd, d0 *)
  SUBGOAL_THEN `&0 < Lam` ASSUME_TAC THENL
   [EXPAND_TAC "Lam" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN
    USE_THEN "RP0" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= rfs_horizon (hs:(A)rfs_history)
                    ==> inv(rp t pow 2) <= Lam` (LABEL_TAC "LAM") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Lam" THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN USE_THEN "RP0" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "RP0" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        USE_THEN "RPM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `Cd = max C (&2)` THEN
  SUBGOAL_THEN `&0 < Cd` ASSUME_TAC THENL [EXPAND_TAC "Cd" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d0 = min (rfs_horizon (hs:(A)rfs_history) - hs_time hs (hs_count hs))
                       (inv(&2 * Cd * Lam))` THEN
  SUBGOAL_THEN `&0 < d0` ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u < d0 ==> &2 * Cd * u * Lam <= &1` (LABEL_TAC "D0") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `u <= inv(&2 * Cd * Lam)` MP_TAC THENL
     [UNDISCH_TAC `u < d0` THEN EXPAND_TAC "d0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * Cd * Lam` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ
      (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < &2 * Cd * Lam`))) THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_horizon (hs:(A)rfs_history) - d0 >= hs_time hs (hs_count hs)`
  ASSUME_TAC THENL [EXPAND_TAC "d0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the times s_y *)
  SUBGOAL_THEN
   `?sf:A->real. !y. y IN K
       ==> rfs_horizon (hs:(A)rfs_history) - d0 < sf y /\
           hs_time hs (hs_count hs) <= sf y /\ sf y < rfs_horizon hs /\
           &2 * Lam < mfd_scalar (hs_atlas hs (hs_count hs))
                                 (hs_metric hs (hs_count hs) (sf y)) y`
  (X_CHOOSE_THEN `sf:A->real` (LABEL_TAC "SF")) THENL
   [SUBGOAL_THEN
     `!y. y IN K
          ==> ?s. rfs_horizon (hs:(A)rfs_history) - d0 < s /\
                  hs_time hs (hs_count hs) <= s /\ s < rfs_horizon hs /\
                  &2 * Lam < mfd_scalar (hs_atlas hs (hs_count hs))
                                        (hs_metric hs (hs_count hs) s) y`
    MP_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      USE_THEN "LARGE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the open cover and a finite subcover *)
  ABBREV_TAC
   `Vf = \y:A. {x | x IN topspace(hs_top (hs:(A)rfs_history) (hs_count hs)) /\
                    mfd_scalar (hs_atlas hs (hs_count hs))
                               (hs_metric hs (hs_count hs) (sf y)) x > &2 * Lam}` THEN
  SUBGOAL_THEN
   `?FF:A->bool. FINITE FF /\ FF SUBSET K /\ K SUBSET UNIONS (IMAGE (Vf:A->A->bool) FF)`
  (X_CHOOSE_THEN `F0:A->bool` STRIP_ASSUME_TAC) THENL
   [USE_THEN "CPT" (MP_TAC o GEN_REWRITE_RULE I [compact_in]) THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (Vf:A->A->bool) K` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
        EXPAND_TAC "Vf" THEN
        MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                       `mfd_scalar (hs_atlas (hs:(A)rfs_history) (hs_count hs))
                                   (hs_metric hs (hs_count hs) ((sf:A->real) y))`]
          CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LT) THEN
        MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q /\ s) ==> r`) THEN
        CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "SF" (MP_TAC o SPEC `y:A`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
        X_GEN_TAC `y:A` THEN DISCH_TAC THEN EXISTS_TAC `y:A` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Vf" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        USE_THEN "SF" (MP_TAC o SPEC `y:A`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        ASM_REWRITE_TAC[real_gt] THEN
        USE_THEN "CPT" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [compact_in]) THEN
        ASM SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `VV:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`Vf:A->A->bool`; `K:A->bool`; `VV:(A->bool)->bool`]
        FINITE_SUBSET_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `F1:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `F1:A->bool` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* t1 = the largest of T - d0 and the s_y of the subcover *)
  MP_TAC(ISPEC `(rfs_horizon (hs:(A)rfs_history) - d0) INSERT IMAGE (sf:A->real) F0`
    SUP_FINITE_LEMMA) THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:real` THEN
  SUBGOAL_THEN `rfs_horizon (hs:(A)rfs_history) - d0 <= t1 /\
                !y. y IN F0 ==> (sf:A->real) y <= t1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `t1 IN (rfs_horizon (hs:(A)rfs_history) - d0) INSERT IMAGE (sf:A->real) F0` THEN
    REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "SF" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  (* the canonical neighbourhoods after t1 *)
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y:A. y IN F0 /\ (x:A) IN (Vf:A->A->bool) y` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET UNIONS (IMAGE (Vf:A->A->bool) F0)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:A) IN Vf (y:A)` THEN EXPAND_TAC "Vf" THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt] THEN STRIP_TAC THEN
  USE_THEN "SF" (MP_TAC o SPEC `y:A`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(sf:A->real) y <= t1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* persistence from (x, sf y) to (x, t) along the slab flow *)
  SUBGOAL_THEN
   `Lam < mfd_scalar (hs_atlas (hs:(A)rfs_history) (hs_count hs))
                     (hs_metric hs (hs_count hs) t) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_FLOW_PERSIST THEN
    MAP_EVERY EXISTS_TAC
     [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
      `hs_time (hs:(A)rfs_history) (hs_count hs)`; `rfs_horizon (hs:(A)rfs_history)`;
      `Cd:real`; `(sf:A->real) y`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN EXPAND_TAC "Cd" THEN
      SUBGOAL_THEN
       `inv(rp u pow 2) <= mfd_scalar (hs_atlas (hs:(A)rfs_history) (hs_count hs))
                                      (hs_metric hs (hs_count hs) u) x`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "LAM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "CB" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`eps:real`; `rp:real->real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "D0" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the canonical neighbourhood assumption at (x,t) *)
  SUBGOAL_THEN `inv(rp t pow 2) <= rfs_vscalar (rfs_view (hs:(A)rfs_history)) t x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P3E_LAST_SLAB_VIEW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "LAM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P3E_CANON_ASSUMPTION_AT THEN EXISTS_TAC `rp:real->real` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P3E_LAST_SLAB_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT1(CONJUNCT2 th)]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The removed points have large curvature near the surgery                  *)
(* time, S9(a), and the uniform t1 for a compact set off Omega_rho.  A point *)
(* y of the last stage outside Omega_rho either is not in Omega = p3_omega   *)
(* (R(y,t) -> infinity: Omega is the set where R stays bounded along times   *)
(* tending to T) or has R(gl)(y) > rho^-2 >= 2 Lam, and R(y,t) -> R(gl)(y)   *)
(* (P3E_LIMIT_SCALAR); either way R(y,s) > 2 Lam at times s arbitrarily     *)
(* close to T.                                                               *)
(* ------------------------------------------------------------------------- *)

let P3E_REMOVED_LARGE = prove
 (`!(hs:(A)rfs_history) gl rho Lam y d.
     rfs_history_ok hs /\
     open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                      (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     &2 * Lam <= inv(rho pow 2) /\
     y IN topspace(hs_top hs (hs_count hs)) /\
     ~(y IN p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rho) /\ &0 < d
     ==> ?s. rfs_horizon hs - d < s /\ hs_time hs (hs_count hs) <= s /\
             s < rfs_horizon hs /\
             &2 * Lam < mfd_scalar (hs_atlas hs (hs_count hs))
                                   (hs_metric hs (hs_count hs) s) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (hs_count hs) < rfs_horizon hs` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_horizon] THEN
    FIRST_ASSUM(MP_TAC o SPEC `hs_count(hs:(A)rfs_history)` o CONJUNCT1 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:A) IN p3_omega hs` THENL
   [SUBGOAL_THEN `&2 * Lam < mfd_scalar (hs_atlas (hs:(A)rfs_history) (hs_count hs)) gl y`
    ASSUME_TAC THENL
     [UNDISCH_TAC `~((y:A) IN p3_omega_rho (hs_atlas (hs:(A)rfs_history) (hs_count hs))
                                (p3_omega hs) gl rho)` THEN
      ASM_REWRITE_TAC[p3_omega_rho; IN_ELIM_THM; REAL_NOT_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                   `hs_atlas (hs:(A)rfs_history) (hs_count hs)`;
                   `p3_omega (hs:(A)rfs_history)`; `rfs_horizon (hs:(A)rfs_history)`;
                   `hs_metric (hs:(A)rfs_history) (hs_count hs)`; `gl:A->real^3^3`; `y:A`]
      P3E_LIMIT_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `hs_count(hs:(A)rfs_history)` o CONJUNCT1 o CONJUNCT2 o
                  CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
      REWRITE_TAC[LE_REFL; GSYM rfs_horizon; ricci_flow_from; ricci_flow_on] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `rfs_horizon (hs:(A)rfs_history) - hs_time hs (hs_count hs)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC
      `mfd_scalar (hs_atlas (hs:(A)rfs_history) (hs_count hs)) gl y - &2 * Lam`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `rfs_horizon (hs:(A)rfs_history) -
                min (min d e1) (rfs_horizon hs - hs_time hs (hs_count hs)) / &2` THEN
    SUBGOAL_THEN `&0 < min (min d e1) (rfs_horizon (hs:(A)rfs_history) -
                                       hs_time hs (hs_count hs))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rfs_horizon (hs:(A)rfs_history) -
                min (min d e1) (rfs_horizon hs - hs_time hs (hs_count hs)) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `~((y:A) IN p3_omega hs)` THEN
    ASM_REWRITE_TAC[p3_omega; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&2 * Lam`) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(max (max t1 (rfs_horizon (hs:(A)rfs_history) - d))
                     (hs_time hs (hs_count hs)) + rfs_horizon hs) / &2` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `(max (max t1 (rfs_horizon (hs:(A)rfs_history) - d))
            (hs_time hs (hs_count hs)) + rfs_horizon hs) / &2`) THEN
    ASM_REAL_ARITH_TAC]);;

let P3E_DISAPPEAR_OMEGA = prove
 (`?eps0. &0 < eps0 /\
     !(hs:(A)rfs_history) C eps rp gl rho K.
       &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\
       rfs_canonical_assumption (rfs_view hs) C eps rp /\
       (!t. &0 <= t ==> &0 < rp t) /\
       (!s t. &0 <= s /\ s <= t ==> rp t <= rp s) /\
       open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
       rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                        (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
       &2 * inv(rp(rfs_horizon hs) pow 2) <= inv(rho pow 2) /\
       compact_in (hs_top hs (hs_count hs)) K /\
       DISJOINT K (p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rho)
       ==> ?t1. hs_time hs (hs_count hs) <= t1 /\ t1 < rfs_horizon hs /\
                !t x. t1 < t /\ t < rfs_horizon hs /\ x IN K
                      ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x t U`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1"))
    P3E_DISAPPEAR_T1 THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "T1" MATCH_MP_TAC THEN EXISTS_TAC `rp:real->real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `d:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3E_REMOVED_LARGE THEN
  MAP_EVERY EXISTS_TAC [`gl:A->real^3^3`; `rho:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `compact_in (hs_top (hs:(A)rfs_history) (hs_count hs)) K` THEN
    REWRITE_TAC[compact_in] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

