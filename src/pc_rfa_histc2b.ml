(* ========================================================================= *)
(* Unit pc_rfa_histc2b: the dynamic part of R13 for the deep balls of        *)
(* canonical neighbourhoods (RFA_HC2_STATIC of pc_rfa_histc2a), away from    *)
(* fresh surgery caps: the early-time bound (R >= eps^-2 forces t >= Tst, by *)
(* the doubling time on the normalized initial stage and the maximality of   *)
(* slab 0); the backward comparison of R along flow lines with derivative    *)
(* bounds only before the top time (RFA_HC2_TIME_BACK, the pattern of        *)
(* P2C_DB_TIME_BACK); and Shi's estimate in scale-invariant form             *)
(* (RFA_C2_SHI_SCALED) on a region of the regular view persisting over the   *)
(* window, with the region glue of pc_p2a_par.                               *)
(* ========================================================================= *)

needs "src/pc_rfa_histc2a.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The backward comparison of R along a flow line of a regular               *)
(* view: if abs(dR/dt) <= C R^2 wherever R >= r0^-2 at the times u in       *)
(* (t',t0) (open: no bound needed at the top time), y persists over         *)
(* (t',t0] and R(y,t0) <= 16/9 Q, then R(y,s) <= 2 Q on (t',t0] when         *)
(* t0 - t' <= 1/(16 C Q).  The proof of P2C_DB_TIME_BACK (pc_p2c_l112) with  *)
(* the weaker hypothesis; it uses only the continuity, evolution and ODE     *)
(* lemmas of Part 2C.                                                        *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_TIME_BACK = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C r0 t0 t' B Q s y.
     p2c_regular_view V /\ &0 < C /\ &0 < r0 /\ &0 < Q /\ inv(r0 pow 2) <= Q /\
     (!u. t' < u /\ u < t0 /\ inv(r0 pow 2) <= rfs_vscalar V u y
          ==> abs(rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) y +
                  &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y) <=
              C * rfs_vscalar V u y pow 2) /\
     t0 - t' <= inv(&16 * C * Q) /\ rfs_persists V B t' t0 /\
     t' < s /\ s <= t0 /\ y IN B /\ rfs_vscalar V t0 y <= &16 / &9 * Q
     ==> rfs_vscalar V s y <= &2 * Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `C * (t0 - s) * (&16 / &9 * Q) <= &1 / &9` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_DB_ARITH1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\u. rfs_vscalar V u (y:A)) real_continuous_on real_interval[s,t0]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_VIEW_SCALAR_CONT_UPTO THEN
    MAP_EVERY EXISTS_TAC [`B:A->bool`; `t':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval(s,t0)
        ==> ((\u. rfs_vscalar V u (y:A)) has_real_derivative
             rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) y +
             &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y) (atreal u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2C_VIEW_SCALAR_EVOL THEN
    MAP_EVERY EXISTS_TAC [`B:A->bool`; `t':real`; `t0:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval(s,t0) /\ inv(r0 pow 2) <= rfs_vscalar V u (y:A)
        ==> abs(rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) y +
                &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y) <=
            C * rfs_vscalar V u y pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_lap")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IN")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\u. rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) u (y:A)`;
     `\u. rfs_scalar_lap (rfs_vatlas (V:(real->A topology)#
            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
            (rfs_vmetric V u) (y:A) +
          &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y`;
     `t0:real`; `s:real`; `C:real`; `inv(r0 pow 2)`; `&16 / &9 * Q`] P2C_ODE_BACKWARD)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P2C_DB_ARITH2 THEN
  EXISTS_TAC `C * (t0 - s) * (&16 / &9 * Q)` THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* In a history with the canonical neighbourhood assumption                  *)
(* before t (rfs_trunc), points with R >= rp(t)^-2 at times u < t have the  *)
(* derivative bounds of P2C_CANON_DERIV (rp is non-increasing), so along    *)
(* the flow line of a point of a set persisting over (a,t], R(t) <= Q gives *)
(* R <= 2 Q on (a,t] when t - a <= 1/(16 max(C,2) Q).                       *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_HIST_DB = prove
 (`?eps1. &0 < eps1 /\
     !C eps (rp:real->real) (hs:(A)rfs_history) t u w.
       &1 < C /\ &0 < eps /\ eps <= eps1 /\ p2c_regular_view (rfs_view hs) /\
       (!s. &0 <= s ==> &0 < rp s) /\ (!s t. &0 <= s /\ s <= t ==> rp t <= rp s) /\
       rfs_canonical_assumption (rfs_trunc (rfs_view hs) t) C eps rp /\
       &0 <= u /\ u < t /\ w IN topspace(rfs_top_at hs u) /\
       inv(rp t pow 2) <= rfs_vscalar (rfs_view hs) u w
       ==> abs(rfs_scalar_lap (rfs_vatlas (rfs_view hs) u) (rfs_vmetric (rfs_view hs) u) w +
               &2 * rfs_ric_norm2 (rfs_vatlas (rfs_view hs) u) (rfs_vmetric (rfs_view hs) u) w)
           <= max C (&2) * rfs_vscalar (rfs_view hs) u w pow 2`,
  MP_TAC(ISPEC `(:A)` P2C_CANON_DERIV) THEN REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv((rp:real->real) u pow 2) <= inv(rp (t:real) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?U. rfs_canonical_nbhd (rfs_top_at hs u,rfs_atlas_at hs u)
                      (rfs_metric_at (hs:(A)rfs_history) u) C eps (w:A) U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_canonical_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) t)
                   C eps rp` THEN
    REWRITE_TAC[rfs_canonical_assumption; rfs_trunc; rfs_view] THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real`; `w:A`]) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `inv((rp:real->real) t pow 2) <=
                    rfs_vscalar (rfs_view (hs:(A)rfs_history)) u (w:A)` THEN
      REWRITE_TAC[rfs_vscalar; rfs_view] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[rfs_strong_canonical; rfs_canonical_nbhd; rfs_strong_neck;
                rfs_evolving_neck] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `u:real`; `w:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN STRIP_TAC THEN
  REMOVE_THEN "cd" (MP_TAC o SPECL [`rfs_top_at (hs:(A)rfs_history) u`; `rfs_atlas_at (hs:(A)rfs_history) u`;
    `rfs_metric_at (hs:(A)rfs_history) u`; `C:real`; `eps:real`; `w:A`; `U:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let RFA_HC2_HIST_BACK = prove
 (`?eps1. &0 < eps1 /\
     !C eps (rp:real->real) (hs:(A)rfs_history) t B a Q s w.
       &1 < C /\ &0 < eps /\ eps <= eps1 /\ p2c_regular_view (rfs_view hs) /\
       (!s. &0 <= s ==> &0 < rp s) /\ (!s t. &0 <= s /\ s <= t ==> rp t <= rp s) /\
       rfs_canonical_assumption (rfs_trunc (rfs_view hs) t) C eps rp /\
       &0 <= a /\ a < t /\ rfs_persists (rfs_view hs) B a t /\ w IN B /\
       rfs_vscalar (rfs_view hs) t w <= Q /\ inv(rp t pow 2) <= Q /\
       t - a <= inv(&16 * max C (&2) * Q) /\ a < s /\ s <= t
       ==> rfs_vscalar (rfs_view hs) s w <= &2 * Q`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "db"))
    (INST_TYPE [`:A`,`:A`] RFA_HC2_HIST_DB) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (rp:real->real) t` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((rp:real->real) t pow 2)` THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_HC2_TIME_BACK THEN
  MAP_EVERY EXISTS_TAC [`max C (&2)`; `(rp:real->real) t`; `t:real`; `a:real`; `B:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN USE_THEN "db" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `rp:real->real`; `t:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) B a t` THEN
    REWRITE_TAC[rfs_persists; rfs_view] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ASM_REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Early times.  On the normalized initial stage abs Rm <= 1,                *)
(* so abs Rm^2 <= H0 (RFA_LRM_SECTIONAL_BOUND), and the doubling time        *)
(* (RFA_RMD2_DOUBLING) keeps abs Rm^2 <= 4 H0 up to Tst = 1/(Cp sqrt H0):   *)
(* slab 0 is maximal, so the first event comes after Tst, and R <= 12       *)
(* sqrt H0 before Tst.  Hence R(x,t) >= eps^-2 with eps small forces        *)
(* t >= Tst (RFA_HC2_EARLY).                                                 *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_RMD0_BOUNDS = prove
 (`!top atlas (g:A->real^3^3) x H.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     rfa_rmd2 0 atlas g x <= H
     ==> mfd_rm_norm atlas g x <= sqrt H /\ mfd_scalar atlas g x <= &6 * sqrt H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v}
                      ==> abs(mfd_sectional atlas (g:A->real^3^3) x u v) <= sqrt H`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(rfa_rmd2 0 atlas (g:A->real^3^3) x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_RMD2 THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3, basis 1, basis 2}` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_NONCOLLINEAR_BASIS THEN REWRITE_TAC[DIMINDEX_3; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                    (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `basis 1:real^3`; `basis 2:real^3`] RFA_FRAME3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `w1:real^3`
    STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_scalar] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (lhs(concl th)))) THEN
  SUBGOAL_THEN `abs(mfd_sectional atlas (g:A->real^3^3) x u1 v1) <= sqrt H /\
                abs(mfd_sectional atlas g x u1 w1) <= sqrt H /\
                abs(mfd_sectional atlas g x v1 w1) <= sqrt H` MP_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC);;

let RFA_HC2_RMD0_FROM_RM = prove
 (`?H0. &1 <= H0 /\
     !top atlas (g:A->real^3^3) x.
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
       mfd_rm_norm atlas g x <= &1
       ==> rfa_rmd2 0 atlas g x <= H0`,
  MP_TAC(INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lsb"))) THEN
  EXISTS_TAC `max (&1) C0` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * &1 pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[rfa_rmd2] THEN USE_THEN "lsb" MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM mfd_sectional] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_rm_norm atlas (g:A->real^3^3) x` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_NORM THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

let RFA_HC2_EARLY = prove
 (`?Tst eps1. &0 < Tst /\ &0 < eps1 /\
     !C eps hf md g0 A0 rp dl (hs:(A)rfs_history) t x.
       p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ &0 < eps /\ eps <= eps1 /\
       &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
       inv(eps pow 2) <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x
       ==> Tst <= t`,
  X_CHOOSE_THEN `H0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h0"))
    (INST_TYPE [`:A`,`:A`] RFA_HC2_RMD0_FROM_RM) THEN
  X_CHOOSE_THEN `Cp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dbl"))
    (INST_TYPE [`:A`,`:A`; `:3`,`:N`] RFA_RMD2_DOUBLING) THEN
  SUBGOAL_THEN `&0 < sqrt H0 /\ sqrt(&4 * H0) = &2 * sqrt H0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SQRT_MUL] THEN SUBGOAL_THEN `sqrt(&4) = &2` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(Cp * sqrt H0)`; `inv(sqrt(&12 * sqrt H0 + &1))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_LT_MUL];
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 0 = &0 /\
                (!k. k <= hs_count hs ==> hs_time hs k < hs_time hs (k + 1)) /\
                hausdorff_space (hs_top hs 0) /\
                smooth_manifold_atlas (hs_top hs 0) (hs_atlas hs 0) /\
                compact_space (hs_top hs 0) /\
                ricci_flow_from (hs_top hs 0,hs_atlas hs 0) (&0) (hs_time hs 1) (hs_metric hs 0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_from")) (concl th))) THEN
    ASM_REWRITE_TAC[LE_0; ADD_CLAUSES] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas hs 0) (hs_metric (hs:(A)rfs_history) 0 (&0))`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
  (* doubling on slab 0 *)
  USE_THEN "dbl" (MP_TAC o SPECL [`hs_top (hs:(A)rfs_history) 0`; `hs_atlas (hs:(A)rfs_history) 0`;
    `&0`; `hs_time (hs:(A)rfs_history) 1`; `hs_metric (hs:(A)rfs_history) 0`; `H0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "h0" MATCH_MP_TAC THEN
    EXISTS_TAC `hs_top (hs:(A)rfs_history) 0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_normalized (hs_top hs 0,hs_atlas hs 0) (hs_metric (hs:(A)rfs_history) 0 (&0))` THEN
    REWRITE_TAC[rfs_normalized] THEN ASM_MESON_TAC[];
    REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(LABEL_TAC "four")] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < inv(Cp * sqrt H0) ==> Cp * sqrt H0 * s <= &1`
  (LABEL_TAC "time") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < Cp * sqrt H0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Cp * sqrt H0) * inv(Cp * sqrt H0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the first event is after Tst *)
  SUBGOAL_THEN `rfs_slab (hs:(A)rfs_history) t = 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `k = 0 <=> ~(1 <= k)`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 1 <= t` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) (rfs_slab hs t)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_slab_maximal")) (concl th))) THEN
    ASM_REWRITE_TAC[rfs_slab_maximal; ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o SPEC `&2 * sqrt H0`) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
    USE_THEN "four" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "time" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) 0`; `hs_atlas (hs:(A)rfs_history) 0`;
                   `hs_metric (hs:(A)rfs_history) 0 s`; `y:A`; `&4 * H0`] RFA_HC2_RMD0_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ricci_flow_from (hs_top hs 0,hs_atlas hs 0) (&0) (hs_time hs 1)
                     (hs_metric (hs:(A)rfs_history) 0)` THEN
      REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
      ASM_CASES_TAC `s = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* R at (x,t) is small *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `t:real`] APX_RFS_SLAB) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_0] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `rfs_top_at (hs:(A)rfs_history) t = hs_top hs 0`;
                              ASSUME `rfs_atlas_at (hs:(A)rfs_history) t = hs_atlas hs 0`;
                              ASSUME `rfs_metric_at (hs:(A)rfs_history) t = hs_metric hs 0 t`]) THEN
  USE_THEN "four" (MP_TAC o SPECL [`t:real`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "time" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) 0`; `hs_atlas (hs:(A)rfs_history) 0`;
                 `hs_metric (hs:(A)rfs_history) 0 t`; `x:A`; `&4 * H0`] RFA_HC2_RMD0_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ricci_flow_from (hs_top hs 0,hs_atlas hs 0) (&0) (hs_time hs 1)
                   (hs_metric (hs:(A)rfs_history) 0)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(sqrt(&12 * sqrt H0 + &1)) pow 2 = inv(&12 * sqrt H0 + &1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_INV] THEN AP_TERM_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&12 * sqrt H0 + &1 <= inv(eps pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(inv(sqrt(&12 * sqrt H0 + &1)) pow 2)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Regions.  A regular view gives the setting of Part 2A (p2a_svs, and       *)
(* p2a_region for persisting sets); on a region over (tt - tau/q, tt] made   *)
(* of the ball of radius r1 >= 4 r / sqrt q about y, abs Rm <= K q gives     *)
(* abs(nabla^l Rm)^2 <= Cl q^(l+2) at (y,tt): RFA_C2_SHI_SCALED on the       *)
(* region flow p2c_vfam (the pattern of P2AP_GRAD_AT, at the top time).      *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_VIEW_ACCESSORS = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2a_vtop V = rfs_vtop V /\ p2a_vatlas V = rfs_vatlas V /\ p2a_vmetric V = rfs_vmetric V`,
  REWRITE_TAC[FORALL_PAIR_THM; p2a_vtop; p2a_vatlas; p2a_vmetric; rfs_vtop; rfs_vatlas;
              rfs_vmetric]);;

let RFA_HC2_REGULAR_SVS = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2c_regular_view V ==> p2a_svs V`,
  GEN_TAC THEN REWRITE_TAC[p2c_regular_view; p2a_svs; RFA_HC2_VIEW_ACCESSORS] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN X_GEN_TAC `t:real` THEN
  ASM_CASES_TAC `topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) t) = {}` THEN
  ASM_SIMP_TAC[HAUSDORFF_SPACE_TOPSPACE_EMPTY]);;

let RFA_HC2_REGULAR_REGION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b ==> p2a_region V W a b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2a_region; P2AP_RMETRIC_VFAM; P2A_FLOW_UPTO_3; RFA_HC2_VIEW_ACCESSORS] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W a b` THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    SPEC_TAC(`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`,`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; p2a_persists; rfs_vtop; rfs_vatlas];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o el 3 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
                  P2C_REGULAR_VFLOW) THEN
    ASM_REWRITE_TAC[p2c_vflow] THEN SIMP_TAC[]]);;

let RFA_HC2_REGION_SHI = prove
 (`!l K r tau. &0 < K /\ &0 < r /\ &0 < tau
     ==> ?Cl. &0 < Cl /\
           !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3)) tt y q r1.
             p2a_svs V /\ y IN topspace(rfs_vtop V tt) /\ &0 < q /\
             &4 * r / sqrt q <= r1 /\
             p2a_region V (rfs_vball V tt y r1) (tt - tau / q) tt /\
             compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt y r1)) /\
             (!s z. tt - tau / q < s /\ s <= tt /\ z IN rfs_vball V tt y r1
                    ==> p3_vrm V s z <= K * q)
             ==> p3_vderiv2 V l tt y <= Cl * q pow (l + 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:num`; `K:real`; `r:real`; `tau:real`]
               (INST_TYPE [`:A`,`:A`] RFA_C2_SHI_SCALED)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shi"))) THEN
  EXISTS_TAC `Cl:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `tt:real`; `y:A`; `q:real`; `r1:real`] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `y:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt q /\ &0 < r / sqrt q /\ &0 < r1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt q` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&4 * r / sqrt q` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `W = mfd_ball (rfs_vtop V tt,rfs_vatlas V tt)
                           (rfs_vmetric (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
                           y r1` THEN
  SUBGOAL_THEN
   `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) tt) W /\
    W SUBSET topspace(rfs_vtop V tt) /\ (y:A) IN W`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) tt) W`
    ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN EXPAND_TAC "W" THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `tt - tau / q`; `tt:real`]
                P2AP_REGION_UPTO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `tt - tau / q`; `tt:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W tt`; `tt:real`] P2AP_UPTO_RIEM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> t - x < t`) THEN ASM_SIMP_TAC[REAL_LT_DIV];
    STRIP_TAC] THEN
  SUBGOAL_THEN `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) W tt tt =
                restrict_metric (rfs_vatlas V tt) W (rfs_vmetric V tt)`
  ASSUME_TAC THENL [REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace(subtopology (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W) = W`
  ASSUME_TAC THENL [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* compactness of the closure of the Shi ball *)
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) tt`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) tt`;
                 `y:A`; `r1:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W tt tt`;
                 `y:A`; `r / sqrt q`; `&1`] P2AP_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_LE_REFL] THEN
     CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `riemannian_metric
                   (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W)
                   (p2c_vfam V W tt tt)` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  (* Shi *)
  USE_THEN "shi" (MP_TAC o SPECL
   [`subtopology (rfs_vtop (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
    `restrict_atlas (rfs_vatlas (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
    `tt - tau / q`; `tt:real`;
    `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) W tt`; `y:A`; `q:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `t - (t - x) = x`] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W tt tt`; `y:A`; `r / sqrt q`]
                    P2AP_BALL_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) t z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AP_VFAM_RM_NORM_LE THEN EXISTS_TAC `tt - tau / q` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt tt`; `y:A`; `(r / &2) / sqrt q`]
                  MFD_CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `tt - tau / q`; `tt:real`; `tt:real`;
                 `l:num`; `y:A`] P2AP_VFAM_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> t - x < t`) THEN ASM_SIMP_TAC[REAL_LT_DIV];
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The persisting case of R13.  y in U with the deep ball                    *)
(* B = B(y,t,1/(2 sqrt(C R(x)))) inside U and its half B(y,t,1/(4 sqrt(C    *)
(* R(x)))) persisting over                                                   *)
(* (t - tau0/R(x), t], tau0 = 1/(32 C max(C,2)): R <= 2 C R(x) on B at t     *)
(* (RFA_C2_RATIO), R <= 4 C R(x) on the region (RFA_HC2_HIST_BACK; the       *)
(* window starts after 0 by RFA_HC2_EARLY), abs Rm <= (8 C + 12 + 2 e^4)     *)
(* R(x) by pinching, and RFA_HC2_REGION_SHI gives abs(nabla^l Rm)^2 <=       *)
(* Cl R(x)^(l+2) at (y,t).                                                   *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_SLICE_FACTS = prove
 (`!(hs:(A)rfs_history) t.
     rfs_history_ok hs /\ &0 <= t /\ t < rfs_horizon hs
     ==> hausdorff_space (rfs_top_at hs t) /\
         smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t) /\
         compact_space (rfs_top_at hs t) /\
         riemannian_metric (rfs_atlas_at hs t) (rfs_metric_at hs t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) t` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t:real`] APX_RFS_SLAB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ricci_flow_from (hs_top hs k,hs_atlas hs k) (hs_time hs k)
                 (hs_time hs (k + 1)) (hs_metric (hs:(A)rfs_history) k)` THEN
  REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = hs_time (hs:(A)rfs_history) k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RFA_HC2_PERSIST_RMD = prove
 (`?eps1. &0 < eps1 /\
     !C. &1 < C
       ==> !l. ?Cl. &0 < Cl /\
             !eps hf md g0 A0 rp dl (hs:(A)rfs_history) t x U y.
               P2C_HISTORY_REGULAR_STATEMENT (:A) /\ &0 < eps /\ eps <= eps1 /\
               p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ rp t <= eps /\
               rfs_canonical_assumption (rfs_trunc (rfs_view hs) t) C eps rp /\
               &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
               inv(rp t pow 2) <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x /\
               rfs_canonical_nbhd (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t)
                                  C eps x U /\
               y IN U /\
               mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) y
                 (inv(&2 * sqrt(C * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)))
               SUBSET U /\
               rfs_persists (rfs_view hs)
                 (mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) y
                   (inv(&4 * sqrt(C * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))))
                 (t - inv(&32 * C * max C (&2)) /
                      mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x) t
               ==> rfa_rmd2 l (rfs_atlas_at hs t) (rfs_metric_at hs t) y <=
                   Cl * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x pow (l + 2)`,
  X_CHOOSE_THEN `Tst:real` (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "early")))) (INST_TYPE [`:A`,`:A`] RFA_HC2_EARLY) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "back"))
    (INST_TYPE [`:A`,`:A`] RFA_HC2_HIST_BACK) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ratio"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_RATIO) THEN
  EXISTS_TAC `min (min (&1 / &2) (sqrt Tst)) (min e1 (min e2 e3))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `C:real` THEN DISCH_TAC THEN X_GEN_TAC `l:num` THEN
  ABBREV_TAC `C2 = max C (&2)` THEN
  SUBGOAL_THEN `&1 < C2 /\ C <= C2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `tau0 = inv(&32 * C * C2)` THEN
  ABBREV_TAC `K = &8 * C + &12 + &2 * exp(&4)` THEN
  SUBGOAL_THEN `&0 < tau0 /\ &0 < K /\ &0 < inv(&16 * sqrt C) /\ tau0 <= &1 / &64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tau0"; "K"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&32 * &1 * &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`l:num`; `K:real`; `inv(&16 * sqrt C)`; `tau0:real`]
               (INST_TYPE [`:A`,`:A`] RFA_HC2_REGION_SHI)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rshi"))) THEN
  EXISTS_TAC `Cl:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                       `hs:(A)rfs_history`; `t:real`; `x:A`; `U:A->bool`; `y:A`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (:A)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!s. &0 <= s ==> &0 < (rp:real->real) s) /\
                (!s t. &0 <= s /\ s <= t ==> (rp:real->real) t <= rp s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rp:real->real) t` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &2 /\ eps <= sqrt Tst /\ eps <= e1 /\ eps <= e2 /\ eps <= e3`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFA_HC2_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the ratio bound on U *)
  USE_THEN "ratio" (MP_TAC o SPECL [`rfs_top_at (hs:(A)rfs_history) t`;
    `rfs_atlas_at (hs:(A)rfs_history) t`; `rfs_metric_at (hs:(A)rfs_history) t`; `C:real`;
    `eps:real`; `x:A`; `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `q = mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at (hs:(A)rfs_history) t) x` THEN
  ABBREV_TAC `W = mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t)
                           (rfs_metric_at (hs:(A)rfs_history) t) y (inv(&4 * sqrt(C * q)))` THEN
  (* q >= eps^-2 >= 4 *)
  SUBGOAL_THEN `inv(eps pow 2) <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((rp:real->real) t pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= inv(eps pow 2) /\ eps pow 2 <= Tst` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((&1 / &2) pow 2)` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt Tst pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= q /\ &0 < q` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* early times *)
  SUBGOAL_THEN `Tst <= t` ASSUME_TAC THENL
   [USE_THEN "early" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                          `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                          `hs:(A)rfs_history`; `x:A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `tau0 / q <= t /\ &0 < tau0 / q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_DIV]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tau0 * eps pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(eps pow 2))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * Tst` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* R <= 2 C q on W at t, R <= 4 C q on the region *)
  SUBGOAL_THEN `(W:A->bool) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t)
                  (rfs_metric_at (hs:(A)rfs_history) t) y (inv(&2 * sqrt(C * q)))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN MATCH_MP_TAC RFA_MFD_BALL_MONO THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `&0 < sqrt(C * q)` MP_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s w. t - tau0 / q < s /\ s <= t /\ (w:A) IN W
          ==> rfs_vscalar (rfs_view (hs:(A)rfs_history)) s w <= &2 * (&2 * C * q)`
  (LABEL_TAC "rbound") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "back" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `rp:real->real`; `t:real`; `W:A->bool`;
                          `t - tau0 / q`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[rfs_vscalar; rfs_view] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `U:A->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th))) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * q <= &2 * C * q ==> q <= &2 * C * q`) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - (t - x) = x`] THEN EXPAND_TAC "tau0" THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&1 < C` THEN
      UNDISCH_TAC `&1 < C2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* abs Rm <= K q on the region *)
  SUBGOAL_THEN
   `!s w. t - tau0 / q < s /\ s <= t /\ (w:A) IN W
          ==> p3_vrm (rfs_view (hs:(A)rfs_history)) s w <= K * q`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s /\ s < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFA_HC2_SLICE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:A) IN topspace(rfs_top_at hs s)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W (t - tau0 / q) t` THEN
      REWRITE_TAC[rfs_persists; rfs_view] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `rfs_pinched_at (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) s w`
    ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
      REWRITE_TAC[rfs_pinched; rfs_view] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`;
                   `rfs_metric_at (hs:(A)rfs_history) s`; `s:real`; `w:A`] RFA_PINCH_RM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REMOVE_THEN "rbound" (MP_TAC o SPECL [`s:real`; `w:A`]) THEN
    ASM_REWRITE_TAC[rfs_vscalar; rfs_view] THEN DISCH_TAC THEN
    SUBGOAL_THEN `-- &6 <= mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) w`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(&6) / (&4 * s + &1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_LE_NEG2] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
        UNDISCH_TAC `rfs_pinched_at (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) s w` THEN
        SIMP_TAC[rfs_pinched_at]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&12 + &2 * exp(&4)) * &1 <= (&12 + &2 * exp(&4)) * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p3_vrm; rfs_view; rfs_vatlas; rfs_vmetric] THEN EXPAND_TAC "K" THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Shi on the region *)
  SUBGOAL_THEN `&0 < sqrt C /\ &0 < sqrt q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "rshi" (MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `y:A`; `q:real`;
                                   `inv(&4 * sqrt(C * q))`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[rfs_view; rfs_vtop; rfs_vball] THEN REWRITE_TAC[GSYM rfs_view] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_HC2_REGULAR_SVS THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SQRT_MUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < sqrt C` THEN UNDISCH_TAC `&0 < sqrt q` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC RFA_HC2_REGULAR_REGION THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[p3_vderiv2; rfs_view; rfs_vatlas; rfs_vmetric; rfa_rmd2]]);;

