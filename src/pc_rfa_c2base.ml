(* ========================================================================= *)
(* Unit pc_rfa_c2base: common facts for the Part 3 obligations R13           *)
(* (P3_HIST_C2_BOUND_STATEMENT) and R14 (P3_STD_C2_BOUND_STATEMENT) of       *)
(* pc_p3_route: Shi's interior estimate (RFA_P2_THM_3_28) in scale-invariant *)
(* form for every order l; nonnegative sectional curvature gives pinching    *)
(* and abs Rm <= 2 R + 2 exp 4 (RFA_PINCH_RM); on a (C,eps)-canonical        *)
(* neighbourhood U of x the scalar curvature is at most 2 C R(x) (necks by   *)
(* closeness, caps by the ratio clause, C-components by the curvature        *)
(* pinching, round components by closeness); the normalized form of the      *)
(* conclusion of R13 and R14.                                                *)
(* ========================================================================= *)

needs "src/pc_rfa_pinchrm.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_rfa_shi329.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_rfa_sec.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Shi's interior estimate in scale-invariant form for every                 *)
(* order l: RFA_P2_THM_3_28 at (l,K,r,tau) for the parabolically rescaled   *)
(* flow q g(t / q).  If abs Rm <= K q on B(x,b,r / sqrt q) over (a,b] and   *)
(* q (b - a) >= tau, then abs(nabla^l Rm)^2 <= Cl q^(l+2) on the half ball. *)
(* ------------------------------------------------------------------------- *)

let RFA_C2_SHI_SCALED = prove
 (`!l K r tau.
     &0 < K /\ &0 < r /\ &0 < tau
     ==> ?Cl. &0 < Cl /\
              !top atlas a b g x q.
                hausdorff_space top /\
                rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
                &0 < q /\ tau <= q * (b - a) /\ x IN topspace top /\
                compact_in top (top closure_of mfd_ball (top,atlas) (g b) x (r / sqrt q)) /\
                (!t y. a < t /\ t <= b /\ y IN mfd_ball (top,atlas) (g b) x (r / sqrt q)
                       ==> mfd_rm_norm atlas (g t) y <= K * q)
                ==> !y. y IN mfd_ball (top,atlas) (g b) x ((r / &2) / sqrt q)
                        ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas y) (g b))
                                              (SND(chart_at atlas y) y)
                            <= Cl * q pow (l + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(:A)` RFA_P2_THM_3_28) THEN REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `K:real`; `r:real`; `tau:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `max C1 (&1)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `x:A`; `q:real`] THEN
  STRIP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q * b) / q = b` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!rr. mfd_ball (top,atlas) (\z. q %% (g:real->A->real^3^3) b z) x rr =
                     mfd_ball (top,atlas) (g b) x (rr / sqrt q)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) b`; `q:real`; `x:A`; `rr:real`] MFD_BALL_SCALE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `q * a:real`; `q * b:real`;
    `\t x. q %% (g:real->A->real^3^3) (t / q) x`; `x:A`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_RFS_FLOW_UPTO_RESCALE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM REAL_SUB_LDISTRIB];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `a < t / q /\ t / q <= b` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) b) x (r / sqrt q)` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `K = (K * q) / q` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) b) x ((r / &2) / sqrt q)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`]
         CHART_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                    ((g:real->A->real^3^3) b)`;
                 `q:real`; `l:num`; `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`]
         RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) b)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  SPEC_TAC(`lrm_deriv_norm2 l
              (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                 ((g:real->A->real^3^3) b))
              (SND(chart_at atlas y) y)`,`D:real`) THEN
  GEN_TAC THEN
  SUBGOAL_THEN `&0 < q pow (l + 2)` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN SPEC_TAC(`q pow (l + 2)`,`p:real`) THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * p:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `D = p * (inv p * D) /\ p * (inv p * D) <= p * C1 ==> D <= C1 * p`) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Nonnegative sectional curvature at x gives R(x) >= 0, a                   *)
(* nonnegative least sectional curvature, pinching at every time t >= 0     *)
(* and abs Rm <= 2 R + 2 exp 4 (RFA_PINCH_RM).                              *)
(* ------------------------------------------------------------------------- *)

let RFA_C2_NONNEG_PINCHED = prove
 (`!top atlas (g:A->real^3^3) t x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 <= t /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> &0 <= mfd_scalar atlas g x /\ &0 <= mfd_sec_min atlas g x /\
         rfs_pinched_at atlas g t x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nn"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3, basis 1, basis 2}` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_NONCOLLINEAR_BASIS THEN REWRITE_TAC[DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
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
    SUBGOAL_THEN `&0 <= mfd_sectional atlas (g:A->real^3^3) x u1 v1 /\
                  &0 <= mfd_sectional atlas g x u1 w1 /\
                  &0 <= mfd_sectional atlas g x v1 w1` MP_TAC THENL
     [REPEAT CONJ_TAC THEN USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_sec_min atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_sec_min] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `mfd_sectional atlas (g:A->real^3^3) x (basis 1) (basis 2)` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_pinched_at] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= t ==> &0 < &4 * t + &1`] THEN
    REAL_ARITH_TAC;
    DISCH_TAC THEN ASM_REAL_ARITH_TAC]);;

let RFA_C2_NONNEG_RM = prove
 (`!top atlas (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> mfd_rm_norm atlas g x <= &2 * mfd_scalar atlas g x + &2 * exp(&4)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `&0`; `x:A`] RFA_C2_NONNEG_PINCHED) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `&0`; `x:A`] RFA_PINCH_RM) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= r ==> abs r = r`]);;


(* ------------------------------------------------------------------------- *)
(* On a (C,eps)-canonical neighbourhood U of x the scalar                    *)
(* curvature is at most 2 C R(x) (R(x) > 0, U in the space).  Necks: R(e y) *)
(* <= 3/2 R(x) by closeness (APX_NECK_CURV); caps: the ratio clause;        *)
(* C-components: R(x) >= 6 d > 6 sup R / C with d the lower bound of the     *)
(* sectional curvatures (RFA_FRAME3); round components q g close to g1 of    *)
(* curvature 1: abs(R / q - 6) <= K1 eps (APX_SCALAR_STABILITY_LIP).        *)
(* ------------------------------------------------------------------------- *)

let RFA_C2_RATIO_NECK = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x e y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN IMAGE e (rfs_neck_dom eps)
        ==> mfd_scalar atlas g y <= &3 / &2 * mfd_scalar atlas g x`,
  MP_TAC(ISPEC `(:A)` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:A`] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `w:real^3`] APX_NECK_SCALAR_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `w:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    SIMP_TAC[]]);;

let RFA_C2_RATIO_CAP = prove
 (`!top atlas (g:A->real^3^3) C eps U Y x.
        rfs_cap (top,atlas) g C eps U Y /\ x IN Y
        ==> &0 < mfd_scalar atlas g x /\ U SUBSET topspace top /\
            !y. y IN U ==> mfd_scalar atlas g y <= C * mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_cap]) THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN Y` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET U` THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`] SUBSET_BALL) THEN
      REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN SET_TAC[];
      ALL_TAC];
    SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN Y` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4)) SUBSET U` THEN
      SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET (annulus (&1 / &4) (&4):real^3->bool)`
      MP_TAC THENL
       [REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SET_TAC[];
      ALL_TAC]] THEN
  (REPEAT CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) y / mfd_scalar atlas g x <= C` MP_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o check (fun th ->
         can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_sup_lt")) (concl th) &&
         not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist_in"))
                  (concl th)) &&
         not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_grad2"))
                  (concl th)) &&
         not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_lap"))
                  (concl th)))) THEN
       REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
       DISCH_THEN(X_CHOOSE_THEN `dq:real` (CONJUNCTS_THEN2 ASSUME_TAC
         (MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) y / mfd_scalar atlas g x`))) THEN
       ANTS_TAC THENL
        [MAP_EVERY EXISTS_TAC [`y:A`; `x:A`] THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
       ASM_SIMP_TAC[REAL_LE_LDIV_EQ]]]));;

let RFA_C2_RATIO_CCOMP = prove
 (`!top atlas (g:A->real^3^3) C U x.
        &0 < C /\ riemannian_metric atlas g /\
        rfs_c_component (top,atlas) g C U /\ x IN U
        ==> &0 < mfd_scalar atlas g x /\ U SUBSET topspace top /\
            !y. y IN U ==> mfd_scalar atlas g y <= C / &6 * mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_c_component] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?b. !r. r IN IMAGE (mfd_scalar atlas (g:A->real^3^3)) U ==> r <= b`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `euclideanreal`;
                   `mfd_scalar atlas (g:A->real^3^3)`; `U:A->bool`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded] THEN
    MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_inf_gt")) (concl th))) THEN
  REWRITE_TAC[rfs_inf_gt; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  SUBGOAL_THEN `&6 * d0 <= mfd_scalar atlas (g:A->real^3^3) x /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
           CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                          (FST(chart_at atlas x))`;
                   `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                      (g:A->real^3^3)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                   `basis 1:real^3`; `basis 2:real^3`] RFA_FRAME3) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFA_NONCOLLINEAR_BASIS THEN REWRITE_TAC[DIMINDEX_3; ARITH]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `w1:real^3`
      STRIP_ASSUME_TAC))) THEN
    REWRITE_TAC[mfd_scalar] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (lhs(concl th)))) THEN
    SUBGOAL_THEN `d0 <= mfd_sectional atlas (g:A->real^3^3) x u1 v1 /\
                  d0 <= mfd_sectional atlas g x u1 w1 /\
                  d0 <= mfd_sectional atlas g x v1 w1` MP_TAC THENL
     [REPEAT CONJ_TAC THEN USE_THEN "lb" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:A`] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_sectional atlas (g:A->real^3^3) x u1 v1 /\
                  &0 < mfd_sectional atlas g x u1 w1 /\
                  &0 < mfd_sectional atlas g x v1 w1` MP_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> mfd_scalar atlas (g:A->real^3^3) y <=
                                sup(IMAGE (mfd_scalar atlas g) U)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) y < C * d0` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv C * mfd_scalar atlas (g:A->real^3^3) y < d0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `inv C * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) y =
                  C * (inv C * mfd_scalar atlas g y)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C / &6 * (&6 * d0) <= C / &6 * mfd_scalar atlas (g:A->real^3^3) x`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) y < C * d0` THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Round components.  With q g eps-close to g1 of sectional                  *)
(* curvature 1 on W (rfs_mclose in the preferred charts), abs(R / q - 6)    *)
(* <= K1 eps on W: in the chart at x, abs Rm(g1) is bounded                 *)
(* (RFA_LRM_SECTIONAL_BOUND), lscalar g1 = 6 (RFA_FRAME3) and the scalar    *)
(* curvature is Lipschitz in the C^2 distance (APX_SCALAR_STABILITY_LIP).   *)
(* ------------------------------------------------------------------------- *)

let RFA_C2_ROUND_SCALAR_Q = prove
 (`?K1. &0 < K1 /\
     !top atlas (g:A->real^3^3) eps W q g1.
       &0 < eps /\ eps <= &1 / &10 /\ riemannian_metric atlas g /\
       smooth_manifold_atlas top atlas /\ W IN connected_components_of top /\
       &0 < q /\ riemannian_metric atlas g1 /\
       (!x u v. x IN W /\ ~collinear {vec 0,u,v}
                ==> mfd_sectional atlas g1 x u v = &1) /\
       rfs_mclose (rfs_kreg eps) eps atlas W g1 (\x. q %% g x)
       ==> !x. x IN W ==> abs(mfd_scalar atlas g x / q - &6) <= K1 * eps`,
  MP_TAC(INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lsb"))) THEN
  EXISTS_TAC `&72 * (&1 + sqrt C0)` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `C0:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_mclose] THEN STRIP_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) x =
                lscalar (metric_local atlas (chart_at atlas x) g) (SND(chart_at atlas x) x)`
  SUBST1_TAC THENL [REWRITE_TAC[mfd_scalar]; ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `yc = SND (c:(A->bool)#(A->real^3)) x` THEN
  ABBREV_TAC `S = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `(yc:real^3) IN S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["yc"; "S"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas c (g1:A->real^3^3)) /\
                metric_field S (metric_local atlas c (g:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas c (\x. q %% (g:A->real^3^3) x) =
                (\z. q %% metric_local atlas c g z)`
  SUBST_ALL_TAC THENL [REWRITE_TAC[METRIC_LOCAL_CMUL]; ALL_TAC] THEN
  ABBREV_TAC `G1 = metric_local atlas c (g1:A->real^3^3)` THEN
  ABBREV_TAC `Gg = metric_local atlas c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field S (\z. q %% (Gg:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v} ==> lsectional (G1:real^3->real^3^3) yc u v = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `u:real^3`; `v:real^3`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional"))
          (concl th))) THEN
    ASM_REWRITE_TAC[mfd_sectional];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 0 (G1:real^3->real^3^3) yc <= sqrt C0 pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2] THEN
    USE_THEN "lsb" (MP_TAC o SPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`;
                                    `&1`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_ABS_NUM; REAL_LE_REFL]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) < eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg eps) (G1:real^3->real^3^3) (\z. q %% Gg z) yc` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN
      ASM_SIMP_TAC[SQRT_MONO_LT_EQ; POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt C0`; `S:real^3->bool`; `G1:real^3->real^3^3`;
                 `\z. q %% (Gg:real^3->real^3^3) z`; `yc:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (G1:real^3->real^3^3) yc = &6` SUBST1_TAC THENL
   [SUBGOAL_THEN `~collinear {vec 0:real^3, basis 1, basis 2}` ASSUME_TAC THENL
     [MATCH_MP_TAC RFA_NONCOLLINEAR_BASIS THEN REWRITE_TAC[DIMINDEX_3; ARITH]; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`;
                   `basis 1:real^3`; `basis 2:real^3`] RFA_FRAME3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `w1:real^3`
      STRIP_ASSUME_TAC))) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Gg:real^3->real^3^3`; `q:real`; `yc:real^3`]
                LSCALAR_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(&1 + sqrt C0) * sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) <=
                (&1 + sqrt C0) * eps` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN MP_TAC(SPEC `C0:real` SQRT_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sqrt C0) = sqrt C0` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3; REAL_ARITH `&3 pow 2 = &9`] THEN REAL_ARITH_TAC);;

let RFA_C2_ROUND_SCALAR = prove
 (`?K1. &0 < K1 /\
     !top atlas (g:A->real^3^3) eps W.
       &0 < eps /\ eps <= &1 / &10 /\ riemannian_metric atlas g /\
       rfs_round_component (top,atlas) g eps W
       ==> ?q. &0 < q /\
               !x. x IN W ==> abs(mfd_scalar atlas g x / q - &6) <= K1 * eps`,
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rq"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_ROUND_SCALAR_Q) THEN
  EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_round_component] THEN STRIP_TAC THEN
  EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "rq" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `g1:A->real^3^3`] THEN ASM_REWRITE_TAC[]);;

let RFA_C2_RATIO_ROUND = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps U x.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_round_component (top,atlas) g eps U /\ x IN U
        ==> &0 < mfd_scalar atlas g x /\ U SUBSET topspace top /\
            !y. y IN U ==> mfd_scalar atlas g y <= &2 * mfd_scalar atlas g x`,
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rs"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_ROUND_SCALAR) THEN
  EXISTS_TAC `min (&1 / &10) (inv K1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN
    ASM_SIMP_TAC[REAL_LT_INV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ K1 * eps <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `eps <= inv K1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM real_div; REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN DISCH_TAC THEN
    SUBGOAL_THEN `K1 * eps <= K1 * inv K1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REMOVE_THEN "rs" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `U:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z. z IN U ==> &5 * q <= mfd_scalar atlas (g:A->real^3^3) z /\
                              mfd_scalar atlas g z <= &7 * q`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(mfd_scalar atlas (g:A->real^3^3) z / q - &6) <= &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_ARITH
     `abs(a - &6) <= &1 <=> &5 <= a /\ a <= &7`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN
    ASM_MESON_TAC[rfs_round_component];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:A` th) THEN MP_TAC(SPEC `y:A` th)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The ratio bound for all four kinds of (C,eps)-canonical                   *)
(* neighbourhoods, and the normalized form of the C^2 conclusion: a bound   *)
(* K R(x)^(l+2) for abs(nabla^l Rm)^2 of g at y is a bound K for the metric *)
(* R(x) g (RFA_LRM_DERIV_NORM2_SCALE).                                      *)
(* ------------------------------------------------------------------------- *)

let RFA_C2_RATIO = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) C eps x U.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        &1 < C /\ &0 < eps /\ eps <= eps1 /\
        rfs_canonical_nbhd (top,atlas) g C eps x U
        ==> &0 < mfd_scalar atlas g x /\ U SUBSET topspace top /\
            !y. y IN U ==> mfd_scalar atlas g y <= &2 * C * mfd_scalar atlas g x`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_RATIO_NECK) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rd"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_RATIO_ROUND) THEN
  EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rfs_canonical_nbhd] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
      REWRITE_TAC[rfs_neck; mfd_param; mfd_diffeo] THEN STRIP_TAC THEN
      MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &2 * mfd_scalar atlas (g:A->real^3^3) x` THEN CONJ_TAC THENL
     [REMOVE_THEN "nk" MATCH_MP_TAC THEN EXISTS_TAC `top:A topology` THEN
      EXISTS_TAC `eps:real` THEN EXISTS_TAC `e:real^3->A` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`] RFA_C2_RATIO_CAP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * mfd_scalar atlas (g:A->real^3^3) x` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `U:A->bool`; `x:A`] RFA_C2_RATIO_CCOMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C / &6 * mfd_scalar atlas (g:A->real^3^3) x` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    REMOVE_THEN "rd" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * mfd_scalar atlas (g:A->real^3^3) x` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC]);;

let RFA_C2_NORMALIZE = prove
 (`!top atlas (g:A->real^3^3) x y l K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ &0 < mfd_scalar atlas g x /\
     lrm_deriv_norm2 l (metric_local atlas (chart_at atlas y) g) (SND(chart_at atlas y) y)
     <= K * mfd_scalar atlas g x pow (l + 2)
     ==> lrm_deriv_norm2 l
           (metric_local atlas (chart_at atlas y) (\z. mfd_scalar atlas g x %% g z))
           (SND(chart_at atlas y) y) <= K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                    (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `l:num`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`]
         RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `lrm_deriv_norm2 l
                 (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                    (g:A->real^3^3))
                 (SND(chart_at atlas y) y) <= K * mfd_scalar atlas g x pow (l + 2)` THEN
  SPEC_TAC(`lrm_deriv_norm2 l
              (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                 (g:A->real^3^3))
              (SND(chart_at atlas y) y)`,`D:real`) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x pow (l + 2)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN
  SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) x pow (l + 2)`,`p:real`) THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `inv p * D <= inv p * (K * p) /\ inv p * (K * p) = K
                           ==> inv p * D <= K`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
    UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD]);;

