(* ========================================================================= *)
(* Unit pc_p2b_p946g: the soliton flow G(t) = abs t phi_t^* g of             *)
(* pc_p2b_p946f satisfies the hypotheses of X2s.  The map phi_t (flow of     *)
(* grad f / abs t from time -1) is an isometry onto (M, g) from              *)
(* (M, phi_t^* g) (P2BX46_SOL_ISOM), so R, sec, |Rm|, completeness and       *)
(* noncollapsing of G(t) come from those of g with the scale abs t           *)
(* (P2BX46_SOL_SCALAR, _SECT_POS, _RM_NORM, _COMPLETE, _NONCOLL, _KNC).      *)
(* dR/dt >= 0 by direct computation: R(G t)(x) = R(g)(phi_t x) / abs t and   *)
(* d/dt R(g)(phi_t x) = 2 Ric(grad f, grad f) / abs t >= 0 by (9.21)         *)
(* (P2BX46_SOL_DR_POS).                                                      *)
(* ========================================================================= *)

needs "src/pc_p2b_p946f.ml";;
needs "src/pc_mfd_transport.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_p2a_flow.ml";;
needs "src/pc_p2b_chainstmts.ml";;
needs "src/pc_p2b_shrinkcl.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The flow maps of the soliton flow, the isometry to g, and                 *)
(* derivatives of functions along flow lines.                               *)
(* ========================================================================= *)

(* The hypotheses under which pc_p2b_p946f builds the soliton flow. *)

let p2bx46_hyp = new_definition
 `p2bx46_hyp (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (f:A->real) (K:real) <=>
    hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
    mfd_complete (top,atlas) g /\ &0 <= K /\
    (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
    (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
    (!y w. y IN topspace top
           ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w)))`;;

(* The flow maps from time -1 to time t and back. *)

let p2bx46_phi = new_definition
 `p2bx46_phi (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (f:A->real) (t:real) =
    mfl_flow top atlas (p2bx46_solX atlas g f) (lift(--(&1))) (lift t)`;;

let p2bx46_psi = new_definition
 `p2bx46_psi (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (f:A->real) (t:real) =
    mfl_flow top atlas (p2bx46_solX atlas g f) (lift t) (lift(--(&1)))`;;

let P2BX46_G_PHI = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f t.
     p2bx46_G top atlas g f t =
     (\x. abs t %% mfd_pullback_metric atlas atlas (p2bx46_phi top atlas g f t) g x)`,
  REWRITE_TAC[p2bx46_G; p2bx46_phi]);;

let P2BX46_HYP_MCF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K.
     p2bx46_hyp top atlas g f K
     ==> mcf_hyp top atlas (p2bx46_solX atlas g f) {t:real^1 | drop t < &0} f /\
         smooth_manifold_atlas top atlas /\ riemannian_metric atlas g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx46_hyp; p2bx46_solX] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_MCF_HYP THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[p2b_shrinker]]);;

(* The flow maps are inverse diffeomorphisms of the whole manifold. *)

let P2BX46_SOL_FLOW = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t.
     p2bx46_hyp top atlas g f K /\ t < &0
     ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
           (p2bx46_phi top atlas g f t) (p2bx46_psi top atlas g f t) /\
         mfd_diffeo top atlas (topspace top) top atlas (topspace top)
           (p2bx46_psi top atlas g f t) (p2bx46_phi top atlas g f t) /\
         (!x. x IN topspace top
              ==> p2bx46_phi top atlas g f t x IN topspace top /\
                  p2bx46_psi top atlas g f t x IN topspace top /\
                  p2bx46_phi top atlas g f t (p2bx46_psi top atlas g f t x) = x /\
                  p2bx46_psi top atlas g f t (p2bx46_phi top atlas g f t x) = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2BX46_HYP_MCF) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MCF_FLOW_GEN) THEN
  SUBGOAL_THEN `lift(--(&1)) IN {t:real^1 | drop t < &0} /\ lift t IN {t:real^1 | drop t < &0}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in") (CONJUNCTS_THEN2 (LABEL_TAC "refl")
    (CONJUNCTS_THEN2 (LABEL_TAC "coc") (CONJUNCTS_THEN2 (LABEL_TAC "dif") ASSUME_TAC)))) THEN
  REWRITE_TAC[p2bx46_phi; p2bx46_psi] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "dif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "dif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "in" (MP_TAC o SPECL [`lift(--(&1))`; `lift t`; `x:A`]) THEN
      ASM_SIMP_TAC[];
      USE_THEN "in" (MP_TAC o SPECL [`lift t`; `lift(--(&1))`; `x:A`]) THEN
      ASM_SIMP_TAC[];
      USE_THEN "coc" (MP_TAC o SPECL [`lift t`; `lift(--(&1))`; `lift t`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "refl" (MP_TAC o SPECL [`lift t`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
      USE_THEN "coc" (MP_TAC o SPECL [`lift(--(&1))`; `lift t`; `lift(--(&1))`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "refl" (MP_TAC o SPECL [`lift(--(&1))`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]]]);;

(* phi_t is an isometry from (M, phi_t^* g) onto (M, g); its inverse psi_t  *)
(* is one from (M, g) onto (M, phi_t^* g).                                  *)

let P2BX46_SOL_ISOM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t.
     p2bx46_hyp top atlas g f K /\ t < &0
     ==> riemannian_metric atlas
           (mfd_pullback_metric atlas atlas (p2bx46_phi top atlas g f t) g) /\
         mfd_isometry (top,atlas) g
           (top,atlas) (mfd_pullback_metric atlas atlas (p2bx46_phi top atlas g f t) g)
           (p2bx46_psi top atlas g f t) (p2bx46_phi top atlas g f t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MTR_PULLBACK_ISOMETRY THEN ASM_REWRITE_TAC[]);;

let P2BX46_SOL_RIEM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t.
     p2bx46_hyp top atlas g f K /\ t < &0
     ==> riemannian_metric atlas (p2bx46_G top atlas g f t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2BX46_G_PHI] THEN
  MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_ISOM) THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* Flow lines stay in a chart for nearby times. *)

let P2BX46_FLOW_NBHD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) c s t x.
     mcf_hyp top atlas X J Fe /\ c IN atlas /\ s IN J /\ t IN J /\ x IN topspace top /\
     mfl_flow top atlas X s t x IN FST c
     ==> ?d. &0 < d /\
             !r. dist(r,t) < d ==> r IN J /\ mfl_flow top atlas X s r x IN FST c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mcf_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                 `c:(A->bool)#(A->real^N)`; `s:real^1`] MCF_JOINT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC
    `pastecart (t:real^1) (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x)`) THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
  SUBGOAL_THEN
   `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
              (SND(chart_at atlas x) x) = x`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[SUBSET] THEN
  DISCH_TAC THEN X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `pastecart (r:real^1) (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x)`) THEN
  REWRITE_TAC[IN_BALL; DIST_PASTECART_CANCEL; IN_ELIM_PASTECART_THM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
              (SND(chart_at atlas x) x) = x`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* The derivative of a function along a flow line, through any chart       *)
(* representation H of the function.                                        *)

let P2BX46_FLOW_CHART_FDERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real)
    (F0:A->real) (H:real^N->real) c s t x.
     mcf_hyp top atlas X J Fe /\ c IN atlas /\ s IN J /\ t IN J /\ x IN topspace top /\
     mfl_flow top atlas X s t x IN FST c /\
     (!z. z IN FST c ==> F0 z = H(SND c z)) /\
     (\y. lift(H y)) differentiable at (SND c (mfl_flow top atlas X s t x))
     ==> ((\r. lift(F0(mfl_flow top atlas X s r x))) has_vector_derivative
          frechet_derivative (\y. lift(H y)) (at (SND c (mfl_flow top atlas X s t x)))
            (mfd_vrep atlas (X (drop t)) c (SND c (mfl_flow top atlas X s t x)))) (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `c:(A->bool)#(A->real^N)`; `s:real^1`; `t:real^1`; `x:A`]
    MCF_FLOW_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `c:(A->bool)#(A->real^N)`; `s:real^1`; `t:real^1`; `x:A`]
    P2BX46_FLOW_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `(\y. lift((H:real^N->real) y)) o
              (\r. SND (c:(A->bool)#(A->real^N))
                     (mfl_flow top atlas (X:real->A->real^N) s r x))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    MP_TAC(ISPECL
     [`\r. SND (c:(A->bool)#(A->real^N)) (mfl_flow top atlas (X:real->A->real^N) s r x)`;
      `\y. lift((H:real^N->real) y)`;
      `mfd_vrep atlas ((X:real->A->real^N) (drop t)) c
         (SND (c:(A->bool)#(A->real^N)) (mfl_flow top atlas X s t x))`;
      `t:real^1`; `(:real^1)`] MCF_VDERIV_CHAIN_WITHIN) THEN
    ASM_REWRITE_TAC[WITHIN_UNIV]]);;

(* ========================================================================= *)
(* Curvature, completeness and noncollapsing of G(t) =                       *)
(* abs t phi_t^* g, from those of g at phi_t x.                             *)
(* ========================================================================= *)

let P2BX46_SOL_SCALAR = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top
     ==> mfd_scalar atlas (p2bx46_G top atlas g f t) x =
         mfd_scalar atlas g (p2bx46_phi top atlas g f t x) / abs t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_ISOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BX46_G_PHI] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas
                    (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t) g`;
                 `abs t`; `x:A`] P2AU_MFD_SCALAR_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_pullback_metric atlas atlas
                    (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t) g`;
                 `p2bx46_psi (top:A topology) atlas (g:A->real^N^N) f t`;
                 `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t`;
                 `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x`]
    MFD_ISOMETRY_SCALAR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[]);;

let P2BX46_SOL_SECT_POS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v}
            ==> &0 < mfd_sectional atlas g (p2bx46_phi top atlas g f t x) u v)
     ==> !u v. ~collinear {vec 0,u,v}
               ==> &0 < mfd_sectional atlas (p2bx46_G top atlas g f t) x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_ISOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas
                    (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t) g`;
                 `p2bx46_psi (top:A topology) atlas (g:A->real^N^N) f t`;
                 `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t`;
                 `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x`;
                 `\s:real. s`] MTR_ISOMETRY_SECTIONAL_SET) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bx46_psi (top:A topology) atlas (g:A->real^N^N) f t
      (p2bx46_phi top atlas g f t x) = x`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[P2BX46_G_PHI] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas
                    (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t) g`;
                 `abs t`; `x:A`; `u:real^N`; `v:real^N`] RFA_MFD_SECTIONAL_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `mfd_sectional atlas
      (mfd_pullback_metric atlas atlas
         (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t) g) x u v`) THEN
  MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u':real^N` (X_CHOOSE_THEN `v':real^N` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[]]);;

let P2BX46_SOL_RM_NORM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x B.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top /\ 2 <= dimindex(:N) /\
     mfd_rm_norm atlas g (p2bx46_phi top atlas g f t x) <= B
     ==> mfd_rm_norm atlas (p2bx46_G top atlas g f t) x <= B / abs t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_ISOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BX46_G_PHI] THEN MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas
                    (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t) g`;
                 `p2bx46_psi (top:A topology) atlas (g:A->real^N^N) f t`;
                 `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t`;
                 `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x`]
    MTR_ISOMETRY_RM_NORM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bx46_psi (top:A topology) atlas (g:A->real^N^N) f t
      (p2bx46_phi top atlas g f t x) = x`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

(* Isometries preserve closed balls, completeness and noncollapsing. *)

let P2BX46_ISOMETRY_CBALL = prove
 (`!(top:A topology) atlas (g:A->real^N^N) (top':B topology) atlas' g' f f' x r.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
     ==> mfd_cball (top',atlas') g' (f x) r = IMAGE f (mfd_cball (top,atlas) g x r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`] MFD_DIST_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_cball; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top'` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `(f':B->A) y IN topspace top` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(f':B->A) y` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `(f':B->A) y`]) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:A->B) ((f':B->A) y) = y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `z:A`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_MESON_TAC[]]);;

let P2BX46_ISOMETRY_COMPLETE = prove
 (`!(top:A topology) atlas (g:A->real^N^N) (top':B topology) atlas' g' f f'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ mfd_complete (top,atlas) g
     ==> mfd_complete (top',atlas') g'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  REWRITE_TAC[mfd_complete] THEN MAP_EVERY X_GEN_TAC [`y:B`; `r:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f':B->A) y IN topspace top /\ (f:A->B)(f' y) = y` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_cball (top',atlas') (g':B->real^N^N) y r =
    IMAGE (f:A->B) (mfd_cball (top,atlas) (g:A->real^N^N) ((f':B->A) y) r)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                   `f:A->B`; `f':B->A`; `(f':B->A) y`; `r:real`] P2BX46_ISOMETRY_CBALL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN REWRITE_TAC[mfd_complete] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `continuous_map (subtopology top (topspace top),top') (f:A->B)` THEN
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]]);;

let P2BX46_NONCOLL_ISOMETRY = prove
 (`!kappa (top:A topology) atlas (g:A->real^N^N) (top':B topology) atlas' g' f f'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
     p2b_rm_noncoll kappa (top,atlas) g
     ==> p2b_rm_noncoll kappa (top',atlas') g'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  REWRITE_TAC[p2b_rm_noncoll] THEN DISCH_THEN(LABEL_TAC "nc") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  MAP_EVERY X_GEN_TAC [`p:B`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb"))) THEN
  SUBGOAL_THEN `(f':B->A) p IN topspace top /\ (f:A->B)(f' p) = p` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top',atlas') (g':B->real^N^N) p r =
    IMAGE (f:A->B) (mfd_ball (top,atlas) (g:A->real^N^N) ((f':B->A) p) r)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                   `f:A->B`; `f':B->A`; `(f':B->A) p`; `r:real`] MTR_ISOMETRY_BALL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) (g:A->real^N^N) ((f':B->A) p) r SUBSET topspace top`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  REMOVE_THEN "nc" (MP_TAC o SPECL [`(f':B->A) p`; `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                   `f:A->B`; `f':B->A`; `y:A`] MTR_ISOMETRY_RM_NORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    USE_THEN "rb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `v:real` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`;
                 `mfd_ball (top,atlas) (g:A->real^N^N) ((f':B->A) p) r`; `v:real`]
    MFD_HAS_VOLUME_ISOMETRY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P2BX46_SOL_COMPLETE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t.
     p2bx46_hyp top atlas g f K /\ t < &0
     ==> mfd_complete (top,atlas) (p2bx46_G top atlas g f t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) (g:A->real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bx46_hyp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_ISOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BX46_G_PHI] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas
                    (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t) g`;
                 `abs t`] MFD_COMPLETE_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2BX46_ISOMETRY_COMPLETE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`;
                        `p2bx46_psi (top:A topology) atlas (g:A->real^N^N) f t`;
                        `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t`] THEN
  ASM_REWRITE_TAC[]);;

let P2BX46_SOL_NONCOLL = prove
 (`!kappa top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K t.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ p2b_rm_noncoll kappa (top,atlas) g
     ==> p2b_rm_noncoll kappa (top,atlas) (p2bx46_G top atlas g f t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_ISOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BX46_G_PHI] THEN MATCH_MP_TAC P2BSK_NONCOLL_SCALE THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2BX46_NONCOLL_ISOMETRY THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`;
                        `p2bx46_psi (top:A topology) atlas (g:A->real^3^3) f t`;
                        `p2bx46_phi (top:A topology) atlas (g:A->real^3^3) f t`] THEN
  ASM_REWRITE_TAC[]);;

(* Flow-level kappa-noncollapsing on all scales from the slices. *)

let P2BX46_SOL_KNC = prove
 (`!kappa top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K r0.
     p2bx46_hyp top atlas g f K /\ p2b_rm_noncoll kappa (top,atlas) g
     ==> rfs_kappa_noncollapsed
           (rfs_flow_view (top,atlas) {s | s < &0} (p2bx46_G top atlas g f)) kappa r0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_vball; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `r:real`] THEN
  ASM_CASES_TAC `t < &0` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb"))))) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_NONCOLL) THEN
  ASM_REWRITE_TAC[p2b_rm_noncoll; DIMINDEX_3] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `r:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  USE_THEN "rb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> t - a < t`) THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* R and f along the flow lines, and dR/dt >= 0 for G.                       *)
(* For t < 0, R(G t)(x) = R(g)(phi_t x) / abs t, and d/dt R(g)(phi_t x) =   *)
(* 2 Ric(grad f, grad f) / abs t by (9.21) in a chart (P2BX46_DR_GRAD).     *)
(* ========================================================================= *)

let P2BX46_PHI_REFL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K x.
     p2bx46_hyp top atlas g f K /\ x IN topspace top
     ==> p2bx46_phi top atlas g f (--(&1)) x = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx46_phi] THEN
  MATCH_MP_TAC MCF_FLOW_REFL THEN
  MAP_EVERY EXISTS_TAC [`{t:real^1 | drop t < &0}`; `f:A->real`] THEN
  ASM_SIMP_TAC[P2BX46_HYP_MCF; IN_ELIM_THM; LIFT_DROP] THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[P2BX46_HYP_MCF]; ALL_TAC]) THEN REAL_ARITH_TAC);;

let P2BX46_SOL_SCALAR_M1 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K x.
     p2bx46_hyp top atlas g f K /\ x IN topspace top
     ==> mfd_scalar atlas (p2bx46_G top atlas g f (--(&1))) x = mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `--(&1)`; `x:A`] P2BX46_SOL_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `x:A`] P2BX46_PHI_REFL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_DIV_1]);;

(* The derivative of a function along phi_s x, through a representation H *)
(* in the chart at phi_t x.                                                 *)

let P2BX46_SOL_FDERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x (F0:A->real) H.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top /\
     (!w. w IN FST(chart_at atlas (p2bx46_phi top atlas g f t x))
          ==> F0 w = H(SND(chart_at atlas (p2bx46_phi top atlas g f t x)) w)) /\
     (\y. lift(H y)) differentiable
       at (SND(chart_at atlas (p2bx46_phi top atlas g f t x)) (p2bx46_phi top atlas g f t x))
     ==> ((\s. F0(p2bx46_phi top atlas g f s x)) has_real_derivative
          (inv(abs t) *
           drop(frechet_derivative (\y. lift(H y))
                 (at (SND(chart_at atlas (p2bx46_phi top atlas g f t x))
                        (p2bx46_phi top atlas g f t x)))
                 (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f t x))))) (atreal t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx46_phi] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `lift(--(&1)) IN {t:real^1 | drop t < &0} /\ lift t IN {t:real^1 | drop t < &0}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfl_flow top atlas (p2bx46_solX atlas (g:A->real^N^N) f) (lift(--(&1))) (lift t) x IN
    topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `p2bx46_solX atlas (g:A->real^N^N) f`; `{t:real^1 | drop t < &0}`;
                   `f:A->real`] MCF_FLOW_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift(--(&1))`; `lift t`; `x:A`] o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `z = mfl_flow top atlas (p2bx46_solX atlas (g:A->real^N^N) f) (lift(--(&1))) (lift t) x` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2bx46_solX atlas (g:A->real^N^N) f`; `{t:real^1 | drop t < &0}`;
                 `f:A->real`; `F0:A->real`; `H:real^N->real`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`;
                 `lift(--(&1))`; `lift t`; `x:A`] P2BX46_FLOW_CHART_FDERIV) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `mfd_vrep atlas (p2bx46_solX atlas (g:A->real^N^N) f t)
      (chart_at atlas (z:A)) (SND(chart_at atlas z) z) =
    inv(abs t) % p2bx46_gradf atlas g f z`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `p2bx46_solX atlas (g:A->real^N^N) f t`; `z:A`] MCF_VREP_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2bx46_solX];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]) THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_DROP]);;

(* d/ds R(g)(phi_s x) = 2 Ric(grad f, grad f) / abs s. *)

let P2BX46_SOL_RDERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top
     ==> ((\s. mfd_scalar atlas g (p2bx46_phi top atlas g f s x)) has_real_derivative
          (&2 * inv(abs t) *
           mfd_ricci atlas g (p2bx46_phi top atlas g f t x)
             (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f t x))
             (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f t x)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `p2b_shrinker (top,atlas) (g:A->real^N^N) f` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bx46_hyp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z = p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x` THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`]
    RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`; `x:A`; `mfd_scalar atlas (g:A->real^N^N)`;
                 `lscalar (metric_local atlas (chart_at atlas (z:A)) (g:A->real^N^N))`]
    P2BX46_SOL_FDERIV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`;
                     `w:A`] RFA_SH_QR_CHART) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                        (FST(chart_at atlas z))` THEN
      ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH; FUN_IN_IMAGE]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                        (FST(chart_at atlas z))`;
                 `metric_local atlas (chart_at atlas (z:A)) (g:A->real^N^N)`;
                 `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                       (z:A)) y)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) z`;
                 `p2bx46_gradf atlas (g:A->real^N^N) f z`] P2BX46_DR_GRAD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mfd_ricci] THEN
  SUBGOAL_THEN
   `matrix_inv(metric_local atlas (chart_at atlas (z:A)) (g:A->real^N^N)
                 (SND(chart_at atlas z) z)) **
    (lambda a. rfa_d1 (\y. (f:A->real)(chart_inv (chart_at atlas z) y))
                      (SND(chart_at atlas z) z) (basis a)) =
    p2bx46_gradf atlas g f z`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2bx46_gradf; p3s_cgrad; P3S_JAC_ROW1; rfa_d1]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* d/ds f(phi_s x) = |grad f|^2 / abs s. *)

let P2BX46_SOL_FFDERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top
     ==> ((\s. f(p2bx46_phi top atlas g f s x)) has_real_derivative
          (inv(abs t) *
           lgrad2 (metric_local atlas (chart_at atlas (p2bx46_phi top atlas g f t x)) g)
                  (\y. f(chart_inv (chart_at atlas (p2bx46_phi top atlas g f t x)) y))
                  (SND(chart_at atlas (p2bx46_phi top atlas g f t x))
                      (p2bx46_phi top atlas g f t x)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `p2b_shrinker (top,atlas) (g:A->real^N^N) f` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bx46_hyp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z = p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x` THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`]
    RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`; `x:A`; `f:A->real`;
                 `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                       (z:A)) y)`]
    P2BX46_SOL_FDERIV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `w:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                        (FST(chart_at atlas z))` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM rfa_d1; GSYM P2BX46_CDF_RFA_D1; p2bx46_gradf] THEN
  MATCH_MP_TAC P2BX46_CDF_CGRAD THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                    (FST(chart_at atlas z))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* A real lemma: if Rs(s) = h(s) / abs s on s < 0 with h, h' >= 0, then     *)
(* every derivative of Rs at t < 0 is >= 0.                                 *)

let P2BX46_DR_SIGN = prove
 (`!(h:real->real) h' (Rs:real->real) t dR.
     t < &0 /\ (h has_real_derivative h') (atreal t) /\ &0 <= h t /\ &0 <= h' /\
     (!s. s < &0 ==> Rs s = h s / abs s) /\ (Rs has_real_derivative dR) (atreal t)
     ==> &0 <= dR`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\s. inv(--s)) has_real_derivative (--(--(&1)) / (--t) pow 2)) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s:real. --s`; `--(&1)`; `t:real`] HAS_REAL_DERIVATIVE_INV_ATREAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->real`; `h':real`; `\s:real. inv(--s)`;
                 `--(--(&1)) / (--t) pow 2`; `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((Rs:real->real) has_real_derivative
     ((h:real->real) t * (--(--(&1)) / (--t) pow 2) + h' * inv(--t))) (atreal t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s. (h:real->real) s * inv(--s)`; `--t:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[real_div; REAL_ARITH `s < &0 ==> abs s = --s`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dR = (h:real->real) t * (--(--(&1)) / (--t) pow 2) + h' * inv(--t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`Rs:real->real`; `t:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]);;

(* The class condition dR/dt >= 0 for G. *)

let P2BX46_SOL_DR_POS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x dR.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top /\
     ((\s. mfd_scalar atlas (p2bx46_G top atlas g f s) x) has_real_derivative dR)
       (atreal t)
     ==> &0 <= dR`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x IN topspace top`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BX46_DR_SIGN THEN
  MAP_EVERY EXISTS_TAC
   [`\s. mfd_scalar atlas (g:A->real^N^N) (p2bx46_phi top atlas g f s x)`;
    `&2 * inv(abs t) *
     mfd_ricci atlas (g:A->real^N^N) (p2bx46_phi top atlas g f t x)
       (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f t x))
       (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f t x))`;
    `\s. mfd_scalar atlas (p2bx46_G top atlas (g:A->real^N^N) f s) x`; `t:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_RDERIV THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[p2bx46_hyp];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ASM_MESON_TAC[p2bx46_hyp]];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BX46_SOL_SCALAR THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* G is in the class p2b_ancflow on t < 0, with the curvature                *)
(* hypotheses of X2s (|Rm(G t)| <= C0 / abs t and sec(G t) > 0).           *)
(* ========================================================================= *)

let P2BX46_SOL_SECT_POS_ALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x u v.
     p2bx46_hyp top atlas g f K /\ t < &0 /\ x IN topspace top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     ~collinear {vec 0,u,v}
     ==> &0 < mfd_sectional atlas (p2bx46_G top atlas g f t) x u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `t:real`; `x:A`] P2BX46_SOL_SECT_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BX46_SOL_ANCFLOW0 = prove
 (`!kappa top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) f K.
     p2bx46_hyp top atlas g f K /\ &0 < kappa /\ ~(topspace top = {}) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     p2b_rm_noncoll kappa (top,atlas) g
     ==> p2b_ancflow0 kappa (top,atlas) (p2bx46_G top atlas g f) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  REWRITE_TAC[p2b_ancflow0] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX46_SOL_RICCI_FLOW THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX46_SOL_COMPLETE THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC P2BX46_SOL_SECT_POS_ALL THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:B` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~collinear {vec 0:real^3, basis 1, basis 2}` ASSUME_TAC THENL
     [MATCH_MP_TAC RFA_NONCOLLINEAR_BASIS THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(mfd_sectional atlas (p2bx46_G top atlas (g:B->real^3^3) f s) x
                      (basis 1) (basis 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < a ==> &0 < abs a`) THEN
      MATCH_MP_TAC P2BX46_SOL_SECT_POS_ALL THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX46_SOL_RIEM THEN
      EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] P2BX46_SOL_DR_POS) THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `f:B->real`; `K:real`; `s:real`; `x:B`] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2BX46_SOL_KNC THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[]]);;

(* All the hypotheses that X2s puts on the flow, for the soliton flow. *)

let P2BX46_SOL_X2S_HYPS = prove
 (`!kappa top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) f K C0.
     p2bx46_hyp top atlas g f K /\ &0 < kappa /\ ~compact_space top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= C0) /\
     p2b_rm_noncoll kappa (top,atlas) g /\ p2b_ksep top atlas
     ==> p2b_ancflow kappa (top,atlas) (p2bx46_G top atlas g f) (&0) /\
         (!t x. t < &0 /\ x IN topspace top
                ==> mfd_rm_norm atlas (p2bx46_G top atlas g f t) x <= C0 / abs t) /\
         (!t x u v. t < &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 < mfd_sectional atlas (p2bx46_G top atlas g f t) x u v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2b_ancflow] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX46_SOL_ANCFLOW0 THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPACT_SPACE_TOPSPACE_EMPTY];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_SOL_RM_NORM THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `f:B->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_SOL_SECT_POS_ALL THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Points pp k for X2s.  A general lemma: if R is bounded                    *)
(* above and outside every compact set there are points with R >= r0 > 0,  *)
(* then L = the limsup of R at infinity is positive and is the limit of R   *)
(* along points leaving every compact set (exhaustion by the compact        *)
(* sublevel sets of a proper continuous F0).                                 *)
(* ========================================================================= *)

let P2BX46_CONT_COMPACT_BOUND = prove
 (`!top (h:A->real) S.
     continuous_map (top,euclideanreal) h /\ compact_in top S
     ==> ?B. !x. x IN S ==> h x <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (h:A->real) S` REAL_COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
    MESON_TAC[REAL_ARITH `abs x <= B ==> x <= B`]]);;

(* The sup of R off S. *)

let P2BX46_TAIL_SUP = prove
 (`!top (R:A->real) Rmax r0 S.
     (!x. x IN topspace top ==> R x <= Rmax) /\
     (?y. y IN topspace top /\ ~(y IN S) /\ r0 <= R y)
     ==> (!x. x IN topspace top /\ ~(x IN S)
              ==> R x <= sup {R x | x IN topspace top /\ ~(x IN S)}) /\
         r0 <= sup {R x | x IN topspace top /\ ~(x IN S)} /\
         (!e. &0 < e
              ==> ?x. x IN topspace top /\ ~(x IN S) /\
                      sup {R x | x IN topspace top /\ ~(x IN S)} - e < R x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `{(R:A->real) x | x IN topspace top /\ ~(x IN S)}` SUP) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`(R:A->real) y`; `y:A`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `Rmax:real` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = sup {(R:A->real) x | x IN topspace top /\ ~(x IN S)}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ub" ACCEPT_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(R:A->real) y` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "lub" (MP_TAC o SPEC `s0 - e:real`) THEN
    MATCH_MP_TAC(TAUT `(~p ==> q) /\ ~r ==> (q ==> r) ==> p`) THEN CONJ_TAC THENL
     [MESON_TAC[REAL_NOT_LT]; ASM_REAL_ARITH_TAC]]);;

let P2BX46_LIMSUP_POINTS = prove
 (`!top (R:A->real) (F0:A->real) Rmax r0.
     continuous_map (top,euclideanreal) F0 /\
     (!c. compact_in top {x | x IN topspace top /\ F0 x <= c}) /\
     (!x. x IN topspace top ==> R x <= Rmax) /\ &0 < r0 /\
     (!S. compact_in top S ==> ?y. y IN topspace top /\ ~(y IN S) /\ r0 <= R y)
     ==> ?pp. (!k. pp k IN topspace top) /\
              (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\
              (?L. &0 < L /\ ((\k. R(pp k)) ---> L) sequentially /\
                   (!e. &0 < e
                        ==> ?S. compact_in top S /\
                                !x. x IN topspace top /\ ~(x IN S) ==> R x <= L + e))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "prop")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "esc"))))) THEN
  ABBREV_TAC `sig = \S. sup {(R:A->real) x | x IN topspace top /\ ~(x IN S)}` THEN
  SUBGOAL_THEN
   `!S. compact_in top S
        ==> (!x. x IN topspace top /\ ~(x IN S) ==> (R:A->real) x <= sig S) /\
            r0 <= sig S /\
            (!e. &0 < e
                 ==> ?x. x IN topspace top /\ ~(x IN S) /\ sig S - e < R x)`
  (LABEL_TAC "sig") THENL
   [X_GEN_TAC `S:A->bool` THEN DISCH_TAC THEN EXPAND_TAC "sig" THEN
    MATCH_MP_TAC P2BX46_TAIL_SUP THEN EXISTS_TAC `Rmax:real` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "esc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{(sig:(A->bool)->real) S | S | compact_in top S}` INF) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`(sig:(A->bool)->real) {}`; `{}:A->bool`] THEN
      REWRITE_TAC[COMPACT_IN_EMPTY];
      EXISTS_TAC `r0:real` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `L = inf {(sig:(A->bool)->real) S | S | compact_in top S}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lb") (LABEL_TAC "glb")) THEN
  SUBGOAL_THEN `r0 <= L` ASSUME_TAC THENL
   [USE_THEN "glb" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> ?S. compact_in top S /\ (sig:(A->bool)->real) S < L + e`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "glb" (MP_TAC o SPEC `L + e:real`) THEN
    MATCH_MP_TAC(TAUT `(~p ==> q) /\ ~r ==> (q ==> r) ==> p`) THEN CONJ_TAC THENL
     [MESON_TAC[REAL_NOT_LT]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?y. y IN topspace top /\ &k < (F0:A->real) y /\ L - inv(&k + &1) < (R:A->real) y`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    ABBREV_TAC `T0 = {x | x IN topspace top /\ (F0:A->real) x <= &k}` THEN
    SUBGOAL_THEN `compact_in top (T0:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "T0" THEN USE_THEN "prop" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    USE_THEN "sig" (MP_TAC o SPEC `T0:A->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&k + &1)` o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    EXPAND_TAC "T0" THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `L <= (sig:(A->bool)->real) T0` MP_TAC THENL
     [USE_THEN "lb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:num->A` (LABEL_TAC "pp")) THEN
  SUBGOAL_THEN `!S. compact_in top S ==> ?N. !k. N <= k ==> ~((pp:num->A) k IN S)`
  (LABEL_TAC "leave") THENL
   [X_GEN_TAC `S:A->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `F0:A->real`; `S:A->bool`] P2BX46_CONT_COMPACT_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "bd")) THEN
    MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    DISCH_TAC THEN USE_THEN "bd" (MP_TAC o SPEC `(pp:num->A) k`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "pp" (MP_TAC o SPEC `k:num`) THEN
    SUBGOAL_THEN `&N <= &k` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `pp:num->A` THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "leave" ACCEPT_TAC; ALL_TAC] THEN
  EXISTS_TAC `L:real` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "near" (MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "leave" (MP_TAC o SPEC `S:A->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "n1" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "pp" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "sig" (MP_TAC o SPEC `S:A->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(pp:num->A) k` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `inv(&k + &1) < e` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "near" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:A->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    USE_THEN "sig" (MP_TAC o SPEC `S:A->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* R and f are nondecreasing along the forward flow lines, f                 *)
(* grows at least like -log|t| once |grad f| >= 1, so far flow lines leave  *)
(* every compact set with R >= R(x0) > 0: the limsup of R at infinity is    *)
(* positive, and the points pp of X2s exist (P2BX46_SOL_POINTS).            *)
(* ========================================================================= *)

let P2BX46_F_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f.
     p2b_shrinker (top,atlas) g f ==> continuous_map (top,euclideanreal) f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift((f:A->real) x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\x:A. lift((f:A->real) x)`] MFD_SMOOTH_ON_TOPSPACE) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\x:A. lift((f:A->real) x)`] GRGE_MFD_SMOOTH_CONTINUOUS) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EQ_DROP; o_DEF; LIFT_DROP; ETA_AX]);;

(* Real lemmas: monotonicity on t < 0, and logarithmic growth. *)

let P2BX46_MONO_NEG = prove
 (`!(h:real->real) h' a b.
     (!s. s < &0 ==> (h has_real_derivative h' s) (atreal s) /\ &0 <= h' s) /\
     a <= b /\ b < &0
     ==> h a <= h b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real->real`; `h':real->real`; `{s:real | s < &0}`; `a:real`; `b:real`]
    HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BX46_LOG_GROWTH = prove
 (`!(u:real->real) u' t.
     (!s. --(&1) <= s /\ s < &0
          ==> (u has_real_derivative u' s) (atreal s) /\ inv(--s) <= u' s) /\
     --(&1) <= t /\ t < &0
     ==> u(--(&1)) - log(--t) <= u t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s < &0 ==> ((\s. log(--s)) has_real_derivative (--(&1) * inv(--s))) (atreal s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. (u:real->real) s + log(--s)`;
                 `\s. (u':real->real) s + --(&1) * inv(--s)`;
                 `{s:real | --(&1) <= s /\ s < &0}`; `--(&1)`; `t:real`]
    HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> &0 <= b + --(&1) * a`) THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_NEG_NEG; LOG_1] THEN REAL_ARITH_TAC]);;

(* R(g) and f are nondecreasing along phi_s x on s < 0. *)

let P2BX46_SOL_R_MONO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K x a b.
     p2bx46_hyp top atlas g f K /\ x IN topspace top /\ a <= b /\ b < &0
     ==> mfd_scalar atlas g (p2bx46_phi top atlas g f a x) <=
         mfd_scalar atlas g (p2bx46_phi top atlas g f b x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s. mfd_scalar atlas (g:A->real^N^N) (p2bx46_phi top atlas g f s x)`;
    `\s. &2 * inv(abs s) *
         mfd_ricci atlas (g:A->real^N^N) (p2bx46_phi top atlas g f s x)
           (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f s x))
           (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f s x))`;
    `a:real`; `b:real`] P2BX46_MONO_NEG) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_RDERIV THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f s x IN topspace top`
    MP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `K:real`; `s:real`] P2BX46_SOL_FLOW) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[p2bx46_hyp]]]);;

let P2BX46_SOL_F_MONO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K x a b.
     p2bx46_hyp top atlas g f K /\ x IN topspace top /\ a <= b /\ b < &0
     ==> f(p2bx46_phi top atlas g f a x) <= f(p2bx46_phi top atlas g f b x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  MP_TAC(ISPECL
   [`\s. (f:A->real) (p2bx46_phi top atlas (g:A->real^N^N) f s x)`;
    `\s. inv(abs s) *
         lgrad2 (metric_local atlas (chart_at atlas (p2bx46_phi top atlas g f s x)) g)
                (\y. (f:A->real)(chart_inv (chart_at atlas (p2bx46_phi top atlas g f s x)) y))
                (SND(chart_at atlas (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f s x))
                    (p2bx46_phi top atlas g f s x))`;
    `a:real`; `b:real`] P2BX46_MONO_NEG) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_FFDERIV THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2BX46_GRAD2_POS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `K:real`; `s:real`] P2BX46_SOL_FLOW) THEN
    ASM_SIMP_TAC[]]);;

(* Far flow lines escape: once R + |grad f|^2 - f = C, R <= Rmax and       *)
(* f(x0) >= Rmax - C + 1, f(phi_t x0) >= f(x0) - log|t| on [-1,0).          *)

let P2BX46_SOL_ESCAPE_LINE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K C Rmax x0.
     p2bx46_hyp top atlas g f K /\ x0 IN topspace top /\
     (!x. x IN topspace top
          ==> mfd_scalar atlas g x +
              lgrad2 (metric_local atlas (chart_at atlas x) g)
                     (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) -
              f x = C) /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x <= Rmax) /\
     Rmax - C + &1 <= f x0
     ==> !M. ?t. --(&1) <= t /\ t < &0 /\ M < f(p2bx46_phi top atlas g f t x0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ham") (CONJUNCTS_THEN2 (LABEL_TAC "rmax") ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN
   `!t. --(&1) <= t /\ t < &0
        ==> f x0 - log(--t) <= (f:A->real)(p2bx46_phi top atlas (g:A->real^N^N) f t x0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\s. (f:A->real) (p2bx46_phi top atlas (g:A->real^N^N) f s x0)`;
      `\s. inv(abs s) *
           lgrad2 (metric_local atlas (chart_at atlas (p2bx46_phi top atlas g f s x0)) g)
                  (\y. (f:A->real)(chart_inv (chart_at atlas (p2bx46_phi top atlas g f s x0)) y))
                  (SND(chart_at atlas (p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f s x0))
                      (p2bx46_phi top atlas g f s x0))`;
      `t:real`] P2BX46_LOG_GROWTH) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BX46_SOL_FFDERIV THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC `z = p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f s x0` THEN
      SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
       [EXPAND_TAC "z" THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `f:A->real`; `K:real`; `s:real`] P2BX46_SOL_FLOW) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:A->real) x0 <= f z` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `f:A->real`; `K:real`; `x0:A`; `--(&1)`; `s:real`]
          P2BX46_SOL_F_MONO) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `f:A->real`; `K:real`; `x0:A`] P2BX46_PHI_REFL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "ham" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "rmax" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `abs s = --s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `K:real`; `x0:A`] P2BX46_PHI_REFL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `M:real` THEN
  ABBREV_TAC `T0 = abs(M - (f:A->real) x0) + &1` THEN
  EXISTS_TAC `--exp(--T0)` THEN
  SUBGOAL_THEN `&0 < exp(--T0) /\ exp(--T0) < &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    EXPAND_TAC "T0" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--exp(--T0)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_NEG; LOG_EXP] THEN EXPAND_TAC "T0" THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The points of X2s for the soliton flow.                                   *)
(* ========================================================================= *)

let P2BX46_SOL_POINTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K Rmax.
     p2bx46_hyp top atlas g f K /\ ~compact_space top /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x <= Rmax) /\
     (!x. x IN topspace top ==> &0 < mfd_scalar atlas g x)
     ==> ?pp. (!k. pp k IN topspace top) /\
              (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\
              (?L. &0 < L /\
                   ((\k. mfd_scalar atlas (p2bx46_G top atlas g f (--(&1))) (pp k)) ---> L)
                   sequentially /\
                   (!e. &0 < e
                        ==> ?S. compact_in top S /\
                                !x. x IN topspace top /\ ~(x IN S)
                                    ==> mfd_scalar atlas (p2bx46_G top atlas g f (--(&1))) x
                                        <= L + e))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rmax") (LABEL_TAC "rpos")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (f:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_F_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. compact_in top {x:A | x IN topspace top /\ f x <= c}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `K:real`] P2BX46_F_PROPER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`] P2BX46_MFD_HAMILTON_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "ham")) THEN
  SUBGOAL_THEN `?x0:A. x0 IN topspace top /\ Rmax - C + &1 <= f x0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~compact_space (top:A topology)` THEN REWRITE_TAC[compact_space] THEN
    SUBGOAL_THEN
     `topspace top = {x:A | x IN topspace top /\ f x <= Rmax - C + &1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_NOT_LE; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `mfd_scalar atlas (g:A->real^N^N)`; `f:A->real`;
                 `Rmax:real`; `mfd_scalar atlas (g:A->real^N^N) x0`] P2BX46_LIMSUP_POINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `S:A->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `f:A->real`; `S:A->bool`] P2BX46_CONT_COMPACT_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "bd")) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `K:real`; `C:real`; `Rmax:real`; `x0:A`]
      P2BX46_SOL_ESCAPE_LINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "ham" ACCEPT_TAC; USE_THEN "rmax" ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC o SPEC `B:real`) THEN
    EXISTS_TAC `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x0` THEN
    SUBGOAL_THEN `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x0 IN topspace top`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "bd" (MP_TAC o SPEC `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f t x0`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `K:real`; `x0:A`; `--(&1)`; `t:real`]
        P2BX46_SOL_R_MONO) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `K:real`; `x0:A`] P2BX46_PHI_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:num->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `pp:num->A` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `L:real` THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> mfd_scalar atlas (p2bx46_G top atlas (g:A->real^N^N) f (--(&1))) x =
            mfd_scalar atlas g x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_SOL_SCALAR_M1 THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

