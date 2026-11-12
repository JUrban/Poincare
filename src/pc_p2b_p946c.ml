(* ========================================================================= *)
(* Unit pc_p2b_p946c: MT Claim 9.51 for the soliton flow, with the form of   *)
(* X2s that has points realizing the limsup L of R at infinity.  The         *)
(* parabolic rescaling Gl(t) = G(lam t) / lam (p2bx46_Gl) is in the class of *)
(* X2s (P2BX46_GL_X2S_HYPS) and has the X2s points (P2BX46_GL_POINTS); for   *)
(* lam = 1/2, the cylinder limit at the points gives L = 1                   *)
(* (P2BX46_CLAIM_951): at the limit time s0 = -L/2 the approximants read     *)
(* R(g) at forward points phi_tau pp, tau in [-1,0), where R(g) -> L by      *)
(* monotonicity along grad f and the limsup bound (P2BX46_FWD_SQUEEZE).      *)
(* ========================================================================= *)

needs "src/pc_p2b_p946g.ml";;
needs "src/pc_lim_curv.ml";;
needs "src/pc_p2b_979.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The parabolic rescaling Gl(t) = G(lam t) / lam of the soliton flow        *)
(* (0 < lam) is in the class of X2s, by scaling the slice properties of G    *)
(* (pc_p2b_p946g).  X2s at Gl reads G at the times lam t, which for lam < 1  *)
(* lie forward of the base time -1 (Claim 9.51, below).                      *)
(* ========================================================================= *)

let p2bx46_Gl = new_definition
 `p2bx46_Gl (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
            (f:A->real) (lam:real) =
    \t x. inv lam %% p2bx46_G top atlas g f (lam * t) x`;;

let P2BX46_GL_SLICE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f lam t.
     p2bx46_Gl top atlas g f lam t = (\x. inv lam %% p2bx46_G top atlas g f (lam * t) x)`,
  REWRITE_TAC[p2bx46_Gl]);;

let P2BX46_NEG_MUL = prove
 (`!lam t. &0 < lam /\ t < &0 ==> lam * t < &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < lam * --t ==> lam * t < &0`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let P2BX46_GL_RIEM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam t.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ t < &0
     ==> riemannian_metric atlas (p2bx46_Gl top atlas g f lam t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2BX46_GL_SLICE] THEN
  MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2BX46_SOL_RIEM THEN
  EXISTS_TAC `K:real` THEN ASM_SIMP_TAC[P2BX46_NEG_MUL]);;

let P2BX46_GL_RF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam a.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ a < &0
     ==> ricci_flow_on (top,atlas) a (&0) (p2bx46_Gl top atlas g f lam)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `lam * a:real`] P2BX46_SOL_RICCI_FLOW) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P2BX46_NEG_MUL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv lam` o MATCH_MP (REWRITE_RULE[IMP_CONJ] RICCI_FLOW_RESCALE)) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `a:real = a' /\ b:real = b' /\ (g:real->A->real^N^N) = g'
                        ==> ricci_flow_on (top,atlas) a b g
                            ==> ricci_flow_on (top,atlas) a' b' g'`) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    REAL_ARITH_TAC;
    REWRITE_TAC[p2bx46_Gl; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[real_div; REAL_INV_INV; REAL_MUL_AC]]);;

let P2BX46_GL_SCALAR = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam t x.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ t < &0 /\ x IN topspace top
     ==> mfd_scalar atlas (p2bx46_Gl top atlas g f lam t) x =
         mfd_scalar atlas g (p2bx46_phi top atlas g f (lam * t) x) / abs t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `lam * t < &0` ASSUME_TAC THENL [ASM_SIMP_TAC[P2BX46_NEG_MUL]; ALL_TAC] THEN
  REWRITE_TAC[P2BX46_GL_SLICE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2bx46_G (top:A topology) atlas (g:A->real^N^N) f (lam * t)`;
                 `inv lam`; `x:A`] P2AU_MFD_SCALAR_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `lam * t:real`; `x:A`] P2BX46_SOL_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs lam = lam /\ ~(abs t = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `~(abs t = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* Slice properties of Gl from those of G at lam t. *)

let P2BX46_GL_SECT_POS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam t x u v.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ t < &0 /\ x IN topspace top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     ~collinear {vec 0,u,v}
     ==> &0 < mfd_sectional atlas (p2bx46_Gl top atlas g f lam t) x u v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `lam * t < &0` ASSUME_TAC THENL [ASM_SIMP_TAC[P2BX46_NEG_MUL]; ALL_TAC] THEN
  REWRITE_TAC[P2BX46_GL_SLICE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2bx46_G (top:A topology) atlas (g:A->real^N^N) f (lam * t)`;
                 `inv lam`; `x:A`; `u:real^N`; `v:real^N`] RFA_MFD_SECTIONAL_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_SECT_POS_ALL THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]]);;

let P2BX46_GL_RM_NORM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam t x C0.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ t < &0 /\ x IN topspace top /\
     2 <= dimindex(:N) /\
     (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= C0)
     ==> mfd_rm_norm atlas (p2bx46_Gl top atlas g f lam t) x <= C0 / abs t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `lam * t < &0` ASSUME_TAC THENL [ASM_SIMP_TAC[P2BX46_NEG_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `C0 / abs t = (C0 / abs(lam * t)) / inv lam` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs lam = lam /\ ~(abs t = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `~(abs t = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[P2BX46_GL_SLICE] THEN MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX46_SOL_RM_NORM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `K:real`; `lam * t:real`] P2BX46_SOL_FLOW) THEN
    ASM_SIMP_TAC[]]);;

let P2BX46_GL_COMPLETE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam t.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ t < &0
     ==> mfd_complete (top,atlas) (p2bx46_Gl top atlas g f lam t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `lam * t < &0` ASSUME_TAC THENL [ASM_SIMP_TAC[P2BX46_NEG_MUL]; ALL_TAC] THEN
  REWRITE_TAC[P2BX46_GL_SLICE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2bx46_G (top:A topology) atlas (g:A->real^N^N) f (lam * t)`;
                 `inv lam`] MFD_COMPLETE_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2BX46_SOL_COMPLETE THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]);;

let P2BX46_GL_NONCOLL = prove
 (`!kappa top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K lam t.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ t < &0 /\ p2b_rm_noncoll kappa (top,atlas) g
     ==> p2b_rm_noncoll kappa (top,atlas) (p2bx46_Gl top atlas g f lam t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `lam * t < &0` ASSUME_TAC THENL [ASM_SIMP_TAC[P2BX46_NEG_MUL]; ALL_TAC] THEN
  REWRITE_TAC[P2BX46_GL_SLICE] THEN MATCH_MP_TAC P2BSK_NONCOLL_SCALE THEN
  ASM_REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX46_SOL_NONCOLL THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]]);;

let P2BX46_GL_KNC = prove
 (`!kappa top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K lam r0.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ p2b_rm_noncoll kappa (top,atlas) g
     ==> rfs_kappa_noncollapsed
           (rfs_flow_view (top,atlas) {s | s < &0} (p2bx46_Gl top atlas g f lam)) kappa r0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_vball; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `r:real`] THEN
  ASM_CASES_TAC `t < &0` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb"))))) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real`; `K:real`; `lam:real`; `t:real`]
    P2BX46_GL_NONCOLL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2b_rm_noncoll; DIMINDEX_3] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `r:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  USE_THEN "rb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> t - a < t`) THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]);;

(* dR/dt >= 0 for Gl: R(Gl u)(x) = R(g)(phi_{lam u} x) / abs u. *)

let P2BX46_DERIV_SCALE_ARG = prove
 (`!(h:real->real) D lam u.
     (h has_real_derivative D) (atreal (lam * u))
     ==> ((\u. h(lam * u)) has_real_derivative (lam * D)) (atreal u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real. v = lam * u`; `\u:real. lam * u`; `h:real->real`]
    (INST [`\v:real. D:real`,`g':real->real`; `lam:real`,`f':real`]
       HAS_REAL_DERIVATIVE_CHAIN)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `u:real` o CONJUNCT2)] THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC; REWRITE_TAC[]]);;

let P2BX46_GL_DR_POS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam t x dR.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ t < &0 /\ x IN topspace top /\
     ((\s. mfd_scalar atlas (p2bx46_Gl top atlas g f lam s) x) has_real_derivative dR)
       (atreal t)
     ==> &0 <= dR`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `lam * t < &0` ASSUME_TAC THENL [ASM_SIMP_TAC[P2BX46_NEG_MUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `lam * t:real`] P2BX46_SOL_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f (lam * t) x IN topspace top`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BX46_DR_SIGN THEN
  MAP_EVERY EXISTS_TAC
   [`\s. mfd_scalar atlas (g:A->real^N^N) (p2bx46_phi top atlas g f (lam * s) x)`;
    `lam * (&2 * inv(abs(lam * t)) *
     mfd_ricci atlas (g:A->real^N^N) (p2bx46_phi top atlas g f (lam * t) x)
       (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f (lam * t) x))
       (p2bx46_gradf atlas g f (p2bx46_phi top atlas g f (lam * t) x)))`;
    `\s. mfd_scalar atlas (p2bx46_Gl top atlas (g:A->real^N^N) f lam s) x`; `t:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\v. mfd_scalar atlas (g:A->real^N^N) (p2bx46_phi top atlas g f v x)`]
      P2BX46_DERIV_SCALE_ARG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC P2BX46_SOL_RDERIV THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[p2bx46_hyp];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ASM_MESON_TAC[p2bx46_hyp]];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BX46_GL_SCALAR THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Gl is in the class of X2s, and the points of X2s for Gl.                  *)
(* ========================================================================= *)

let P2BX46_GL_ANCFLOW0 = prove
 (`!kappa top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) f K lam.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ &0 < kappa /\ ~(topspace top = {}) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     p2b_rm_noncoll kappa (top,atlas) g
     ==> p2b_ancflow0 kappa (top,atlas) (p2bx46_Gl top atlas g f lam) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  REWRITE_TAC[p2b_ancflow0] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX46_GL_RF THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX46_GL_COMPLETE THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC P2BX46_GL_SECT_POS THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:B` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~collinear {vec 0:real^3, basis 1, basis 2}` ASSUME_TAC THENL
     [MATCH_MP_TAC RFA_NONCOLLINEAR_BASIS THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(mfd_sectional atlas (p2bx46_Gl top atlas (g:B->real^3^3) f lam s) x
                      (basis 1) (basis 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < a ==> &0 < abs a`) THEN
      MATCH_MP_TAC P2BX46_GL_SECT_POS THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX46_GL_RIEM THEN
      EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] P2BX46_GL_DR_POS) THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `f:B->real`; `K:real`; `lam:real`; `s:real`;
                          `x:B`] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2BX46_GL_KNC THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[]]);;

let P2BX46_GL_X2S_HYPS = prove
 (`!kappa top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) f K lam C0.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ &0 < kappa /\ ~compact_space top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= C0) /\
     p2b_rm_noncoll kappa (top,atlas) g /\ p2b_ksep top atlas
     ==> p2b_ancflow kappa (top,atlas) (p2bx46_Gl top atlas g f lam) (&0) /\
         (!t x. t < &0 /\ x IN topspace top
                ==> mfd_rm_norm atlas (p2bx46_Gl top atlas g f lam t) x <= C0 / abs t) /\
         (!t x u v. t < &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 < mfd_sectional atlas (p2bx46_Gl top atlas g f lam t) x u v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2b_ancflow] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX46_GL_ANCFLOW0 THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPACT_SPACE_TOPSPACE_EMPTY];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_GL_RM_NORM THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_GL_SECT_POS THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]]);;

(* Points: R(g) along phi_tau pp k for tau in [-1,0) tends to L when       *)
(* R(g)(pp k) tends to L, the limsup of R at infinity.                       *)

let P2BX46_FWD_SQUEEZE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K (pp:num->A) L tau.
     p2bx46_hyp top atlas g f K /\ (!k. pp k IN topspace top) /\
     (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\
     ((\k. mfd_scalar atlas g (pp k)) ---> L) sequentially /\
     (!e. &0 < e
          ==> ?S. compact_in top S /\
                  !x. x IN topspace top /\ ~(x IN S) ==> mfd_scalar atlas g x <= L + e) /\
     (?N. !k. N <= k ==> --(&1) <= tau k /\ tau k < &0)
     ==> ((\k. mfd_scalar atlas g (p2bx46_phi top atlas g f (tau k) (pp k))) ---> L)
         sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in")
    (CONJUNCTS_THEN2 (LABEL_TAC "leave") (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lsup") (X_CHOOSE_THEN `N0:num` (LABEL_TAC "tau"))))))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(LABEL_TAC "lim") THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `p2b_shrinker (top,atlas) (g:A->real^N^N) f` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bx46_hyp]; ALL_TAC] THEN
  USE_THEN "lim" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
  USE_THEN "lsup" (MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sb"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real`; `S:A->bool`] P2BX46_CONT_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX46_F_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "bd"))] THEN
  USE_THEN "leave" (MP_TAC o SPEC `{x:A | x IN topspace top /\ f x <= B}`) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `K:real`] P2BX46_F_PROPER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[p2bx46_hyp]; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2"))] THEN
  EXISTS_TAC `N0 + N1 + N2:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "tau" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "n1" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "n2" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(pp:num->A) k IN topspace top` ASSUME_TAC THENL
   [USE_THEN "in" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `B < (f:A->real) ((pp:num->A) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((pp:num->A) k IN {x:A | x IN topspace top /\ f x <= B})` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_NOT_LE];
    ALL_TAC] THEN
  ABBREV_TAC `z = p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f (tau(k:num)) (pp k)` THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `K:real`; `tau(k:num):real`]
      P2BX46_SOL_FLOW) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^N^N) ((pp:num->A) k) <= mfd_scalar atlas g z /\
    (f:A->real) (pp k) <= f z`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `K:real`; `(pp:num->A) k`] P2BX46_PHI_REFL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `K:real`; `(pp:num->A) k`; `--(&1)`;
                     `tau(k:num):real`] P2BX46_SOL_R_MONO);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `K:real`; `(pp:num->A) k`; `--(&1)`;
                     `tau(k:num):real`] P2BX46_SOL_F_MONO)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z:A) IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "bd" (MP_TAC o SPEC `z:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sb" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `abs(mfd_scalar atlas (g:A->real^N^N) ((pp:num->A) k) - L) < e` THEN
  ASM_REAL_ARITH_TAC);;

let P2BX46_GL_POINTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K lam (pp:num->A) L.
     p2bx46_hyp top atlas g f K /\ &0 < lam /\ lam <= &1 /\ (!k. pp k IN topspace top) /\
     (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\ &0 < L /\
     ((\k. mfd_scalar atlas g (pp k)) ---> L) sequentially /\
     (!e. &0 < e
          ==> ?S. compact_in top S /\
                  !x. x IN topspace top /\ ~(x IN S) ==> mfd_scalar atlas g x <= L + e)
     ==> ((\k. mfd_scalar atlas (p2bx46_Gl top atlas g f lam (--(&1))) (pp k)) ---> L)
         sequentially /\
         (!e. &0 < e
              ==> ?S. compact_in top S /\
                      !x. x IN topspace top /\ ~(x IN S)
                          ==> mfd_scalar atlas (p2bx46_Gl top atlas g f lam (--(&1))) x
                              <= L + e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lsup")))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> mfd_scalar atlas (p2bx46_Gl top atlas g f lam (--(&1))) x =
            mfd_scalar atlas (g:A->real^N^N) (p2bx46_phi top atlas g f (--lam) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `K:real`; `lam:real`; `--(&1)`; `x:A`]
      P2BX46_GL_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_DIV_1; REAL_MUL_RNEG; REAL_MUL_RID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\k. mfd_scalar atlas (g:A->real^N^N)
                      (p2bx46_phi top atlas g f ((\k:num. --lam) k) ((pp:num->A) k))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P2BX46_FWD_SQUEEZE THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "lsup" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sb"))) THEN
  EXISTS_TAC `IMAGE (p2bx46_psi (top:A topology) atlas (g:A->real^N^N) f (--lam)) S` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `K:real`; `--lam:real`] P2BX46_SOL_FLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[p2bx46_psi] THEN
    MATCH_MP_TAC MCF_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`{t:real^1 | drop t < &0}`; `f:A->real`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  USE_THEN "sb" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((x:A) IN IMAGE (p2bx46_psi top atlas (g:A->real^N^N) f (--lam)) S)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `p2bx46_phi (top:A topology) atlas (g:A->real^N^N) f (--lam) x` THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* MT Claim 9.51 (the limsup L of R at infinity is 1).  X2s at               *)
(* the points pp for Gl (lam = 1/2) gives a cylinder limit g' with           *)
(* R(g'(s)) = 1/(1 - s); at the limit time s0 = -L/2 the approximants read  *)
(* R(g) at phi_{lam tau} pp with lam tau in [-1,0), where R(g) -> L, so      *)
(* R(g'(s0)) = 1/(1 - s0/L), and L = 1.                                       *)
(* ========================================================================= *)

let P2BX46_CYL_MODEL_SCALAR = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3).
     p2b_cyl_model (top,atlas) g /\ smooth_manifold_atlas top atlas /\
     (!t. t <= &0 ==> riemannian_metric atlas (g t))
     ==> ?lam. &0 < lam /\
               !t x. t <= &0 /\ x IN topspace top
                     ==> mfd_scalar atlas (g t) x = &1 / (lam - t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_cyl_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "par") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pb")))))))
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y. ~(y = vec 0:real^3) /\ x = (p:real^3->B) y`
  (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `IMAGE (p:real^3->B) {y | ~(y = vec 0)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "par" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `t / lam < &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) t`; `ball(y:real^3,r)`; `p:real^3->B`;
                 `&1`; `y:real^3`] P2B9_PARAM_LSCALAR_SCALED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_01]; REWRITE_TAC[REAL_DIV_1]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `lscalar (\z. &1 %% rfs_pullback atlas (p:real^3->B) ((g:real->B->real^3^3) t) z) y =
    lscalar (\z. lam %% cylinder_flow (t / lam) z) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; MATRIX_CMUL_LID] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `dist(y:real^3,z) < r` THEN ASM_REWRITE_TAC[DIST_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (t / lam)`; `lam:real`; `y:real^3`]
    LSCALAR_SCALE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; IN_DELETE; IN_UNIV]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`t / lam`; `y:real^3`] RFB_CYL_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~(lam = &0) /\ ~(lam - t = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(lam = &0) /\ ~(lam - t = &0)
                           ==> (&1 / (&1 - t / lam)) / lam = &1 / (lam - t)`]);;

let P2BX46_CYL_LIMIT_R = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) xl.
     p2b_cyl_model (top,atlas) g /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     mfd_scalar atlas (g(&0)) xl = &1
     ==> (!t. t <= &0 ==> riemannian_metric atlas (g t)) /\
         (!t x. t <= &0 /\ x IN topspace top
                ==> mfd_scalar atlas (g t) x = &1 / (&1 - t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[rfs_flow_upto; ricci_flow_on]] THEN
    ASM_CASES_TAC `t = &0` THENL
     [ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`] P2BX46_CYL_MODEL_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rs"))) THEN
  SUBGOAL_THEN `lam = &1` SUBST_ALL_TAC THENL
   [USE_THEN "rs" (MP_TAC o SPECL [`&0`; `xl:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ASM_REWRITE_TAC[REAL_SUB_RZERO]] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    USE_THEN "rs" ACCEPT_TAC]);;

(* Subsequences keep the point properties. *)

let P2BX46_SUBSEQ_POINTS = prove
 (`!top (R:A->real) (pp:num->A) L sub.
     p3_subseq sub /\ (!k. pp k IN topspace top) /\
     (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\
     ((\k. R(pp k)) ---> L) sequentially
     ==> (!k. (pp o sub) k IN topspace top) /\
         (!S. compact_in top S ==> ?N. !k. N <= k ==> ~((pp o sub) k IN S)) /\
         ((\k. R((pp o sub) k)) ---> L) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_subseq; o_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MONOTONE_BIGGER) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `S:A->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `S:A->bool` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS];
    UNDISCH_TAC `((\k. (R:A->real) ((pp:num->A) k)) ---> L) sequentially` THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN ASM_MESON_TAC[LE_TRANS]]);;

(* A real limit identity. *)

let P2BX46_LIMIT_ID = prove
 (`!(A:num->real) (Rk:num->real) (Qk:num->real) a L s0.
     &0 < L /\ s0 < &0 /\ (A ---> a) sequentially /\ (Rk ---> L) sequentially /\
     (Qk ---> L) sequentially /\ (!k. &0 < Qk k) /\
     (!k. A k = Rk k / abs(--(&1) + s0 / Qk k) / Qk k)
     ==> a = &1 / (&1 - s0 / L)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `A:num->real` THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN `!k. abs(--(&1) + s0 / (Qk:num->real) k) = &1 - s0 / Qk k` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `s0 / (Qk:num->real) k < &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `A = (\k. (Rk:num->real) k / (&1 - s0 / (Qk:num->real) k) / Qk k)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / (&1 - s0 / L) = (L / (&1 - s0 / L)) / L` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(L = &0) /\ ~(&1 - s0 / L = &0)` MP_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `s0 / L < &0` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_DIV THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REALLIM_DIV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC REALLIM_DIV THEN ASM_REWRITE_TAC[REALLIM_CONST] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `s0 / L < &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Claim 9.51.                                                               *)
(* ========================================================================= *)

let P2BX46_CLAIM_951 = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) f K (pp:num->B) L sub
    (top':B topology) atlas' g' xl W phi.
     p2bx46_hyp top atlas g f K /\ (!k. pp k IN topspace top) /\
     (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\ &0 < L /\
     ((\k. mfd_scalar atlas g (pp k)) ---> L) sequentially /\
     (!e. &0 < e
          ==> ?S. compact_in top S /\
                  !x. x IN topspace top /\ ~(x IN S) ==> mfd_scalar atlas g x <= L + e) /\
     p3_subseq sub /\
     p2c_flow_limit_with
       (\k. rfs_flow_view (top,atlas) {t | t < &0} (p2bx46_Gl top atlas g f (inv(&2))))
       (pp o sub) (\k. --(&1))
       (\k. mfd_scalar atlas (p2bx46_Gl top atlas g f (inv(&2)) (--(&1))) (pp(sub k)))
       {s | s <= &0} (top',atlas') g' xl W phi /\
     mfd_scalar atlas' (g'(&0)) xl = &1 /\
     (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
     p2b_cyl_model (top',atlas') g'
     ==> L = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lsup") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "flim") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  ABBREV_TAC `s0 = --(L / &2)` THEN
  SUBGOAL_THEN `s0 < &0` ASSUME_TAC THENL [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the points pp o sub *)
  MP_TAC(ISPECL [`top:B topology`; `mfd_scalar atlas (g:B->real^3^3)`; `pp:num->B`; `L:real`;
                 `sub:num->num`] P2BX46_SUBSEQ_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[o_THM]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ABBREV_TAC
   `Q = \k. mfd_scalar atlas (p2bx46_Gl top atlas (g:B->real^3^3) f (inv(&2)) (--(&1)))
                       ((pp:num->B)((sub:num->num) k))` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `f:B->real`; `K:real`; `inv(&2)`; `\k. (pp:num->B)((sub:num->num) k)`; `L:real`]
    P2BX46_GL_POINTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
  (* facts from the flow limit *)
  USE_THEN "flim" (MP_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`] P2BX46_CYL_LIMIT_R) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cyl")) THEN
  (* scalar curvature of the limit at time s0 *)
  MP_TAC(ISPECL
   [`\k:num. rfs_flow_view (top,atlas) {t | t < &0}
                (p2bx46_Gl top atlas (g:B->real^3^3) f (inv(&2)))`;
    `(pp:num->B) o (sub:num->num)`; `\k:num. --(&1)`; `Q:num->real`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
    `s0:real`; `xl:B`] LIM_CURV_KEY) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "flim" ACCEPT_TAC;
      REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
      REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN DISCH_TAC THEN
      MATCH_MP_TAC P2BX46_GL_RIEM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; o_THM] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "key") THEN
  (* the limit identity *)
  MP_TAC(ISPECL
   [`\k. mfd_scalar atlas
           (p2bx46_Gl top atlas (g:B->real^3^3) f (inv(&2)) (--(&1) + s0 / (Q:num->real) k))
           ((pp:num->B)((sub:num->num) k)) / Q k`;
    `\k. mfd_scalar atlas (g:B->real^3^3)
           (p2bx46_phi top atlas g f (inv(&2) * (--(&1) + s0 / (Q:num->real) k))
              ((pp:num->B)((sub:num->num) k)))`;
    `Q:num->real`; `mfd_scalar atlas' ((g':real->B->real^3^3) s0) xl`; `L:real`; `s0:real`]
    P2BX46_LIMIT_ID) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "key" (MP_TAC o SPEC `e / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `f:B->real`; `K:real`; `\k. (pp:num->B)((sub:num->num) k)`;
                     `L:real`; `\k. inv(&2) * (--(&1) + s0 / (Q:num->real) k)`]
        P2BX46_FWD_SQUEEZE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `((Q:num->real) ---> L) sequentially` THEN
      REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `L / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `--(&1) <= s0 / (Q:num->real) k /\ s0 / Q k < &0` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN EXPAND_TAC "s0" THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      X_GEN_TAC `k:num` THEN
      SUBGOAL_THEN `--(&1) + s0 / (Q:num->real) k < &0` ASSUME_TAC THENL
       [SUBGOAL_THEN `s0 / (Q:num->real) k < &0` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        ALL_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC P2BX46_GL_SCALAR THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  USE_THEN "cyl" (MP_TAC o SPECL [`s0:real`; `xl:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "s0" THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD);;

