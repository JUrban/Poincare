(* ========================================================================= *)
(* Unit pc_p2b_p946h: far level sets of the soliton potential f in           *)
(* MT Prop 9.46.  Ricci bounds from sectional bounds in dimension 3          *)
(* (P2BX46_LRIC_FRAME, _LE_HALF, _POS); R < 1 at far points once the limsup  *)
(* of R at infinity is 1 (P2BX46_R_LT_1_FAR); traces in orthonormal bases    *)
(* (P2BX46_TRACE_ONB, P2BX46_LSCALAR_ONB3); MT (9.26): the induced scalar    *)
(* curvature of a regular level set is < 1 where R < 1 and |grad f|^2 > 1/2  *)
(* (P2BX46_LEVEL_RN_LT1, from LVS_GAUSS of pc_mfd_level4).  The normalized   *)
(* gradient flow maps far level sets onto each other (P2BX46_NFLOW_LEVEL) by *)
(* leaf diffeomorphisms (P2BX46_LEAF_DIFFEO) which stretch tangent vectors   *)
(* (P2BX46_LEAF_STRETCH); hence areas of spheres pulled back to a fixed far  *)
(* level do not grow (P2BX46_AREA_PULL), and Gauss-Bonnet (pc_cm_gbs2)       *)
(* excludes far spheres of area near 8 pi (P2BX46_FAR_SPHERES_CONTRA, with   *)
(* the neck spheres of pc_p2b_p946i as input).                               *)
(* ========================================================================= *)

needs "src/pc_p2b_p946c.ml";;
needs "src/pc_mfd_level4.ml";;
needs "src/pc_rfa_p3alg.ml";;
needs "src/pc_cmp_frame.ml";;
needs "src/pc_p2b_sol.ml";;
needs "src/pc_cm_gbs2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Ricci bounds in dimension 3 from the sectional curvature,                 *)
(* in a frame diagonalizing Ric (RFA_P3_EIGENFRAME): Ric(w,w) <= R/2 |w|^2   *)
(* when sec >= 0, and 0 < Ric(w,w) for w ~= 0 when sec > 0.                 *)
(* ========================================================================= *)

let P2BX46_LRIC_FRAME = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> ?S:real^3^3 r1 r2 r3.
           (!w. lricci G y w w =
                ((transp S ** basis 1) dot (G y ** w)) pow 2 * r1 +
                ((transp S ** basis 2) dot (G y ** w)) pow 2 * r2 +
                ((transp S ** basis 3) dot (G y ** w)) pow 2 * r3 /\
                w dot (G y ** w) =
                ((transp S ** basis 1) dot (G y ** w)) pow 2 +
                ((transp S ** basis 2) dot (G y ** w)) pow 2 +
                ((transp S ** basis 3) dot (G y ** w)) pow 2) /\
           invertible S /\ matrix_inv(G y) = transp S ** S /\
           lscalar G y = r1 + r2 + r3 /\
           r1 = lricci G y (transp S ** basis 1) (transp S ** basis 1) /\
           r2 = lricci G y (transp S ** basis 2) (transp S ** basis 2) /\
           r3 = lricci G y (transp S ** basis 3) (transp S ** basis 3) /\
           r1 <= lscalar G y / &2 /\ r2 <= lscalar G y / &2 /\ r3 <= lscalar G y / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_P3_EIGENFRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INVERTIBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!b. 1 <= b /\ b <= 3
        ==> lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis b) (transp S ** basis b)
            <= lscalar G y / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(transp (S:real^3^3) ** basis b) dot
      ((G:real^3->real^3^3) y ** (transp S ** basis b)) = &1`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `b:num`; `b:num`]
        RFA_GFRAME_ORTHO) THEN
      ASM_REWRITE_TAC[DIMINDEX_3];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `transp (S:real^3^3) ** basis b`] RFA_PCURV_AS_SEC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[RFA_LPCURV_DIAG; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `S:real^3^3` THEN
  MAP_EVERY EXISTS_TAC
   [`lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis 1) (transp S ** basis 1)`;
    `lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis 2) (transp S ** basis 2)`;
    `lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis 3) (transp S ** basis 3)`] THEN
  ASM_SIMP_TAC[ARITH] THEN CONJ_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                     `w:real^3`; `w:real^3`] RFA_FRAME3_RIC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `w:real^3`; `w:real^3`]
        RFA_FRAME3_DOT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_2]];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
      RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3]]);;

let P2BX46_LRIC_LE_HALF = prove
 (`!U (G:real^3->real^3^3) y w.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> lricci G y w w <= lscalar G y / &2 * (w dot (G y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] P2BX46_LRIC_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real`
    (X_CHOOSE_THEN `r3:real`
      (CONJUNCTS_THEN2 (MP_TAC o SPEC `w:real^3`) STRIP_ASSUME_TAC))))) THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let P2BX46_LRIC_POS = prove
 (`!U (G:real^3->real^3^3) y w.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < lsectional G y u v) /\ ~(w = vec 0)
     ==> &0 < lricci G y w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] P2BX46_LRIC_FRAME) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real`
    (X_CHOOSE_THEN `r3:real`
      (CONJUNCTS_THEN2 (MP_TAC o SPEC `w:real^3`) STRIP_ASSUME_TAC))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (LABEL_TAC "gw")) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
    RFA_SH_RIC_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `w:real^3`]
    LRG_METRIC_POS) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "gw" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  ABBREV_TAC `c1 = (transp (S:real^3^3) ** basis 1) dot ((G:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `c2 = (transp (S:real^3^3) ** basis 2) dot ((G:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `c3 = (transp (S:real^3^3) ** basis 3) dot ((G:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `m = min r1 (min r2 r3)` THEN
  SUBGOAL_THEN `&0 < m /\ m <= r1 /\ m <= r2 /\ m <= r3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `m * (c1 pow 2 + c2 pow 2 + c3 pow 2)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* Manifold forms at the preferred chart. *)

let P2BX46_MFD_RIC_LE_HALF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> mfd_ricci atlas g x w w <= mfd_scalar atlas g x / &2 * (w dot (g x ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
    [SYM th]) THEN
  REWRITE_TAC[mfd_ricci; mfd_scalar] THEN MATCH_MP_TAC P2BX46_LRIC_LE_HALF THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[GSYM mfd_sectional]);;

let P2BX46_MFD_RIC_POS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas g x u v) /\ ~(w = vec 0)
     ==> &0 < mfd_ricci atlas g x w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci] THEN MATCH_MP_TAC P2BX46_LRIC_POS THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[GSYM mfd_sectional]);;

(* ========================================================================= *)
(* R < 1 at far points (MT p. 214, after Claim 9.51).  With L =              *)
(* 1, R(x) >= 1 at a far point x would make R increase strictly along the   *)
(* forward flow line (d/dt R = 2 Ric(grad f, grad f) / |t| > 0), which       *)
(* leaves every compact set, against R <= 1 + e outside a compact set.       *)
(* ========================================================================= *)

let P2BX46_DERIV_POS_RIGHT = prove
 (`!(h:real->real) h' a.
     (h has_real_derivative h') (atreal a) /\ &0 < h'
     ==> ?d. &0 < d /\ !t. a < t /\ t < a + d ==> h a < h t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_DERIVATIVE_ATREAL]) THEN
  REWRITE_TAC[REALLIM_ATREAL] THEN DISCH_THEN(MP_TAC o SPEC `h' / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < ((h:real->real) t - h a) / (t - a)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO] THEN REAL_ARITH_TAC);;

let P2BX46_GRADF_NZ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f x.
     p2b_shrinker (top,atlas) g f /\ x IN topspace top /\
     ~(lgrad2 (metric_local atlas (chart_at atlas x) g)
              (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) = &0)
     ==> ~(p2bx46_gradf atlas g f x = vec 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
    RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^N^N)`;
                 `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                       (x:A)) y)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
    P2BX46_CDF_CGRAD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `p2bx46_gradf atlas (g:A->real^N^N) f x = vec 0` THEN
  REWRITE_TAC[p2bx46_gradf] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[P2BX46_CDF_RFA_D1; rfa_d1] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
      (\z. lift((f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                 (x:A)) z)))
      (at (SND(chart_at atlas x) x)))`
  (fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th; DROP_VEC]) THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let P2BX46_R_LT_1_FAR = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K C Rmax x.
     p2bx46_hyp top atlas g f K /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top
          ==> mfd_scalar atlas g x +
              lgrad2 (metric_local atlas (chart_at atlas x) g)
                     (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) -
              f x = C) /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x <= Rmax) /\
     (!e. &0 < e
          ==> ?S. compact_in top S /\
                  !x. x IN topspace top /\ ~(x IN S) ==> mfd_scalar atlas g x <= &1 + e) /\
     x IN topspace top /\ Rmax - C + &1 <= f x
     ==> mfd_scalar atlas g x < &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ham") (CONJUNCTS_THEN2 (LABEL_TAC "rmax")
    (CONJUNCTS_THEN2 (LABEL_TAC "lsup") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_HYP_MCF) THEN
  SUBGOAL_THEN `p2b_shrinker (top,atlas) (g:A->real^3^3) f` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bx46_hyp]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  (* the derivative of R along the flow line at t = -1 is positive *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `--(&1)`; `x:A`] P2BX46_SOL_RDERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `x:A`] P2BX46_PHI_REFL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_INV_1; REAL_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 < &2 * mfd_ricci atlas (g:A->real^3^3) x (p2bx46_gradf atlas g f x)
                         (p2bx46_gradf atlas g f x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC P2BX46_MFD_RIC_POS THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC P2BX46_GRADF_NZ THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ham" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "rmax" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. mfd_scalar atlas (g:A->real^3^3) (p2bx46_phi top atlas g f s x)`;
    `&2 * mfd_ricci atlas (g:A->real^3^3) x (p2bx46_gradf atlas g f x)
                    (p2bx46_gradf atlas g f x)`; `--(&1)`] P2BX46_DERIV_POS_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t1 = --(&1) + min (d / &2) (&1 / &2)` THEN
  SUBGOAL_THEN `--(&1) < t1 /\ t1 < --(&1) + d /\ t1 < &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `x:A`] P2BX46_PHI_REFL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ABBREV_TAC
   `eta = (mfd_scalar atlas (g:A->real^3^3) (p2bx46_phi top atlas g f t1 x) - &1) / &2` THEN
  SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL [EXPAND_TAC "eta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "lsup" (MP_TAC o SPEC `eta:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sb"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real`; `S:A->bool`] P2BX46_CONT_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P2BX46_F_CONTINUOUS) THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "bd"))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C:real`; `Rmax:real`; `x:A`] P2BX46_SOL_ESCAPE_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "ham" ACCEPT_TAC; USE_THEN "rmax" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `max B ((f:A->real)(p2bx46_phi top atlas (g:A->real^3^3) f t1 x))`) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t1 <= t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `f:A->real`; `K:real`; `x:A`; `t:real`; `t1:real`]
      P2BX46_SOL_F_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bx46_phi (top:A topology) atlas (g:A->real^3^3) f t x IN topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p2bx46_phi (top:A topology) atlas (g:A->real^3^3) f t x IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "bd" (MP_TAC o SPEC `p2bx46_phi (top:A topology) atlas
                                                    (g:A->real^3^3) f t x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sb" (MP_TAC o SPEC `p2bx46_phi (top:A topology) atlas (g:A->real^3^3) f t x`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `x:A`; `t1:real`; `t:real`] P2BX46_SOL_R_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(mfd_scalar atlas (g:A->real^3^3) (p2bx46_phi top atlas g f t1 x) - &1) / &2 =
               eta` THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Traces in an orthonormal basis, and MT (9.26): on a far                   *)
(* regular level set the induced scalar curvature is < 1.                    *)
(* ========================================================================= *)

let P2BX46_TRACE_ONB = prove
 (`!(h:real^N^N) (M:real^N^N) (v:num->real^N).
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> v i dot (h ** v j) = if i = j then &1 else &0)
     ==> trace(matrix_inv h ** M) = sum(1..dimindex(:N)) (\i. v i dot (M ** v i))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `V = (lambda r i. (v:num->real^N) i $ r):real^N^N` THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N) ==> (V:real^N^N) ** basis i = v i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS] THEN EXPAND_TAC "V" THEN
    SIMP_TAC[column; CART_EQ; LAMBDA_BETA] THEN ASM_SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w i. 1 <= i /\ i <= dimindex(:N) ==> (transp(V:real^N^N) ** (w:real^N))$i = v i dot w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "V" THEN
    ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; TRANSP_COMPONENT; dot] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(V:real^N^N) ** (h:real^N^N) ** V = mat 1` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_EQUAL_COLUMNS] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_BASIS; GSYM MATRIX_VECTOR_MUL_ASSOC;
                 MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[BASIS_COMPONENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv(h:real^N^N) = (V:real^N^N) ** transp V` SUBST1_TAC THENL
   [MATCH_MP_TAC MATRIX_INV_UNIQUE_LEFT THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(transp(V:real^N^N) ** (M:real^N^N) ** V)$i$i =
    ((transp V ** M ** V) ** basis i)$i`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC]);;

(* The scalar curvature is the sum of Ric over an orthonormal frame (3-d). *)

let P2BX46_LRIC_MATRIX_DOT = prove
 (`!U (G:real^N->real^N^N) y v w.
     metric_field U G /\ y IN U
     ==> v dot ((lambda i j. lricci G y (basis i) (basis j)):real^N^N ** w) =
         lricci G y v w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM BASIS_EXPANSION] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `1..dimindex(:N)`;
                 `\i. (v:real^N)$i`; `\i. basis i:real^N`;
                 `vsum(1..dimindex(:N)) (\i. (w:real^N)$i % (basis i:real^N))`] P2BX46_LRICCI_VSUM1) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `1..dimindex(:N)`;
                 `\j. (w:real^N)$j`; `\j. basis j:real^N`; `basis i:real^N`]
    P2BX46_LRICCI_VSUM2) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let P2BX46_LSCALAR_ONB3 = prove
 (`!U (G:real^3->real^3^3) y e1 e2 e3.
     metric_field U G /\ y IN U /\
     e1 dot (G y ** e1) = &1 /\ e2 dot (G y ** e2) = &1 /\ e3 dot (G y ** e3) = &1 /\
     e1 dot (G y ** e2) = &0 /\ e1 dot (G y ** e3) = &0 /\ e2 dot (G y ** e3) = &0
     ==> lscalar G y = lricci G y e1 e1 + lricci G y e2 e2 + lricci G y e3 e3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp((G:real^3->real^3^3) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (G:real^3->real^3^3) y =
    trace(matrix_inv(G y) ** (lambda i j. lricci G y (basis i) (basis j)):real^3^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[lscalar; trace] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`;
                 `(lambda i j. lricci (G:real^3->real^3^3) y (basis i) (basis j)):real^3^3`;
                 `\i. if i = 1 then e1 else if i = 2 then e2 else e3:real^3`]
    P2BX46_TRACE_ONB) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_3] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(i = 1 \/ i = 2 \/ i = 3) /\ (j = 1 \/ j = 2 \/ j = 3)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[DOT_SYM; DOT_MATRIX_TRANSP_LMUL];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
    P2BX46_LRIC_MATRIX_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* MT (9.26).  On a regular level set of f, at x with R < 1 and              *)
(* |grad f|^2 > 1/2, the induced scalar curvature is < 1:                    *)
(*   R_N = R - 2 Ric(n,n) + 2 det(II), II = (g/2 - Ric)|TN / |grad f|,      *)
(*   4 det(Hess f|TN) <= (1 - R + Ric(n,n))^2 < 2 (1 - R + Ric(n,n)) |grad f|^2. *)
(* ========================================================================= *)

let P2BX46_LHESS_MFD_HESS = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f x a b.
     cmp_lhess (metric_local atlas (chart_at atlas x) g)
               (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) a b =
     p2b_mfd_hess atlas g f x a b`,
  REWRITE_TAC[cmp_lhess; p2b_mfd_hess]);;

(* The arithmetic core of (9.26). *)

let P2BX46_926_ARITH = prove
 (`!p q r Rn s2.
     &0 <= Rn /\ &0 <= p /\ &0 <= q /\ Rn <= (p + q + Rn) / &2 /\
     p + q + Rn < &1 /\ &1 < &2 * s2
     ==> (p + q + Rn) - &2 * Rn +
         &2 * (((inv(&2) - p) / sqrt s2) * ((inv(&2) - q) / sqrt s2) -
               ((&0 - r) / sqrt s2) pow 2) < &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt s2 /\ sqrt s2 pow 2 = s2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((inv(&2) - p) / sqrt s2) * ((inv(&2) - q) / sqrt s2) - ((&0 - r) / sqrt s2) pow 2 =
    ((inv(&2) - p) * (inv(&2) - q) - r pow 2) / s2`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ABBREV_TAC `t = sqrt s2` THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `Y = (inv(&2) - p) * (inv(&2) - q) - r pow 2` THEN
  SUBGOAL_THEN `&2 * Y < (&1 - p - q + Rn) * s2` MP_TAC THENL
   [SUBGOAL_THEN `(&1 - p - q) * (&1 - p - q) < (&1 - p - q) * (&2 * s2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Rn * s2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `p - q:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN
    EXPAND_TAC "Y" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&2 * (Y / s2) < &1 - p - q + Rn` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&2 * (Y / s2) = (&2 * Y) / s2`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    REAL_ARITH_TAC]);;

let P2BX46_LEVEL_RN_LT1 = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f W u x.
     p2b_shrinker (top,atlas) g f /\ open_in top W /\ lvs_regular atlas W f u /\
     x IN lvs_set W f u /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v) /\
     mfd_scalar atlas g x < &1 /\
     &1 < &2 * lgrad2 (metric_local atlas (chart_at atlas x) g)
                      (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x)
     ==> mfd_scalar (lvs_atlas top atlas W f u) (lvs_metric top atlas g W f u) x < &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set W f u` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. p2b_mfd_hess atlas (g:A->real^3^3) f x a b =
          inv(&2) * (a dot (g x ** b)) - mfd_ricci atlas g x a b`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `mfd_ricci atlas (g:A->real^3^3) x a b + p2b_mfd_hess atlas g f x a b =
      inv(&2) * (a dot (g x ** b))`
    MP_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`] LVS_GAUSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`] LVS_GAUSS_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v2:real^2` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`] LVS_II_PUSHFORWARD) THEN
  ASM_REWRITE_TAC[P2BX46_LHESS_MFD_HESS] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  (* the trace R = Ric(e1,e1) + Ric(e2,e2) + Ric(n,n) *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) x =
    mfd_ricci atlas g x (lvs_jac top atlas W f u x v1) (lvs_jac top atlas W f u x v1) +
    mfd_ricci atlas g x (lvs_jac top atlas W f u x v2) (lvs_jac top atlas W f u x v2) +
    mfd_ricci atlas g x (lvs_normal atlas g f x) (lvs_normal atlas g f x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_scalar; mfd_ricci] THEN MATCH_MP_TAC P2BX46_LSCALAR_ONB3 THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Ric bounds *)
  SUBGOAL_THEN
   `!w. &0 <= mfd_ricci atlas (g:A->real^3^3) x w w`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mfd_ricci] THEN
    MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                          (FST(chart_at atlas x))`;
                   `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                   `&0`; `w:real^3`] CMPZ_LRICCI_SEC_LOWER) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; GSYM mfd_sectional];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ricci atlas (g:A->real^3^3) x (lvs_normal atlas g f x) (lvs_normal atlas g f x) <=
    mfd_scalar atlas g x / &2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `lvs_normal atlas (g:A->real^3^3) f (x:A)`] P2BX46_MFD_RIC_LE_HALF) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
  UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) x < &1` THEN
  UNDISCH_TAC
   `mfd_ricci atlas (g:A->real^3^3) x (lvs_normal atlas g f x) (lvs_normal atlas g f x) <=
    mfd_scalar atlas g x / &2` THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `mfd_scalar atlas (g:A->real^3^3) x`)) THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC P2BX46_926_ARITH THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The normalized gradient field chi(f) grad f / |grad f|^2,                 *)
(* chi(s) = smooth_step(s - a), on a manifold where |grad f| > 0 on f >= a; *)
(* it is smooth in charts and f is an escape function for it, so its flow    *)
(* exists (pc_mfd_cflow); along the flow f grows with speed in [0,1], with   *)
(* speed 1 where f >= a + 1, so the flow maps level sets onto level sets.    *)
(* ========================================================================= *)

let p2bx46_ngrad = new_definition
 `p2bx46_ngrad (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) (x:A) =
    lgrad2 (metric_local atlas (chart_at atlas x) g)
           (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x)`;;

let p2bx46_nfield = new_definition
 `p2bx46_nfield (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) (a:real) =
    \t:real x:A. (smooth_step(f x - a) * inv(p2bx46_ngrad atlas g f x)) %
                 p2bx46_gradf atlas g f x`;;

let P2BX46_NGRAD_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f c p.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\ p IN FST c
     ==> p2bx46_ngrad atlas g f p =
         lgrad2 (metric_local atlas c g) (\y. f(chart_inv c y)) (SND c p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx46_ngrad] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX46_LGRAD2_CHART THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  ASM_SIMP_TAC[]);;

let P2BX46_NFIELD_REP_SMOOTH = prove
 (`!U (G:real^N->real^N^N) fc a.
     metric_field U G /\ smooth_map_on U (\y. lift(fc y)) /\
     (!y. y IN U /\ a <= fc y ==> &0 < lgrad2 G fc y)
     ==> smooth_map_on U
           (\y. (smooth_step(fc y - a) * inv(lgrad2 G fc y)) % p3s_cgrad G fc y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\y. lift(lgrad2 (G:real^N->real^N^N) fc y))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BS_LGRAD2_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `a <= (fc:real^N->real) y0` THENL
   [EXISTS_TAC `{y:real^N | y IN U /\ lift(lgrad2 (G:real^N->real^N^N) fc y) IN
                                      {z:real^1 | &0 < drop z}}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[drop; REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT];
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `W = {y:real^N | y IN U /\ lift(lgrad2 (G:real^N->real^N^N) fc y) IN
                                         {z:real^1 | &0 < drop z}}` THEN
    SUBGOAL_THEN `open(W:real^N->bool) /\ W SUBSET U /\
                  !y. y IN W ==> &0 < lgrad2 (G:real^N->real^N^N) fc y`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        REWRITE_TAC[drop; REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
        REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN
     `(\y. smooth_step((fc:real^N->real) y - a) %
           inv(lgrad2 (G:real^N->real^N^N) fc y) % p3s_cgrad G fc y) =
      (\y. drop(lift(smooth_step(drop(lift(fc y) - lift a)))) %
           (drop(lift(inv(drop(lift(lgrad2 G fc y))))) % p3s_cgrad G fc y))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP; DROP_SUB]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
          ASM_REWRITE_TAC[];
          ASM_MESON_TAC[REAL_LT_IMP_NZ]];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_CGRAD_SMOOTH THEN ASM_REWRITE_TAC[]]];
    EXISTS_TAC `{y:real^N | y IN U /\ lift((fc:real^N->real) y) IN {z:real^1 | drop z < a}}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT];
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^N. vec 0:real^N` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_ELIM_THM; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `smooth_step((fc:real^N->real) x - a) = &0` SUBST1_TAC THENL
       [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO]]]]);;

let P2BX46_NFIELD_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f a c.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x)
     ==> smooth_map_on ((:real^1) PCROSS IMAGE (SND c) (FST c))
           (mfl_field atlas (p2bx46_nfield atlas g f a) c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `open((:real^1) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `(\y. (smooth_step((\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)) y - a) *
          inv(lgrad2 (metric_local atlas c (g:A->real^N^N))
                     (\y. f(chart_inv c y)) y)) %
         p3s_cgrad (metric_local atlas c g) (\y. f(chart_inv c y)) y) o
    (sndcart:real^(1,N)finite_sum->real^N)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV; o_THM;
                SNDCART_PASTECART; MFL_FIELD_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN DISCH_TAC THEN
    REWRITE_TAC[p2bx46_nfield] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\x:A. smooth_step((f:A->real) x - a) *
                          inv(p2bx46_ngrad atlas (g:A->real^N^N) f x)`;
                   `p2bx46_gradf atlas (g:A->real^N^N) f`;
                   `c:(A->bool)#(A->real^N)`; `y:real^N`] MCF_VREP_CMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`; `y:real^N`]
      P2BX46_GRADF_VREP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`;
                   `chart_inv (c:(A->bool)#(A->real^N)) y`] P2BX46_NGRAD_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART] THEN SIMP_TAC[];
    MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_SNDCART];
    REWRITE_TAC[] THEN MATCH_MP_TAC P2BX46_NFIELD_REP_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`;
                   `chart_inv (c:(A->bool)#(A->real^N)) y`] P2BX46_NGRAD_CHART) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]);;

(* ========================================================================= *)
(* The flow of the normalized gradient field; f grows along it               *)
(* with speed smooth_step(f - a) in [0,1], equal to 1 where f >= a + 1.      *)
(* ========================================================================= *)

let P2BX46_SPEED_BOUND = prove
 (`!s q. &0 <= s /\ s <= &1 ==> &0 <= s * inv q * q /\ s * inv q * q <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `q = &0` THEN
  ASM_SIMP_TAC[REAL_INV_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL; REAL_POS;
               GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RID]);;

let P2BX46_NFIELD_ESCAPE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K a.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x)
     ==> mcf_escape top atlas (p2bx46_nfield atlas g f a) (:real^1) f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`] P2BX46_SOL_ESCAPE) THEN
  ASM_REWRITE_TAC[mcf_escape] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a0:real^1`; `b0:real^1`] THEN DISCH_TAC THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
    RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CHART_AT]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] CMPF_LOCAL_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\y. lift((f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y)))
                              (at (SND c0 (x:A))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  REWRITE_TAC[p2bx46_nfield] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[DROP_CMUL; p2bx46_gradf; p2bx46_ngrad] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `\y. (f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y)`;
                 `SND (c0:(A->bool)#(A->real^N)) (x:A)`] P2BX46_CDF_CGRAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p3s_cdf]] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`smooth_step((f:A->real) x - a)`;
                 `lgrad2 (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N))
                         (\y. (f:A->real)(chart_inv c0 y)) (SND c0 (x:A))`]
    P2BX46_SPEED_BOUND) THEN
  REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN REAL_ARITH_TAC);;

let P2BX46_NFIELD_MCF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K a.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x)
     ==> mcf_hyp top atlas (p2bx46_nfield atlas g f a) (:real^1) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mcf_hyp] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_UNIV] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_NFIELD_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX46_NFIELD_ESCAPE THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]]);;

(* d/dr f(flow(s0 -> r) x) = smooth_step(f z - a) * inv q * q, z the flow point. *)

let P2BX46_NFLOW_FDERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K a s0 t x.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     x IN topspace top
     ==> ((\r. f(mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift r) x))
          has_real_derivative
          (smooth_step(f(mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift t) x)
                       - a) *
           inv(p2bx46_ngrad atlas g f
                 (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift t) x)) *
           p2bx46_ngrad atlas g f
             (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift t) x)))
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `a:real`] P2BX46_NFIELD_MCF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^N^N) f a) (lift s0) (lift t) x IN
    topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `p2bx46_nfield atlas (g:A->real^N^N) f a`; `(:real^1)`;
                   `f:A->real`] MCF_FLOW_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift s0`; `lift t`; `x:A`] o CONJUNCT1) THEN
    ASM_SIMP_TAC[IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC
   `z = mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^N^N) f a) (lift s0) (lift t) x` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`]
    RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2bx46_nfield atlas (g:A->real^N^N) f a`; `(:real^1)`;
                 `f:A->real`; `f:A->real`;
                 `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                       (z:A)) y)`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`;
                 `lift s0`; `lift t`; `x:A`] P2BX46_FLOW_CHART_FDERIV) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `w:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                        (FST(chart_at atlas z))` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2bx46_nfield atlas (g:A->real^N^N) f a t`; `z:A`] MCF_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2bx46_nfield] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
      (\y. lift((f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                (z:A)) y)))
      (at (SND(chart_at atlas z) z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                      (FST(chart_at atlas z))` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\y. lift((f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                (z:A)) y)))
      (at (SND(chart_at atlas z) z)) (p2bx46_gradf atlas (g:A->real^N^N) f z) =
    lift(p2bx46_ngrad atlas g f z)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LIFT_DROP] THEN AP_TERM_TAC THEN
    REWRITE_TAC[p2bx46_gradf; p2bx46_ngrad] THEN
    MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                          (FST(chart_at atlas z))`;
                   `metric_local atlas (chart_at atlas (z:A)) (g:A->real^N^N)`;
                   `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                         (z:A)) y)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) z`]
      P2BX46_CDF_CGRAD) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; REWRITE_TAC[p3s_cdf]];
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_ASSOC]]);;

(* A real lemma: speed in [0,1], equal to 1 above b, keeps u - r constant   *)
(* between s0 and t when u >= b at both ends of the motion.                 *)

let P2BX46_ODE_LEVEL = prove
 (`!(u:real->real) (D:real->real) b s0 t.
     (!r. (u has_real_derivative D r) (atreal r) /\ &0 <= D r /\ D r <= &1 /\
          (b <= u r ==> D r = &1)) /\
     b <= u s0 /\ b <= u s0 + (t - s0)
     ==> u t = u s0 + (t - s0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "d") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!r. r IN real_interval[min s0 t,max s0 t] ==> b <= (u:real->real) r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s0 <= t` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(u:real->real) s0` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL [`u:real->real`; `D:real->real`; `real_interval[s0,t]`;
                           `s0:real`; `r:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
      REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        USE_THEN "d" (fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      CONJ_TAC THENL [USE_THEN "d" (fun th -> REWRITE_TAC[th]); ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(u:real->real) s0 - s0 <= u r - r` MP_TAC THENL
       [MP_TAC(ISPECL [`\r. --((u:real->real) r - r)`; `\r. &1 - (D:real->real) r`;
                       `real_interval[t,s0]`; `r:real`; `s0:real`]
          HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
        REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
            SUBGOAL_THEN `&1 - (D:real->real) x = --(D x - &1)` SUBST1_TAC THENL
             [REAL_ARITH_TAC; ALL_TAC] THEN
            MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
            MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
            REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN USE_THEN "d" (fun th -> REWRITE_TAC[th]);
            ALL_TAC] THEN
          CONJ_TAC THENL
           [REPEAT STRIP_TAC THEN USE_THEN "d" (MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. (u:real->real) r - r`; `real_interval[min s0 t,max s0 t]`]
    HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `&0 = (D:real->real) r - &1` SUBST1_TAC THENL
     [USE_THEN "d" (MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN USE_THEN "d" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `s0:real` th) THEN MP_TAC(SPEC `t:real` th)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* The normalized flow maps the level f = u (u >= a + 1) to the level      *)
(* f = u + (t - s0) while that stays >= a + 1.                              *)

let P2BX46_NFLOW_LEVEL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K a s0 t x.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     x IN topspace top /\ a + &1 <= f x /\ a + &1 <= f x + (t - s0)
     ==> f(mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift t) x) =
         f x + (t - s0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `a:real`] P2BX46_NFIELD_MCF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2bx46_nfield atlas (g:A->real^N^N) f a`; `(:real^1)`;
                 `f:A->real`] MCF_FLOW_GEN) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in") (CONJUNCTS_THEN2 (LABEL_TAC "refl") (K ALL_TAC))) THEN
  MP_TAC(ISPECL
   [`\r. (f:A->real)(mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^N^N) f a)
                               (lift s0) (lift r) x)`;
    `\r. smooth_step((f:A->real)(mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^N^N) f a)
                                          (lift s0) (lift r) x) - a) *
         inv(p2bx46_ngrad atlas g f
               (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift r) x)) *
         p2bx46_ngrad atlas g f
           (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift r) x)`;
    `a + &1`; `s0:real`; `t:real`] P2BX46_ODE_LEVEL) THEN
  REWRITE_TAC[] THEN
  USE_THEN "refl" (MP_TAC o SPECL [`lift s0`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN
  SUBGOAL_THEN
   `mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^N^N) f a) (lift s0) (lift r) x IN
    topspace top`
  ASSUME_TAC THENL
   [USE_THEN "in" (MP_TAC o SPECL [`lift s0`; `lift r`; `x:A`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `z = mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^N^N) f a) (lift s0) (lift r) x` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `K:real`; `a:real`; `s0:real`; `r:real`; `x:A`]
      P2BX46_NFLOW_FDERIV) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`smooth_step((f:A->real) z - a)`; `p2bx46_ngrad atlas (g:A->real^N^N) f z`]
      P2BX46_SPEED_BOUND) THEN
    REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`smooth_step((f:A->real) z - a)`; `p2bx46_ngrad atlas (g:A->real^N^N) f z`]
      P2BX46_SPEED_BOUND) THEN
    REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN SIMP_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < p2bx46_ngrad atlas (g:A->real^N^N) f z` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_step((f:A->real) z - a) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LID; REAL_MUL_LINV; REAL_LT_IMP_NZ]]);;

(* ========================================================================= *)
(* Smooth maps into and out of regular level sets (leaves),                  *)
(* through the adapted charts (IMAGE e s INTER N, lvs_proj o e').           *)
(* ========================================================================= *)

let P2BX46_LEAF_INTO = prove
 (`!(topX:B topology) (atlasX:((B->bool)#(B->real^2))->bool) top
    (atlas:((A->bool)#(A->real^3))->bool) W f u D (F0:B->A).
     smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas top atlas /\
     open_in top W /\ lvs_regular atlas W f u /\
     open_in topX D /\ continuous_map (subtopology topX D,top) F0 /\
     mfd_smooth_map atlasX atlas D F0 /\ IMAGE F0 D SUBSET lvs_set W f u
     ==> mfd_smooth_map atlasX (lvs_atlas top atlas W f u) D F0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^2)`; `c':(A->bool)#(A->real^2)`] THEN
  REWRITE_TAC[LVS_ATLAS_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^3->bool`
    (X_CHOOSE_THEN `e:real^3->A` (X_CHOOSE_THEN `e':A->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LVS_DIFFEO_FACTS) THEN
  SUBGOAL_THEN `open_in topX {x:B | x IN D /\ (F0:B->A) x IN IMAGE (e:real^3->A) s}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `open_in (subtopology topX D)
                    {x:B | x IN D /\ (F0:B->A) x IN IMAGE (e:real^3->A) s}` MP_TAC THENL
     [MP_TAC(ISPECL [`F0:B->A`; `subtopology topX (D:B->bool)`; `top:A topology`;
                     `IMAGE (e:real^3->A) s`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`topX:B topology`; `D:B->bool`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  ABBREV_TAC `D' = {x:B | x IN D /\ (F0:B->A) x IN IMAGE (e:real^3->A) s}` THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^2))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `D':B->bool`; `IMAGE (e:real^3->A) s`; `F0:B->A`; `e':A->real^3`]
    MFD_SMOOTH_MAP_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LVS_EUCLIDEAN_ATLAS] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "D'" THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `D:B->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "D'" THEN SET_TAC[];
      MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN EXISTS_TAC `D:B->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "D'" THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
        try fst(dest_const t) = "mfd_diffeo" with Failure _ -> false)) (concl th))) THEN
      SIMP_TAC[mfd_diffeo]];
    ALL_TAC] THEN
  REWRITE_TAC[MFD_SMOOTH_MAP_INTO_EUCLIDEAN; mfd_smooth_on] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^2)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (SND (c:(B->bool)#(B->real^2)))
      {x | x IN FST c INTER D /\
           (F0:B->A) x IN IMAGE (e:real^3->A) s INTER lvs_set W f u} =
    IMAGE (SND c) (FST c INTER D')`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN EXPAND_TAC "D'" THEN REWRITE_TAC[FST] THEN
    UNDISCH_TAC `IMAGE (F0:B->A) D SUBSET lvs_set W f u` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SND] THEN
  SUBGOAL_THEN
   `(\x. lvs_proj((e':A->real^3) x)) o (F0:B->A) o chart_inv (c:(B->bool)#(B->real^2)) =
    lvs_proj o ((e' o F0) o chart_inv c)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LVS_PROJ_LINEAR] THEN
  MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^2))->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^2))->bool`;
                 `c:(B->bool)#(B->real^2)`] MFDM_CHART) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER]);;

let P2BX46_LEAF_FROM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (topY:C topology)
    (atlasY:((C->bool)#(C->real^M))->bool) W f u V (F0:A->C).
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topY atlasY /\
     open_in top W /\ lvs_regular atlas W f u /\
     open_in top V /\ continuous_map (subtopology top V,topY) F0 /\
     mfd_smooth_map atlas atlasY V F0
     ==> mfd_smooth_map (lvs_atlas top atlas W f u) atlasY (lvs_set W f u INTER V) F0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `topY:C topology`; `atlasY:((C->bool)#(C->real^M))->bool`;
                 `lvs_set W f u INTER V:A->bool`; `V:A->bool`;
                 `\x:A. x`; `F0:A->C`] MFD_SMOOTH_MAP_COMPOSE) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LVS_MANIFOLD] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `V:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    SET_TAC[];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID];
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN EXISTS_TAC `lvs_set W (f:A->real) u` THEN
    ASM_SIMP_TAC[LVS_INCLUSION_SMOOTH; INTER_SUBSET]]);;

(* An ambient diffeomorphism mapping one regular leaf onto another is a      *)
(* diffeomorphism of the leaves.                                             *)

let P2BX46_LEAF_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) f u1 u2 (F0:A->A) F1.
     smooth_manifold_atlas top atlas /\
     lvs_regular atlas (topspace top) f u1 /\ lvs_regular atlas (topspace top) f u2 /\
     mfd_diffeo top atlas (topspace top) top atlas (topspace top) F0 F1 /\
     IMAGE F0 (lvs_set (topspace top) f u1) SUBSET lvs_set (topspace top) f u2 /\
     IMAGE F1 (lvs_set (topspace top) f u2) SUBSET lvs_set (topspace top) f u1
     ==> mfd_diffeo (subtopology top (lvs_set (topspace top) f u1))
                    (lvs_atlas top atlas (topspace top) f u1) (lvs_set (topspace top) f u1)
                    (subtopology top (lvs_set (topspace top) f u2))
                    (lvs_atlas top atlas (topspace top) f u2) (lvs_set (topspace top) f u2)
                    F0 F1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f u1))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                     (topspace top) f u1) /\
    smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f u2))
                          (lvs_atlas top atlas (topspace top) f u2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LVS_MANIFOLD THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  ABBREV_TAC `N1 = lvs_set (topspace top) (f:A->real) u1` THEN
  ABBREV_TAC `N2 = lvs_set (topspace top) (f:A->real) u2` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBTOPOLOGY_TOPSPACE]) THEN
  SUBGOAL_THEN `continuous_map (top,top) (F0:A->A) /\ continuous_map (top,top) (F1:A->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphic_maps (top,top) ((F0:A->A),F1)` THEN
    SIMP_TAC[homeomorphic_maps];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N1:A->bool) SUBSET topspace top /\ (N2:A->bool) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN REWRITE_TAC[lvs_set] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphic_maps (subtopology top N1,subtopology top N2) ((F0:A->A),F1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAPS_SUBTOPOLOGIES_ALT THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology top N1,top) (F0:A->A) /\
                continuous_map (subtopology top N2,top) (F1:A->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphic_maps (subtopology top N1,subtopology top N2) ((F0:A->A),F1)` THEN
    REWRITE_TAC[homeomorphic_maps] THEN
    MESON_TAC[CONTINUOUS_MAP_INTO_FULLTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace (subtopology top N1) = (N1:A->bool) /\
                topspace (subtopology top N2) = (N2:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u1)
                   atlas N1 (F0:A->A) /\
    mfd_smooth_map (lvs_atlas top atlas (topspace top) f u2) atlas N2 (F1:A->A)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `topspace top:A->bool`; `f:A->real`; `u1:real`; `topspace top:A->bool`;
                     `F0:A->A`] P2BX46_LEAF_FROM) THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
      ASM_SIMP_TAC[SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `topspace top:A->bool`; `f:A->real`; `u2:real`; `topspace top:A->bool`;
                     `F1:A->A`] P2BX46_LEAF_FROM) THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
      ASM_SIMP_TAC[SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[homeomorphic_maps]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
  SUBGOAL_THEN `open_in (subtopology top N1) (N1:A->bool) /\
                open_in (subtopology top N2) (N2:A->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `subtopology top (N1:A->bool)` OPEN_IN_TOPSPACE);
      MP_TAC(ISPEC `subtopology top (N2:A->bool)` OPEN_IN_TOPSPACE)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC P2BX46_LEAF_INTO THENL
   [EXISTS_TAC `subtopology top (N1:A->bool)`; EXISTS_TAC `subtopology top (N2:A->bool)`] THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT]);;

(* ========================================================================= *)
(* Induced metrics are natural.  If an ambient diffeomorphism                *)
(* F0 maps the leaf N1 into the leaf N2, the pullback by F0 of the induced  *)
(* metric of N2 is the induced metric on N1 of the ambient pullback F0^* g; *)
(* hence F0 is an isometry of the leaves for these metrics.                  *)
(* ========================================================================= *)

let P2BX46_JAC_CHAIN_LOCAL = prove
 (`!(h1:real^M->real^N) (h2:real^N->real^P) (h:real^M->real^P) y U.
     open U /\ y IN U /\ h1 differentiable at y /\ h2 differentiable at (h1 y) /\
     (!z. z IN U ==> h z = h2(h1 z))
     ==> matrix(frechet_derivative h (at y)) =
         matrix(frechet_derivative h2 (at (h1 y))) ** matrix(frechet_derivative h1 (at y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(h has_derivative (frechet_derivative (h2:real^N->real^P) (at ((h1:real^M->real^N) y)) o
                       frechet_derivative h1 (at y))) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(h2:real^N->real^P) o (h1:real^M->real^N)` THEN
    UNDISCH_TAC `open(U:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  MATCH_MP_TAC MATRIX_COMPOSE THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]);;

let P2BX46_LEAF_PULLBACK_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f u1 u2 (F0:A->A) F1 p.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     lvs_regular atlas (topspace top) f u1 /\ lvs_regular atlas (topspace top) f u2 /\
     mfd_diffeo top atlas (topspace top) top atlas (topspace top) F0 F1 /\
     IMAGE F0 (lvs_set (topspace top) f u1) SUBSET lvs_set (topspace top) f u2 /\
     IMAGE F1 (lvs_set (topspace top) f u2) SUBSET lvs_set (topspace top) f u1 /\
     p IN lvs_set (topspace top) f u1
     ==> mfd_pullback_metric (lvs_atlas top atlas (topspace top) f u1)
                             (lvs_atlas top atlas (topspace top) f u2) F0
                             (lvs_metric top atlas g (topspace top) f u2) p =
         lvs_metric top atlas (mfd_pullback_metric atlas atlas F0 g) (topspace top) f u1 p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real`;
                 `u1:real`; `u2:real`; `F0:A->A`; `F1:A->A`] P2BX46_LEAF_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f u1))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                     (topspace top) f u1) /\
    smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f u2))
                          (lvs_atlas top atlas (topspace top) f u2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LVS_MANIFOLD THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  ABBREV_TAC `N1 = lvs_set (topspace top) (f:A->real) u1` THEN
  ABBREV_TAC `N2 = lvs_set (topspace top) (f:A->real) u2` THEN
  SUBGOAL_THEN `(N1:A->bool) SUBSET topspace top /\ (N2:A->bool) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN REWRITE_TAC[lvs_set] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace top /\ (F0:A->A) p IN N2 /\ F0 p IN topspace top`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace (subtopology top N1) = (N1:A->bool) /\
                topspace (subtopology top N2) = (N2:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o
    check (fun th -> can (find_term ((=) `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                                       (topspace top) f u1`)) (concl th))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> can (find_term ((=) `subtopology (subtopology top N1) (N1:A->bool)`))
                         (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o
    check (fun th -> can (find_term ((=) `top:A topology`)) (concl th) &&
                     not (can (find_term ((=) `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                                         (topspace top) f u1`)) (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBTOPOLOGY_TOPSPACE; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT]) THEN
  SUBGOAL_THEN `continuous_map (subtopology top N1,top) (F0:A->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_INTO_FULLTOPOLOGY]; ALL_TAC] THEN
  (* the charts *)
  MP_TAC(ISPECL [`subtopology top (N1:A->bool)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u1`;
                 `p:A`] CHART_AT) THEN
  MP_TAC(ISPECL [`subtopology top (N2:A->bool)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u2`;
                 `(F0:A->A) p`] CHART_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`] CHART_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(F0:A->A) p`]
    CHART_AT) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_pullback_metric; mpullback; o_DEF] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV) [lvs_metric] THEN BETA_TAC THEN
  REWRITE_TAC[lvs_jac] THEN
  ABBREV_TAC `c1 = chart_at (lvs_atlas top atlas (topspace top) f u1) (p:A)` THEN
  ABBREV_TAC `c2 = chart_at (lvs_atlas top atlas (topspace top) f u2) ((F0:A->A) p)` THEN
  ABBREV_TAC `d1 = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN
  ABBREV_TAC `d2 = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((F0:A->A) p)` THEN
  MP_TAC(ISPECL [`subtopology top (N1:A->bool)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u1`;
                 `c1:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (N2:A->bool)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u2`;
                 `c2:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `d1:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `d2:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  (* the induced metric of N2 in the chart c2, read through d2 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`; `f:A->real`; `u2:real`;
                 `c2:(A->bool)#(A->real^2)`; `d2:(A->bool)#(A->real^3)`;
                 `SND (c2:(A->bool)#(A->real^2)) ((F0:A->A) p)`] LVS_METRIC_LOCAL) THEN
  ASM_SIMP_TAC[OPEN_IN_TOPSPACE; FUN_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(F0:A->A) p`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  (* open sets in the chart of c1 *)
  SUBGOAL_THEN
   `open (IMAGE (SND (c1:(A->bool)#(A->real^2)))
           {x | x IN FST c1 INTER N1 /\ (F0:A->A) x IN FST (c2:(A->bool)#(A->real^2))})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`subtopology top (N1:A->bool)`;
      `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN
     `{x | x IN FST (c1:(A->bool)#(A->real^2)) INTER N1 /\
           (F0:A->A) x IN FST (c2:(A->bool)#(A->real^2))} =
      FST c1 INTER {x | x IN topspace (subtopology top N1) /\ F0 x IN FST c2}`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `subtopology top (N2:A->bool)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. SND (c2:(A->bool)#(A->real^2)) ((F0:A->A) (chart_inv (c1:(A->bool)#(A->real^2)) x)))
    differentiable at (SND c1 p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c1:(A->bool)#(A->real^2)))
                  {x | x IN FST c1 INTER N1 /\ (F0:A->A) x IN FST (c2:(A->bool)#(A->real^2))}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth_map (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                    (topspace top) f u1)
                     (lvs_atlas top atlas (topspace top) f u2) N1 (F0:A->A)` THEN
      REWRITE_TAC[mfd_smooth_map] THEN
      DISCH_THEN(MP_TAC o SPECL [`c1:(A->bool)#(A->real^2)`; `c2:(A->bool)#(A->real^2)`]) THEN
      ASM_REWRITE_TAC[o_DEF];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `p:A` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `topspace top:A->bool`; `f:A->real`; `u1:real`;
                 `c1:(A->bool)#(A->real^2)`; `d1:(A->bool)#(A->real^3)`] LVS_CHART_AMBIENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `topspace top:A->bool`; `f:A->real`; `u2:real`;
                 `c2:(A->bool)#(A->real^2)`; `d2:(A->bool)#(A->real^3)`] LVS_CHART_AMBIENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. SND (d2:(A->bool)#(A->real^3)) ((F0:A->A) (chart_inv (d1:(A->bool)#(A->real^3)) x)))
    differentiable at (SND d1 p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (d1:(A->bool)#(A->real^3)))
                  {x | x IN FST d1 INTER topspace top /\
                       (F0:A->A) x IN FST (d2:(A->bool)#(A->real^3))}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      SUBGOAL_THEN
       `{x | x IN FST (d1:(A->bool)#(A->real^3)) INTER topspace top /\
             (F0:A->A) x IN FST (d2:(A->bool)#(A->real^3))} =
        FST d1 INTER {x | x IN topspace top /\ F0 x IN FST d2}`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `homeomorphic_maps (top,top) ((F0:A->A),F1)` THEN
        SIMP_TAC[homeomorphic_maps]];
      UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^3))->bool) atlas
                     (topspace top) (F0:A->A)` THEN
      REWRITE_TAC[mfd_smooth_map] THEN
      DISCH_THEN(MP_TAC o SPECL [`d1:(A->bool)#(A->real^3)`; `d2:(A->bool)#(A->real^3)`]) THEN
      ASM_REWRITE_TAC[o_DEF];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `p:A` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the two chain rules *)
  SUBGOAL_THEN
   `matrix(frechet_derivative (\w. SND (d2:(A->bool)#(A->real^3))
                                     (chart_inv (c2:(A->bool)#(A->real^2)) w))
                              (at (SND c2 ((F0:A->A) p)))) **
    matrix(frechet_derivative (\x. SND c2 (F0 (chart_inv (c1:(A->bool)#(A->real^2)) x)))
                              (at (SND c1 p))) =
    matrix(frechet_derivative (\z. SND d2 (F0 (chart_inv c1 z))) (at (SND c1 p)))`
  (LABEL_TAC "ch2") THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`\x. SND (c2:(A->bool)#(A->real^2))
                          ((F0:A->A) (chart_inv (c1:(A->bool)#(A->real^2)) x))`;
                   `\w. SND (d2:(A->bool)#(A->real^3)) (chart_inv (c2:(A->bool)#(A->real^2)) w)`;
                   `\z. SND (d2:(A->bool)#(A->real^3))
                          ((F0:A->A) (chart_inv (c1:(A->bool)#(A->real^2)) z))`;
                   `SND (c1:(A->bool)#(A->real^2)) p`;
                   `IMAGE (SND (c1:(A->bool)#(A->real^2)))
                      {x | x IN FST c1 INTER N1 /\
                           (F0:A->A) x IN FST (c2:(A->bool)#(A->real^2))}`]
      P2BX46_JAC_CHAIN_LOCAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `p:A` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{w | w IN IMAGE (SND (c2:(A->bool)#(A->real^2))) (FST c2) /\
                       chart_inv c2 w IN FST (d2:(A->bool)#(A->real^3))}` THEN
      ASM_SIMP_TAC[IN_ELIM_THM; FUN_IN_IMAGE];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix(frechet_derivative (\x. SND (d2:(A->bool)#(A->real^3))
                                     ((F0:A->A) (chart_inv (d1:(A->bool)#(A->real^3)) x)))
                              (at (SND d1 p))) **
    matrix(frechet_derivative (\z. SND d1 (chart_inv (c1:(A->bool)#(A->real^2)) z))
                              (at (SND c1 p))) =
    matrix(frechet_derivative (\z. SND d2 (F0 (chart_inv c1 z))) (at (SND c1 p)))`
  (LABEL_TAC "ch1") THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`\z. SND (d1:(A->bool)#(A->real^3)) (chart_inv (c1:(A->bool)#(A->real^2)) z)`;
                   `\x. SND (d2:(A->bool)#(A->real^3))
                          ((F0:A->A) (chart_inv (d1:(A->bool)#(A->real^3)) x))`;
                   `\z. SND (d2:(A->bool)#(A->real^3))
                          ((F0:A->A) (chart_inv (c1:(A->bool)#(A->real^2)) z))`;
                   `SND (c1:(A->bool)#(A->real^2)) p`;
                   `{w | w IN IMAGE (SND (c1:(A->bool)#(A->real^2))) (FST c1) /\
                         chart_inv c1 w IN FST (d1:(A->bool)#(A->real^3))}`]
      P2BX46_JAC_CHAIN_LOCAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[IN_ELIM_THM; FUN_IN_IMAGE];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{w | w IN IMAGE (SND (c1:(A->bool)#(A->real^2))) (FST c1) /\
                       chart_inv c1 w IN FST (d1:(A->bool)#(A->real^3))}` THEN
      ASM_SIMP_TAC[IN_ELIM_THM; FUN_IN_IMAGE];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `M = matrix(frechet_derivative
                   (\z. SND (d2:(A->bool)#(A->real^3))
                          ((F0:A->A) (chart_inv (c1:(A->bool)#(A->real^2)) z))) (at (SND c1 p)))` THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `transp(M:real^2^3) ** g((F0:A->A) p) ** M` THEN
  CONJ_TAC THENL
   [USE_THEN "ch2" (fun th -> REWRITE_TAC[GSYM th; MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);
    USE_THEN "ch1" (fun th -> REWRITE_TAC[GSYM th; MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC])]);;

let P2BX46_LEAF_ISOMETRY = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f u1 u2 (F0:A->A) F1.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     lvs_regular atlas (topspace top) f u1 /\ lvs_regular atlas (topspace top) f u2 /\
     mfd_diffeo top atlas (topspace top) top atlas (topspace top) F0 F1 /\
     IMAGE F0 (lvs_set (topspace top) f u1) SUBSET lvs_set (topspace top) f u2 /\
     IMAGE F1 (lvs_set (topspace top) f u2) SUBSET lvs_set (topspace top) f u1
     ==> mfd_isometry (subtopology top (lvs_set (topspace top) f u1),
                       lvs_atlas top atlas (topspace top) f u1)
                      (lvs_metric top atlas (mfd_pullback_metric atlas atlas F0 g)
                                  (topspace top) f u1)
                      (subtopology top (lvs_set (topspace top) f u2),
                       lvs_atlas top atlas (topspace top) f u2)
                      (lvs_metric top atlas g (topspace top) f u2) F0 F1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real`;
                 `u1:real`; `u2:real`; `F0:A->A`; `F1:A->A`] P2BX46_LEAF_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f u1))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                     (topspace top) f u1) /\
    smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f u2))
                          (lvs_atlas top atlas (topspace top) f u2) /\
    riemannian_metric (lvs_atlas top atlas (topspace top) f u2)
                      (lvs_metric top atlas (g:A->real^3^3) (topspace top) f u2) /\
    topspace (subtopology top (lvs_set (topspace top) f u1)) = lvs_set (topspace top) f u1 /\
    topspace (subtopology top (lvs_set (topspace top) f u2)) = lvs_set (topspace top) f u2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_MANIFOLD; LVS_RIEMANNIAN; OPEN_IN_TOPSPACE; TOPSPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[lvs_set] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) u2)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u2`;
                 `subtopology top (lvs_set (topspace top) (f:A->real) u1)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u1`;
                 `F1:A->A`; `F0:A->A`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) f u2`]
    MTR_PULLBACK_ISOMETRY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC MFD_ISOMETRY_INVERSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MTR_ISOMETRY_CONG THEN
  EXISTS_TAC `mfd_pullback_metric (lvs_atlas top atlas (topspace top) f u1)
                (lvs_atlas top atlas (topspace top) f u2) (F0:A->A)
                (lvs_metric top atlas (g:A->real^3^3) (topspace top) f u2)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX46_LEAF_PULLBACK_EQ THEN
  EXISTS_TAC `F1:A->A` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The normalized flow stretches tangent vectors of far level                *)
(* sets.  For X = smooth_step(f - a) grad f / |grad f|^2 and w tangent to   *)
(* the level set at x, s -> |d F_s (w)|^2 has derivative                    *)
(* (L_X g)(W,W) = phi (|W|^2 - 2 Ric(W,W)) >= 0, W = d F_s (w), because     *)
(* df(W) = 0 kills the term with d phi and Ric <= R/2 g, R <= 1.            *)
(* ========================================================================= *)

let P2BX46_FD_CHAIN_LOCAL = prove
 (`!(h1:real^M->real^N) (h2:real^N->real^P) (h:real^M->real^P) y U w.
     open U /\ y IN U /\ h1 differentiable at y /\ h2 differentiable at (h1 y) /\
     (!z. z IN U ==> h z = h2(h1 z))
     ==> frechet_derivative h (at y) w =
         frechet_derivative h2 (at (h1 y)) (frechet_derivative h1 (at y) w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(h has_derivative (frechet_derivative (h2:real^N->real^P) (at ((h1:real^M->real^N) y)) o
                       frechet_derivative h1 (at y))) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(h2:real^N->real^P) o (h1:real^M->real^N)` THEN
    UNDISCH_TAC `open(U:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM]);;

let P2BX46_MPULLBACK_ID_LOCAL = prove
 (`!(k:real^N->real^N) (G:real^N->real^N^N) s y.
     open s /\ y IN s /\ (!w. w IN s ==> k w = w) ==> mpullback k G y = G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative (k:real^N->real^N) (at y) = (\x. x)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    UNDISCH_TAC `open(s:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(y:real^N,d) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->real^N) y = y` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[mpullback; MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P2BX46_QF_EXPAND = prove
 (`!(M:real^N^N) w.
     w dot (M ** w) =
     sum(1..dimindex(:N)) (\i. w$i * sum(1..dimindex(:N)) (\j. M$i$j * w$j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA]);;

let P2BX46_QF_DERIV = prove
 (`!(P:real->real^N^N) (D:real^N^N) w t.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> ((\s. P s$i$j) has_real_derivative D$i$j) (atreal t))
     ==> ((\s. w dot (P s ** w)) has_real_derivative (w dot (D ** w))) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2BX46_QF_EXPAND] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN ASM_SIMP_TAC[]);;

(* The quadratic form of llie. *)

let P2BX46_LLIE_QF = prove
 (`!(X:real^N->real^N) (G:real^N->real^N^N) y w.
     linear(frechet_derivative X (at y))
     ==> w dot (llie X G y ** w) =
         w dot (mderiv G y (X y) ** w) +
         frechet_derivative X (at y) w dot (G y ** w) +
         w dot (G y ** frechet_derivative X (at y) w)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[llie; MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]));;

(* Product rule for llie, as a quadratic form. *)

let P2BX46_LLIE_SMUL_QF = prove
 (`!(ph:real^N->real) (X:real^N->real^N) (G:real^N->real^N^N) y w.
     (\z. lift(ph z)) differentiable at y /\ X differentiable at y /\
     ((vectorize:real^N^N->real^(N,N)finite_prod) o G) differentiable at y
     ==> w dot (llie (\z. ph z % X z) G y ** w) =
         ph y * (w dot (llie X G y ** w)) +
         p3s_cdf ph y w * (X y dot (G y ** w) + w dot (G y ** X y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (X:real^N->real^N) (at y)) /\
    linear(frechet_derivative (\z. lift((ph:real^N->real) z)) (at y)) /\
    linear(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G) (at y))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (X:real^N->real^N) (at y)` THEN
  ABBREV_TAC `dp = frechet_derivative (\z. lift((ph:real^N->real) z)) (at y)` THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. (ph:real^N->real) z % (X:real^N->real^N) z) (at y) =
    (\h. ph y % (L:real^N->real^N) h + drop((dp:real^N->real^1) h) % X y)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_MUL_AT THEN
    MAP_EVERY EXPAND_TAC ["L"; "dp"] THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(\h. (ph:real^N->real) y % (L:real^N->real^N) h +
               drop((dp:real^N->real^1) h) % (X:real^N->real^N) y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[linear] THEN
    REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear(dp:real^N->real^1)`);
                MATCH_MP LINEAR_CMUL (ASSUME `linear(dp:real^N->real^1)`);
                MATCH_MP LINEAR_ADD (ASSUME `linear(L:real^N->real^N)`);
                MATCH_MP LINEAR_CMUL (ASSUME `linear(L:real^N->real^N)`)] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL] THEN CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (ph:real^N->real) z % (X:real^N->real^N) z`; `G:real^N->real^N^N`;
                 `y:real^N`; `w:real^N`] P2BX46_LLIE_QF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`]
    P2BX46_LLIE_QF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mderiv] THEN
  REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME
    `linear(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                (G:real^N->real^N^N)) (at (y:real^N)))`)] THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIX_VECTOR_LMUL; p3s_cdf] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_LADD; DOT_RADD; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_RMUL] THEN
  REAL_ARITH_TAC);;

(* The chart representative of the normalized field. *)

let P2BX46_NFIELD_VREP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f a c t y.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> mfl_field atlas (p2bx46_nfield atlas g f a) c (pastecart t y) =
         (smooth_step(f(chart_inv c y) - a) *
          inv(lgrad2 (metric_local atlas c g) (\z. f(chart_inv c z)) y)) %
         p3s_cgrad (metric_local atlas c g) (\z. f(chart_inv c z)) y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[MFL_FIELD_PASTECART; p2bx46_nfield] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\x:A. smooth_step((f:A->real) x - a) *
                        inv(p2bx46_ngrad atlas (g:A->real^N^N) f x)`;
                 `p2bx46_gradf atlas (g:A->real^N^N) f`;
                 `c:(A->bool)#(A->real^N)`; `y:real^N`] MCF_VREP_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`; `y:real^N`]
    P2BX46_GRADF_VREP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] P2BX46_NGRAD_CHART) THEN
  ASM_SIMP_TAC[]);;

let P2BX46_NPHI_DIFF = prove
 (`!U (G:real^N->real^N^N) fc a y.
     metric_field U G /\ smooth_map_on U (\z. lift(fc z)) /\ y IN U /\ &0 < lgrad2 G fc y
     ==> (\z. lift(smooth_step(fc z - a) * inv(lgrad2 G fc z))) differentiable at y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\y. lift(lgrad2 (G:real^N->real^N^N) fc y))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BS_LGRAD2_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W = {y:real^N | y IN U /\ lift(lgrad2 (G:real^N->real^N^N) fc y) IN
                                       {z:real^1 | &0 < drop z}}` THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ W SUBSET U /\ (y:real^N) IN W /\
                !y. y IN W ==> &0 < lgrad2 (G:real^N->real^N^N) fc y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[drop; REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP];
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\z. lift(smooth_step((fc:real^N->real) z - a) * inv(lgrad2 (G:real^N->real^N^N) fc z))) =
    (\z. drop(lift(smooth_step(drop(lift(fc z) - lift a)))) %
         lift(inv(drop(lift(lgrad2 G fc z)))))`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP; DROP_SUB; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[REAL_LT_IMP_NZ]]]);;

(* On a vector w with df(w) = 0 the Lie derivative of g along the normalized *)
(* field is phi (g - 2 Ric)(w,w), phi = smooth_step(f - a) / |grad f|^2.     *)

let P2BX46_NFIELD_LLIE_QF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f a c t y w.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\ y IN IMAGE (SND c) (FST c) /\
     &0 < lgrad2 (metric_local atlas c g) (\z. f(chart_inv c z)) y /\
     p3s_cdf (\z. f(chart_inv c z)) y w = &0
     ==> w dot (llie (\z. mfl_field atlas (p2bx46_nfield atlas g f a) c (pastecart t z))
                     (metric_local atlas c g) y ** w) =
         (smooth_step(f(chart_inv c y) - a) *
          inv(lgrad2 (metric_local atlas c g) (\z. f(chart_inv c z)) y)) *
         (w dot (metric_local atlas c g y ** w) -
          &2 * lricci (metric_local atlas c g) y w w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\z. p3s_cgrad (G:real^N->real^N^N)
                                   (\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_CGRAD_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(smooth_step((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) - a) *
               inv(lgrad2 (G:real^N->real^N^N) (\z. f(chart_inv c z)) z)))
    differentiable at y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)`; `a:real`;
                   `y:real^N`] P2BX46_NPHI_DIFF) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `llie (\z. mfl_field atlas (p2bx46_nfield atlas (g:A->real^N^N) f a)
                        (c:(A->bool)#(A->real^N)) (pastecart t z)) G y =
    llie (\z. (smooth_step(f(chart_inv c z) - a) * inv(lgrad2 G (\z. f(chart_inv c z)) z)) %
              p3s_cgrad G (\z. f(chart_inv c z)) z) G y`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX46_LLIE_LOCAL THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `a:real`; `c:(A->bool)#(A->real^N)`;
                     `t:real^1`; `z:real^N`] P2BX46_NFIELD_VREP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z. (smooth_step((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) - a) *
            inv(lgrad2 (G:real^N->real^N^N) (\z. f(chart_inv c z)) z)) %
           p3s_cgrad G (\z. f(chart_inv c z)) z) =
      (\z. drop((\z. lift(smooth_step(f(chart_inv c z) - a) *
                            inv(lgrad2 G (\z. f(chart_inv c z)) z))) z) %
           (\z. p3s_cgrad G (\z. f(chart_inv c z)) z) z)`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_MUL_AT THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. smooth_step((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) - a) *
                      inv(lgrad2 (G:real^N->real^N^N) (\z. f(chart_inv c z)) z)`;
                 `\z. p3s_cgrad (G:real^N->real^N^N)
                                (\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)) z`;
                 `G:real^N->real^N^N`; `y:real^N`; `w:real^N`] P2BX46_LLIE_SMUL_QF) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `w dot ((G:real^N->real^N^N) y **
           p3s_cgrad G (\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)) y) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)`; `y:real^N`;
                   `w:real^N`] P3S_CGRAD_DOT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3s_cgrad (G:real^N->real^N^N) (\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)) y
    dot (G y ** w) = &0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(G:real^N->real^N^N) y`;
                   `p3s_cgrad (G:real^N->real^N^N)
                              (\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)) y`;
                   `w:real^N`] DOT_MATRIX_TRANSP_LMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_LID; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `c:(A->bool)#(A->real^N)`; `y:real^N`] P2BX46_LLIE_SOLITON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_LMUL; DOT_RSUB; DOT_RMUL] THEN
  REWRITE_TAC[pde_lricci_matrix] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`; `w:real^N`]
    P2BX46_LRIC_MATRIX_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Vectors of the leaf Jacobian are tangent: df(lvs_jac v) = 0. *)

let P2BX46_LVS_JAC_TANGENT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u x v.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     x IN lvs_set W f u
     ==> p3s_cdf (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x)
                 (lvs_jac top atlas W f u x v) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top (lvs_set W f u))
                  (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u)` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_MANIFOLD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (x:A) IN W /\ (f:A->real) x = u` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set W f u` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W (f:A->real) u)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`; `x:A`] CHART_AT) THEN
  ASM_SIMP_TAC[LVS_TOPSPACE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lvs_jac; p3s_cdf] THEN
  ABBREV_TAC `c = chart_at (lvs_atlas top atlas W f u) (x:A)` THEN
  ABBREV_TAC `d = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W (f:A->real) u)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `d:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`;
                 `c:(A->bool)#(A->real^2)`; `d:(A->bool)#(A->real^3)`] LVS_CHART_AMBIENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST (c:(A->bool)#(A->real^2)) SUBSET lvs_set W (f:A->real) u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (lvs_set W (f:A->real) u)`;
                   `FST (c:(A->bool)#(A->real^2))`] OPEN_IN_SUBSET) THEN
    ASM_SIMP_TAC[LVS_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND (d:(A->bool)#(A->real^3))) (FST d INTER W))
                  (\y. lift((f:A->real)(chart_inv d y)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `lvs_regular atlas W (f:A->real) u` THEN
    REWRITE_TAC[lvs_regular; mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o SPEC `d:(A->bool)#(A->real^3)` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND (d:(A->bool)#(A->real^3))) (FST d INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w. SND (d:(A->bool)#(A->real^3)) (chart_inv (c:(A->bool)#(A->real^2)) w)`;
    `\y. lift((f:A->real)(chart_inv (d:(A->bool)#(A->real^3)) y))`;
    `\w:real^2. lift u`;
    `SND (c:(A->bool)#(A->real^2)) x`;
    `{w | w IN IMAGE (SND (c:(A->bool)#(A->real^2))) (FST c) /\
          chart_inv c w IN FST (d:(A->bool)#(A->real^3))}`;
    `v:real^2`] P2BX46_FD_CHAIN_LOCAL) THEN
  ASM_SIMP_TAC[FRECHET_DERIVATIVE_CONST_AT] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{w | w IN IMAGE (SND (c:(A->bool)#(A->real^2))) (FST c) /\
                       chart_inv c w IN FST (d:(A->bool)#(A->real^3))}` THEN
      ASM_SIMP_TAC[IN_ELIM_THM; FUN_IN_IMAGE];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (SND (d:(A->bool)#(A->real^3))) (FST d INTER W)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^2)) z IN lvs_set W (f:A->real) u` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN SIMP_TAC[]]];
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[DROP_VEC]]);;

(* A smooth self-map shifting f by a constant near x preserves df = 0. *)

let P2BX46_SHIFT_TANGENT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (F0:A->A) (f:A->real) x V k w.
     smooth_manifold_atlas top atlas /\ open_in top V /\ x IN V /\
     continuous_map (top,top) F0 /\ mfd_smooth_map atlas atlas (topspace top) F0 /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     (!z. z IN V ==> f(F0 z) = f z + k) /\
     p3s_cdf (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) w = &0
     ==> p3s_cdf (\y. f(chart_inv (chart_at atlas (F0 x)) y)) (SND(chart_at atlas (F0 x)) (F0 x))
           (matrix(frechet_derivative
                     (SND(chart_at atlas (F0 x)) o F0 o chart_inv(chart_at atlas x))
                     (at (SND(chart_at atlas x) x))) ** w) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (F0:A->A) x IN topspace top` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `continuous_map (top,top) (F0:A->A)` THEN REWRITE_TAC[continuous_map] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(F0:A->A) x`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `c1 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((F0:A->A) x)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c1:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST (c0:(A->bool)#(A->real^N)) INTER topspace top = FST c0 /\
                FST (c1:(A->bool)#(A->real^N)) INTER topspace top = FST c1`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`]; ALL_TAC] THEN
  ABBREV_TAC `U = IMAGE (SND (c0:(A->bool)#(A->real^N)))
                    {z | z IN FST c0 INTER V /\ (F0:A->A) z IN FST (c1:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN
     `{z | z IN FST (c0:(A->bool)#(A->real^N)) INTER V /\
           (F0:A->A) z IN FST (c1:(A->bool)#(A->real^N))} =
      (FST c0 INTER V) INTER {z | z IN topspace top /\ F0 z IN FST c1}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c0:(A->bool)#(A->real^N)) x IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (SND (c1:(A->bool)#(A->real^N)) o (F0:A->A) o
                     chart_inv (c0:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N)))
                  {z | z IN FST c0 INTER topspace top /\
                       (F0:A->A) z IN FST (c1:(A->bool)#(A->real^N))}` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "U" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
      UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool) atlas
                     (topspace top) (F0:A->A)` THEN
      REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1))
                  (\y. lift((f:A->real)(chart_inv c1 y))) /\
    smooth_map_on (IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0))
                  (\y. lift((f:A->real)(chart_inv c0 y)))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                   (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `c0:(A->bool)#(A->real^N)` th) THEN
                         MP_TAC(SPEC `c1:(A->bool)#(A->real^N)` th)) THEN
    ASM_REWRITE_TAC[o_DEF] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(SND (c1:(A->bool)#(A->real^N)) o (F0:A->A) o chart_inv (c0:(A->bool)#(A->real^N)))
      (SND c0 x) = SND c1 (F0 x)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(SND (c1:(A->bool)#(A->real^N)) o (F0:A->A) o chart_inv (c0:(A->bool)#(A->real^N)))
      differentiable at (SND c0 x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`SND (c1:(A->bool)#(A->real^N)) o (F0:A->A) o chart_inv (c0:(A->bool)#(A->real^N))`;
    `\y. lift((f:A->real)(chart_inv (c1:(A->bool)#(A->real^N)) y))`;
    `\y. lift((f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y) + k)`;
    `SND (c0:(A->bool)#(A->real^N)) x`; `U:real^N->bool`; `w:real^N`] P2BX46_FD_CHAIN_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1)` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      EXPAND_TAC "U" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. lift((f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y) + k))
                       (at (SND c0 x)) =
    frechet_derivative (\y. lift(f(chart_inv c0 y))) (at (SND c0 x))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[LIFT_ADD] THEN
    MP_TAC(ISPECL [`\y. lift((f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y))`;
                   `frechet_derivative (\y. lift((f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y)))
                                       (at (SND c0 x))`;
                   `\y:real^N. lift k`; `\h:real^N. vec 0:real^1`;
                   `at (SND (c0:(A->bool)#(A->real^N)) x)`] HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_RID; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (SND (c1:(A->bool)#(A->real^N)) o (F0:A->A) o
                               chart_inv (c0:(A->bool)#(A->real^N))) (at (SND c0 x)))`
  ASSUME_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  UNDISCH_TAC `p3s_cdf (\y. (f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y)) (SND c0 x) w = &0` THEN
  REWRITE_TAC[p3s_cdf] THEN ASM_REWRITE_TAC[]);;

(* The derivative of s -> |d F_s(w)|^2 is >= 0 for w tangent to the level set. *)

let P2BX46_NFLOW_QF_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K a s0 t x w.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top /\ a + &1 <= f x ==> mfd_scalar atlas g x <= &1) /\
     x IN topspace top /\ a + &1 < f x /\ s0 <= t /\
     p3s_cdf (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) w = &0
     ==> ?D. ((\s. w dot (mfd_pullback_metric atlas atlas
                            (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift s))
                            g x ** w)) has_real_derivative D) (atreal t) /\
             &0 <= D`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`] P2BX46_NFIELD_MCF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p2bx46_nfield atlas (g:A->real^3^3) f a`; `(:real^1)`;
                 `f:A->real`] MCF_FLOW_GEN) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in") (CONJUNCTS_THEN2 (LABEL_TAC "refl")
    (CONJUNCTS_THEN2 (LABEL_TAC "coc") (CONJUNCTS_THEN2 (LABEL_TAC "dif") (K ALL_TAC))))) THEN
  EXISTS_TAC
   `w dot (mpullback
     (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool)
             (mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                       (lift s0) (lift t) (x:A))) o
      mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift t) o
      chart_inv (chart_at atlas x))
     (llie (\z. mfl_field atlas (p2bx46_nfield atlas g f a)
                  (chart_at atlas (mfl_flow top atlas (p2bx46_nfield atlas g f a)
                                            (lift s0) (lift t) x))
                  (pastecart (lift t) z))
           (metric_local atlas (chart_at atlas (mfl_flow top atlas (p2bx46_nfield atlas g f a)
                                                         (lift s0) (lift t) x)) g))
     (SND (chart_at atlas x) x) ** (w:real^3))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_QF_DERIV THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `p2bx46_nfield atlas (g:A->real^3^3) f a`; `(:real^1)`; `f:A->real`;
                   `g:A->real^3^3`; `lift s0`; `t:real`; `x:A`; `i:num`; `j:num`]
      P2BX46_PULLBACK_STATIC_DERIV) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  (* the flow map and its properties *)
  ABBREV_TAC `F1 = mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                            (lift s0) (lift t)` THEN
  SUBGOAL_THEN `(F1:A->A) x IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "F1" THEN USE_THEN "in" (MP_TAC o SPECL [`lift s0`; `lift t`; `x:A`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN topspace top /\ a + &1 <= f z ==> (f:A->real)((F1:A->A) z) = f z + (t - s0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN STRIP_TAC THEN EXPAND_TAC "F1" THEN
    MATCH_MP_TAC P2BX46_NFLOW_LEVEL THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real)((F1:A->A) x) = f x + (t - s0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,top) (F1:A->A) /\
                mfd_smooth_map (atlas:((A->bool)#(A->real^3))->bool) atlas
                               (topspace top) (F1:A->A)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "F1" THEN USE_THEN "dif" (MP_TAC o SPECL [`lift s0`; `lift t`]) THEN
    REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_TOPSPACE; homeomorphic_maps] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* tangency at the image point *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `F1:A->A`;
                 `f:A->real`; `x:A`; `{z:A | z IN topspace top /\ f z > a + &1}`;
                 `t - s0`; `w:real^3`] P2BX46_SHIFT_TANGENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; real_gt] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `f:A->real`] P2BX46_F_CONTINUOUS) THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LT; real_gt] THEN SIMP_TAC[];
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(F1:A->A) x`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `c1 = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((F1:A->A) x)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c0:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mpullback; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  SUBGOAL_THEN
   `(SND (c1:(A->bool)#(A->real^3)) o (F1:A->A) o chart_inv (c0:(A->bool)#(A->real^3)))
      (SND c0 x) = SND c1 (F1 x)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  ABBREV_TAC `W = matrix(frechet_derivative
                    (SND (c1:(A->bool)#(A->real^3)) o (F1:A->A) o
                     chart_inv (c0:(A->bool)#(A->real^3))) (at (SND c0 x))) ** (w:real^3)` THEN
  (* the Lie derivative on W *)
  SUBGOAL_THEN `&0 < lgrad2 (metric_local atlas (c1:(A->bool)#(A->real^3)) (g:A->real^3^3))
                           (\z. (f:A->real)(chart_inv c1 z)) (SND c1 ((F1:A->A) x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < p2bx46_ngrad atlas (g:A->real^3^3) f ((F1:A->A) x)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[p2bx46_ngrad]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `a:real`; `c1:(A->bool)#(A->real^3)`; `lift t`;
                 `SND (c1:(A->bool)#(A->real^3)) ((F1:A->A) x)`; `W:real^3`]
    P2BX46_NFIELD_LLIE_QF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SMOOTH_STEP_BOUNDS; REAL_LE_INV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas (c1:(A->bool)#(A->real^3)) (g:A->real^3^3)
                  (SND c1 ((F1:A->A) x)) = g (F1 x)` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lricci (metric_local atlas (c1:(A->bool)#(A->real^3)) (g:A->real^3^3))
                       (SND c1 ((F1:A->A) x)) W W = mfd_ricci atlas g (F1 x) W W`
  SUBST1_TAC THENL [EXPAND_TAC "c1" THEN REWRITE_TAC[mfd_ricci]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= W dot ((g:A->real^3^3) ((F1:A->A) x) ** W)` ASSUME_TAC THENL
   [ASM_CASES_TAC `W:real^3 = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `c1:(A->bool)#(A->real^3)`] RFA_SH_CHART_DATA) THEN
    ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SND (c1:(A->bool)#(A->real^3)) ((F1:A->A) x)`) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `W:real^3` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(F1:A->A) x`; `W:real^3`] P2BX46_MFD_RIC_LE_HALF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((F1:A->A) x) <= &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((F1:A->A) x) * (W dot (g (F1 x) ** W)) <=
                &1 * (W dot (g (F1 x) ** W))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= W dot ((g:A->real^3^3) ((F1:A->A) x) ** W)` THEN
  REAL_ARITH_TAC);;

(* Hence |d F_r(w)|^2 >= |w|^2 for r >= s0, F_r the flow from s0 to r. *)

let P2BX46_NFLOW_STRETCH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K a s0 r x w.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top /\ a + &1 <= f x ==> mfd_scalar atlas g x <= &1) /\
     x IN topspace top /\ a + &1 < f x /\ s0 <= r /\
     p3s_cdf (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) w = &0
     ==> w dot (g x ** w) <=
         w dot (mfd_pullback_metric atlas atlas
                  (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift r)) g x ** w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`] P2BX46_NFIELD_MCF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p2bx46_nfield atlas (g:A->real^3^3) f a`; `(:real^1)`;
                 `f:A->real`] MCF_FLOW_GEN) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in") (CONJUNCTS_THEN2 (LABEL_TAC "refl") (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `mfd_pullback_metric atlas atlas
      (mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a) (lift s0) (lift s0)) g x =
    g x`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THENL
   [REWRITE_TAC[mfd_pullback_metric] THEN
    USE_THEN "refl" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN topspace top`)]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3) (SND c x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BX46_MPULLBACK_ID_LOCAL THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) z IN topspace top` ASSUME_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
      USE_THEN "refl" (fun th -> ASM_SIMP_TAC[th]);
      EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?D. !s. s IN real_interval[s0,r]
            ==> ((\s. w dot (mfd_pullback_metric atlas atlas
                         (mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                                   (lift s0) (lift s)) g x ** w))
                 has_real_derivative D s) (atreal s) /\ &0 <= D s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX46_NFLOW_QF_DERIV THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. w dot (mfd_pullback_metric atlas atlas
                         (mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                                   (lift s0) (lift s)) g x ** w)`;
                 `D:real->real`; `real_interval[s0,r]`; `s0:real`; `r:real`]
    HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN CONJ_TAC THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

(* The same on a far leaf, for its induced metrics. *)

let P2BX46_LEAF_STRETCH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K a s0 r u y v.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top /\ a + &1 <= f x ==> mfd_scalar atlas g x <= &1) /\
     lvs_regular atlas (topspace top) f u /\ a + &1 < u /\ s0 <= r /\
     y IN lvs_set (topspace top) f u
     ==> v dot (lvs_metric top atlas g (topspace top) f u y ** v) <=
         &1 * (v dot (lvs_metric top atlas
                        (mfd_pullback_metric atlas atlas
                           (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift s0) (lift r)) g)
                        (topspace top) f u y ** v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (f:A->real) y = u` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN lvs_set (topspace top) f u` THEN
    REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `topspace top:A->bool`; `f:A->real`; `u:real`; `y:A`] LVS_JAC_FACTS) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN STRIP_TAC THEN
  REWRITE_TAC[lvs_metric; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  MATCH_MP_TAC P2BX46_NFLOW_STRETCH THEN EXISTS_TAC `K:real` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX46_LVS_JAC_TANGENT THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]);;

(* ========================================================================= *)
(* Area of far spheres and the Gauss-Bonnet contradiction.                   *)
(* The flow back from level v to level u0 maps a sphere S of N_v onto a      *)
(* sphere D of N_u0 with Area(D) <= Area(S) (tangential stretching), and on  *)
(* N_u0 the intrinsic curvature is <= 2 k0 with k0 < 1/2; Gauss-Bonnet then  *)
(* gives 4 pi <= k0 Area(D) <= k0 (8 pi + delta) < 4 pi.                     *)
(* ========================================================================= *)

let P2BX46_COMPACT_LT_BOUND = prove
 (`!top (h:A->real) S b.
     continuous_map (top,euclideanreal) h /\ compact_in top S /\ (!x. x IN S ==> h x < b)
     ==> ?c. c < b /\ !x. x IN S ==> h x <= c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `S:A->bool = {}` THENL
   [EXISTS_TAC `b - &1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (h:A->real) S` REAL_COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; real_compact_def] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(h:A->real) x0` THEN ASM_SIMP_TAC[]]);;

let P2BX46_DIFFEO_IMAGE_COMPACT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^M))->bool) W
    (top':B topology) (atlas':((B->bool)#(B->real^N))->bool) W' psi psi'.
     compact_in top W /\ mfd_diffeo top atlas W top' atlas' W' psi psi'
     ==> compact_in top' W'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace top /\ (W':B->bool) SUBSET topspace top'`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP th) THEN
                       ASSUME_TAC(MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP th)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
  SUBGOAL_THEN `topspace top INTER (W:A->bool) = W /\ topspace top' INTER (W':B->bool) = W'`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `topspace top INTER (W:A->bool) = W`;
                              ASSUME `topspace top' INTER (W':B->bool) = W'`]) THEN
  SUBGOAL_THEN `compact_in (subtopology top' W') (IMAGE (psi:A->B) W)` MP_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL];
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN SIMP_TAC[]]);;

(* On a compact regular leaf with R_N < 1 everywhere, R_N <= 2 k0, k0 < 1/2. *)

let P2BX46_LEAF_K0 = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f u.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     lvs_regular atlas (topspace top) f u /\ compact_in top (lvs_set (topspace top) f u) /\
     (!x. x IN lvs_set (topspace top) f u
          ==> mfd_scalar (lvs_atlas top atlas (topspace top) f u)
                         (lvs_metric top atlas g (topspace top) f u) x < &1)
     ==> ?k0. &0 < k0 /\ k0 < inv(&2) /\
              !x. x IN lvs_set (topspace top) f u
                  ==> mfd_scalar (lvs_atlas top atlas (topspace top) f u)
                                 (lvs_metric top atlas g (topspace top) f u) x <= &2 * k0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) u)`;
                 `mfd_scalar (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                        (topspace top) f u)
                             (lvs_metric top atlas (g:A->real^3^3) (topspace top) f u)`;
                 `lvs_set (topspace top) (f:A->real) u`; `&1`] P2BX46_COMPACT_LT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN
    ASM_SIMP_TAC[LVS_MANIFOLD; LVS_RIEMANNIAN; OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max (c / &2) (inv(&4))` THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The flow maps between the far leaves N_u0 and N_v. *)

let P2BX46_NFLOW_LEAF_MAPS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K a u0 v.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     a + &1 <= u0 /\ u0 <= v
     ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
           (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift(&0)) (lift(v - u0)))
           (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift(v - u0)) (lift(&0))) /\
         IMAGE (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift(&0)) (lift(v - u0)))
               (lvs_set (topspace top) f u0) SUBSET lvs_set (topspace top) f v /\
         IMAGE (mfl_flow top atlas (p2bx46_nfield atlas g f a) (lift(v - u0)) (lift(&0)))
               (lvs_set (topspace top) f v) SUBSET lvs_set (topspace top) f u0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`] P2BX46_NFIELD_MCF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p2bx46_nfield atlas (g:A->real^3^3) f a`; `(:real^1)`;
                 `f:A->real`] MCF_FLOW_GEN) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "dif") (K ALL_TAC))))) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "dif" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; lvs_set; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "in" (MP_TAC o SPECL [`lift(&0)`; `lift(v - u0)`; `x:A`]) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real`; `K:real`; `a:real`; `&0`; `v - u0`; `x:A`]
        P2BX46_NFLOW_LEVEL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; lvs_set; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "in" (MP_TAC o SPECL [`lift(v - u0)`; `lift(&0)`; `x:A`]) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real`; `K:real`; `a:real`; `v - u0`; `&0`; `x:A`]
        P2BX46_NFLOW_LEVEL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* Area comparison: the flow back to N_u0 does not increase area. *)

let P2BX46_AREA_PULL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K a u0 v S A.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top /\ a + &1 <= f x ==> mfd_scalar atlas g x <= &1) /\
     a + &1 < u0 /\ u0 <= v /\
     lvs_regular atlas (topspace top) f u0 /\ lvs_regular atlas (topspace top) f v /\
     compact_in (subtopology top (lvs_set (topspace top) f v)) S /\
     mfd_has_volume (subtopology top (lvs_set (topspace top) f v),
                     lvs_atlas top atlas (topspace top) f v)
                    (lvs_metric top atlas g (topspace top) f v) S A
     ==> ?a'. mfd_has_volume (subtopology top (lvs_set (topspace top) f u0),
                              lvs_atlas top atlas (topspace top) f u0)
                             (lvs_metric top atlas g (topspace top) f u0)
                             (IMAGE (mfl_flow top atlas (p2bx46_nfield atlas g f a)
                                              (lift(v - u0)) (lift(&0))) S) a' /\
              a' <= A`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`; `u0:real`; `v:real`] P2BX46_NFLOW_LEAF_MAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!y w. y IN lvs_set (topspace top) f u0
          ==> w dot (lvs_metric top atlas (g:A->real^3^3) (topspace top) f u0 y ** w) <=
              &1 * (w dot (lvs_metric top atlas
                             (mfd_pullback_metric atlas atlas
                                (mfl_flow top atlas (p2bx46_nfield atlas g f a)
                                          (lift(&0)) (lift(v - u0))) g)
                             (topspace top) f u0 y ** w))`
  (LABEL_TAC "str") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_LEAF_STRETCH THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `F0 = mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                            (lift(&0)) (lift(v - u0))` THEN
  ABBREV_TAC `F1 = mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                            (lift(v - u0)) (lift(&0))` THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f u0))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                     (topspace top) f u0) /\
    smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f v))
                          (lvs_atlas top atlas (topspace top) f v) /\
    riemannian_metric (lvs_atlas top atlas (topspace top) f u0)
                      (lvs_metric top atlas (g:A->real^3^3) (topspace top) f u0) /\
    riemannian_metric (lvs_atlas top atlas (topspace top) f v)
                      (lvs_metric top atlas g (topspace top) f v) /\
    riemannian_metric (lvs_atlas top atlas (topspace top) f u0)
                      (lvs_metric top atlas (mfd_pullback_metric atlas atlas (F0:A->A) g)
                                  (topspace top) f u0) /\
    hausdorff_space (subtopology top (lvs_set (topspace top) f u0))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_MANIFOLD; LVS_RIEMANNIAN; OPEN_IN_TOPSPACE; LVS_HAUSDORFF] THEN
    MATCH_MP_TAC LVS_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`; `F1:A->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the leaf isometry and the area of IMAGE F1 S for the pulled-back metric *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `u0:real`; `v:real`; `F0:A->A`; `F1:A->A`] P2BX46_LEAF_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`subtopology top (lvs_set (topspace top) (f:A->real) u0)`;
    `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u0`;
    `lvs_metric top atlas (mfd_pullback_metric atlas atlas (F0:A->A) (g:A->real^3^3))
                (topspace top) f u0`;
    `subtopology top (lvs_set (topspace top) (f:A->real) v)`;
    `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f v`;
    `lvs_metric top atlas (g:A->real^3^3) (topspace top) f v`;
    `F0:A->A`; `F1:A->A`] MFD_ISOMETRY_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET lvs_set (topspace top) f v /\ compact_in top S`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `compact_in (subtopology top (lvs_set (topspace top) f v)) (S:A->bool)` THEN
    SIMP_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology top (lvs_set (topspace top) (f:A->real) v)`;
    `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f v`;
    `lvs_metric top atlas (g:A->real^3^3) (topspace top) f v`;
    `subtopology top (lvs_set (topspace top) (f:A->real) u0)`;
    `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u0`;
    `lvs_metric top atlas (mfd_pullback_metric atlas atlas (F0:A->A) (g:A->real^3^3))
                (topspace top) f u0`;
    `F1:A->A`; `F0:A->A`; `S:A->bool`; `A:real`] MFD_HAS_VOLUME_ISOMETRY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LVS_TOPSPACE; OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the area of IMAGE F1 S for the induced metric *)
  SUBGOAL_THEN `compact_in (subtopology top (lvs_set (topspace top) f u0))
                           (IMAGE (F1:A->A) S)`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_diffeo top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                     top atlas (topspace top) (F0:A->A) F1` THEN
      REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_TOPSPACE; homeomorphic_maps] THEN SIMP_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) u0)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u0`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) f u0`;
                 `IMAGE (F1:A->A) S`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a':real`) THEN
  EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) u0)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u0`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) f u0`;
                 `lvs_metric top atlas (mfd_pullback_metric atlas atlas (F0:A->A) (g:A->real^3^3))
                             (topspace top) f u0`;
                 `IMAGE (F1:A->A) S`; `a':real`; `A:real`; `&1`] LVS_HAS_VOLUME_COMPARE_QF) THEN
  REWRITE_TAC[SQRT_1; REAL_POW_ONE; REAL_MUL_LID; REAL_POS] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `w:real^2`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN lvs_set (topspace top) f u0` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "str" (MP_TAC o SPECL [`y:A`; `w:real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_MUL_LID]]);;

(* The flow back maps a sphere of N_v onto a sphere of N_u0. *)

let P2BX46_SPHERE_PULL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K a u0 v S
    (psi:real^3->A) psi'.
     p2bx46_hyp top atlas g f K /\
     (!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas g f x) /\
     a + &1 <= u0 /\ u0 <= v /\
     lvs_regular atlas (topspace top) f u0 /\ lvs_regular atlas (topspace top) f v /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0,&1))
                (subtopology top (lvs_set (topspace top) f v))
                (lvs_atlas top atlas (topspace top) f v) S psi psi'
     ==> mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                    (sphere(vec 0,&1))
                    (subtopology top (lvs_set (topspace top) f u0))
                    (lvs_atlas top atlas (topspace top) f u0)
                    (IMAGE (mfl_flow top atlas (p2bx46_nfield atlas g f a)
                                     (lift(v - u0)) (lift(&0))) S)
                    (mfl_flow top atlas (p2bx46_nfield atlas g f a)
                              (lift(v - u0)) (lift(&0)) o psi)
                    (psi' o mfl_flow top atlas (p2bx46_nfield atlas g f a)
                                     (lift(&0)) (lift(v - u0)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`; `u0:real`; `v:real`] P2BX46_NFLOW_LEAF_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `F0 = mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                            (lift(&0)) (lift(v - u0))` THEN
  ABBREV_TAC `F1 = mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                            (lift(v - u0)) (lift(&0))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real`;
                 `v:real`; `u0:real`; `F1:A->A`; `F0:A->A`] P2BX46_LEAF_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET lvs_set (topspace top) f v` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      can (term_match [] `open_in (subtopology top (lvs_set (topspace top) (f:A->real) v))
                                  (S:A->bool)`) (concl th))) THEN
    ASM_SIMP_TAC[LVS_TOPSPACE; OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) v)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f v`;
                 `lvs_set (topspace top) (f:A->real) v`;
                 `subtopology top (lvs_set (topspace top) (f:A->real) u0)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u0`;
                 `lvs_set (topspace top) (f:A->real) u0`;
                 `F1:A->A`; `F0:A->A`; `S:A->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:real^3`,`:A`; `:A`,`:B`; `:A`,`:C`;
                          `:2`,`:M`; `:2`,`:N`; `:2`,`:P`] MFD_DIFFEO_COMPOSE) THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology top (lvs_set (topspace top) (f:A->real) v)`;
    `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f v`;
    `S:A->bool`] THEN
  ASM_SIMP_TAC[SPHERE2_ATLAS; LVS_MANIFOLD; OPEN_IN_TOPSPACE]);;

(* MT 9.46: far level sets cannot contain spheres of area close to 8 pi.    *)
(* The sphere hypothesis is the output of pc_p2b_p946i (necks).             *)

let P2BX46_FAR_SPHERES_CONTRA = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K C Rmax.
     p2bx46_hyp top atlas g f K /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top
          ==> mfd_scalar atlas g x +
              lgrad2 (metric_local atlas (chart_at atlas x) g)
                     (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) -
              f x = C) /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x <= Rmax) /\
     (!e. &0 < e
          ==> ?S. compact_in top S /\
                  !x. x IN topspace top /\ ~(x IN S) ==> mfd_scalar atlas g x <= &1 + e) /\
     (!c. compact_in top {x | x IN topspace top /\ f x <= c}) /\
     (!delta V0. &0 < delta
        ==> ?v S (psi:real^3->A) psi' A.
              V0 <= v /\
              mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                         (sphere(vec 0,&1))
                         (subtopology top (lvs_set (topspace top) f v))
                         (lvs_atlas top atlas (topspace top) f v) S psi psi' /\
              mfd_has_volume (subtopology top (lvs_set (topspace top) f v),
                              lvs_atlas top atlas (topspace top) f v)
                             (lvs_metric top atlas g (topspace top) f v) S A /\
              A <= &8 * pi + delta)
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ham") (CONJUNCTS_THEN2 (LABEL_TAC "rmax")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I"))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ABBREV_TAC `a = Rmax - C + &1` THEN
  SUBGOAL_THEN `!x. x IN topspace top /\ a <= f x ==> &1 <= p2bx46_ngrad atlas (g:A->real^3^3) f x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN REWRITE_TAC[p2bx46_ngrad] THEN
    USE_THEN "ham" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
    USE_THEN "rmax" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top /\ a <= f x ==> &0 < p2bx46_ngrad atlas (g:A->real^3^3) f x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_SIMP_TAC[REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top /\ a <= f x ==> mfd_scalar atlas (g:A->real^3^3) x < &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_R_LT_1_FAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real`; `K:real`; `C:real`; `Rmax:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top /\ a + &1 <= f x ==> mfd_scalar atlas (g:A->real^3^3) x <= &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> &0 <= mfd_sectional atlas (g:A->real^3^3) x u v`
  ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!u. a <= u ==> lvs_regular atlas (topspace top) (f:A->real) u` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LVS_REGULAR_GRAD2 THEN
    EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= p2bx46_ngrad atlas (g:A->real^3^3) f x` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(f:A->real) o chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) x) =
                    (\y. f(chart_inv (chart_at atlas x) y))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[p2bx46_ngrad] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `u0 = a + &2` THEN
  SUBGOAL_THEN `lvs_regular atlas (topspace top) (f:A->real) u0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (lvs_set (topspace top) (f:A->real) u0)` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_COMPACT_SUBLEVEL THEN EXISTS_TAC `u0:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P2BX46_F_CONTINUOUS) THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the curvature bound on N_u0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `u0:real`] P2BX46_LEAF_K0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top /\ (f:A->real) x = u0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN lvs_set (topspace top) f u0` THEN
      REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BX46_LEVEL_RN_LT1 THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&1 <= p2bx46_ngrad atlas (g:A->real^3^3) f x` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(f:A->real) o chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) x) =
                      (\y. f(chart_inv (chart_at atlas x) y))` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[p2bx46_ngrad] THEN REAL_ARITH_TAC]]];
    DISCH_THEN(X_CHOOSE_THEN `k0:real` STRIP_ASSUME_TAC)] THEN
  (* the sphere at a far level v *)
  SUBGOAL_THEN `&2 < inv k0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k0:real`; `inv(&2)`] REAL_LT_INV2) THEN
    ASM_REWRITE_TAC[REAL_INV_INV];
    ALL_TAC] THEN
  USE_THEN "I" (MP_TAC o SPECL [`pi * (inv k0 - &2)`; `u0:real`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real`; `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`; `A:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lvs_regular atlas (topspace top) (f:A->real) v` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (subtopology top (lvs_set (topspace top) (f:A->real) v)) S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:real^3`,`:A`; `:A`,`:B`; `:2`,`:M`; `:2`,`:N`]
                  P2BX46_DIFFEO_IMAGE_COMPACT) THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                          `sphere(vec 0:real^3,&1)`;
                          `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f v`;
                          `psi:real^3->A`; `psi':A->real^3`] THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`; `u0:real`; `v:real`; `S:A->bool`; `A:real`]
    P2BX46_AREA_PULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`; `u0:real`; `v:real`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`] P2BX46_SPHERE_PULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `a:real`; `u0:real`; `v:real`] P2BX46_NFLOW_LEAF_MAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* Gauss-Bonnet on N_u0 *)
  MP_TAC(REWRITE_RULE[CM_GB_SPHERE_AREA_STATEMENT] (ISPEC `UNIV:A->bool` GBS2_GB_SPHERE_AREA)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`subtopology top (lvs_set (topspace top) (f:A->real) u0)`;
    `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f u0`;
    `lvs_metric top atlas (g:A->real^3^3) (topspace top) f u0`;
    `IMAGE (mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                     (lift(v - u0)) (lift(&0))) S`;
    `mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
              (lift(v - u0)) (lift(&0)) o (psi:real^3->A)`;
    `(psi':A->real^3) o mfl_flow top atlas (p2bx46_nfield atlas (g:A->real^3^3) f a)
                                (lift(&0)) (lift(v - u0))`;
    `k0:real`; `a':real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LVS_HAUSDORFF; LVS_MANIFOLD; LVS_RIEMANNIAN; OPEN_IN_TOPSPACE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `(S:A->bool) SUBSET lvs_set (topspace top) f v` MP_TAC THENL
     [UNDISCH_TAC `compact_in (subtopology top (lvs_set (topspace top) (f:A->real) v)) S` THEN
      SIMP_TAC[COMPACT_IN_SUBTOPOLOGY];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the arithmetic *)
  SUBGOAL_THEN `k0 * a' <= k0 * (&8 * pi + pi * (inv k0 - &2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `k0 * (&8 * pi + pi * (inv k0 - &2)) = pi * (&6 * k0 + &1)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < k0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `pi * (&6 * k0 + &1) < pi * &4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

