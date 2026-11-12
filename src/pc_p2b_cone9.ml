(* ========================================================================= *)
(* Unit pc_p2b_cone9: step (E) of the blow-up of MT Sec 10.6.  A limit flow  *)
(* on a ball of real^3 with nonnegative sectional curvature whose time-0     *)
(* metric carries a cone function rho (the conclusion of P2BK_LIMIT_CONE) is *)
(* flat: by P2BK_CONE_REGULAR_STATEMENT rho is smooth with                   *)
(* Hess(rho^2/2) = g(0), and MT Prop 4.22 (RFA_P2B_REQ_CONE) then gives      *)
(* sectional curvature 0, hence scalar curvature 0, which contradicts R = 1  *)
(* at the base point (P2BK_FLAT_CONTRA).                                     *)
(* ========================================================================= *)

needs "src/pc_p2b_cone8.ml";;
needs "src/pc_rfa_cone.ml";;
needs "src/pc_p2b_slice.ml";;
needs "src/pc_p2b_cone6.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Open-set atlases.  Sectional curvature is the local one, and smoothness   *)
(* and chart Hessians pass from the atlas of an open set U to the atlas of   *)
(* an open subset V.                                                         *)
(* ------------------------------------------------------------------------- *)

let P2BK_OSA_SECT = prove
 (`!U (G:real^N->real^N^N) x u v.
     open U /\ x IN U ==> mfd_sectional (open_set_atlas U) G x u v = lsectional G x u v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mfd_sectional; RFB_OPEN_SET_CHART_AT] THEN
  REWRITE_TAC[SND] THEN MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL]);;

let P2BK_OSA_SMOOTH_TRANSFER = prove
 (`!U V (f:real^N->real^K).
     open U /\ open V /\ V SUBSET U /\ mfd_smooth_on (open_set_atlas U) V f
     ==> mfd_smooth_on (open_set_atlas V) V f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mfd_smooth_on; RFB_OPEN_SET_ATLAS_CASES;
              FORALL_UNWIND_THM2; FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `U INTER V = V:real^N->bool` SUBST_ALL_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(f:real^N->real^K) o chart_inv (U:real^N->bool,(\x:real^N. x))` THEN
  ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BK_OSA_CHART_INV]);;

let P2BK_OSA_HESS_TRANSFER = prove
 (`!U V (G:real^N->real^N^N) (f:real^N->real) x u v.
     open U /\ open V /\ V SUBSET U /\ x IN V
     ==> p2b_mfd_hess (open_set_atlas V) G f x u v =
         p2bk_chart_hess (open_set_atlas U) (U,(\x:real^N. x)) G f x u v`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[p2b_mfd_hess; p2bk_chart_hess; RFB_OPEN_SET_CHART_AT] THEN
  REWRITE_TAC[SND] THEN MATCH_MP_TAC LRG_LNABLA_LOCAL THEN
  EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL];
    MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN DISCH_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2BK_OSA_CHART_INV]]);;

(* ------------------------------------------------------------------------- *)
(* The flat-limit contradiction.  Data: a flow g on the open subsets of      *)
(* ball(vec 0,r0) on (a,0] with nonnegative sectional curvature on ball(vec  *)
(* 0,r) and nonzero scalar curvature at the centre at time 0, and a cone     *)
(* function rho on ball(vec 0,r) for the distance of g(0) on ball(vec 0,rb)  *)
(* (the conclusion of P2BK_LIMIT_CONE with G0 = g(0)).  CONE_REGULAR makes   *)
(* rho smooth with Hess(rho^2/2) = g(0); MT Prop 4.22 (RFA_P2B_REQ_CONE)     *)
(* gives sectional curvature 0 at time 0, so the scalar curvature vanishes   *)
(* at the centre (P2BS_MFD_SCALAR_SECT).                                     *)
(* ------------------------------------------------------------------------- *)

let P2BK_FLAT_CONTRA = prove
 (`!r0 rb r a (g:real->real^3->real^3^3) (rho:real^3->real).
     P2BK_CONE_REGULAR_STATEMENT (:real^3) /\
     &0 < r /\ r < rb /\ rb <= r0 /\ a < &0 /\
     (!O. open O /\ O SUBSET ball(vec 0,r0)
          ==> rfs_flow_upto (subtopology euclidean O,open_set_atlas O) a (&0) g) /\
     (!t x u v. a < t /\ t <= &0 /\ x IN ball(vec 0,r) /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (g t) x u v) /\
     ~(lscalar (g(&0)) (vec 0) = &0) /\
     (!w. w IN ball(vec 0,r) ==> &0 < rho w) /\
     (!w w'. w IN ball(vec 0,r) /\ w' IN ball(vec 0,r)
             ==> mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                               open_set_atlas (ball(vec 0,rb))) w w' /\
                 abs(rho w - rho w') <=
                 mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                           open_set_atlas (ball(vec 0,rb))) (g(&0)) w w') /\
     (!w. w IN ball(vec 0,r)
          ==> ?r'. &0 < r' /\
                   !t. &0 < t /\ t < r'
                       ==> ?y. y IN ball(vec 0,r) /\
                               mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                         open_set_atlas (ball(vec 0,rb))) (g(&0)) w y = t /\
                               rho y = rho w - t) /\
     (!w y z. w IN ball(vec 0,r) /\ y IN ball(vec 0,r) /\ z IN ball(vec 0,r)
              ==> p2bk_cang (rho w) (rho z)
                    (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                               open_set_atlas (ball(vec 0,rb))) (g(&0)) w z) <=
                  p2bk_cang (rho w) (rho y)
                    (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                               open_set_atlas (ball(vec 0,rb))) (g(&0)) w y) +
                  p2bk_cang (rho y) (rho z)
                    (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                               open_set_atlas (ball(vec 0,rb))) (g(&0)) y z))
     ==> F`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "creg rpos rrb rbr0 aneg flow sec scal pos lip ray ang" THEN
  SUBGOAL_THEN `open(ball(vec 0:real^3,rb)) /\ open(ball(vec 0:real^3,r)) /\
                ball(vec 0:real^3,r) SUBSET ball(vec 0,rb) /\
                ball(vec 0:real^3,rb) SUBSET ball(vec 0,r0) /\
                ball(vec 0:real^3,r) SUBSET ball(vec 0,r0) /\
                (vec 0:real^3) IN ball(vec 0,r)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN
    MAP_EVERY UNDISCH_TAC [`r < rb`; `rb <= r0`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_flow_upto (subtopology euclidean (ball(vec 0:real^3,rb)),
                               open_set_atlas (ball(vec 0:real^3,rb))) a (&0)
                              (g:real->real^3->real^3^3) /\
                rfs_flow_upto (subtopology euclidean (ball(vec 0:real^3,r)),
                               open_set_atlas (ball(vec 0:real^3,r))) a (&0) g`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "flow" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (ball(vec 0:real^3,rb)))
                                  ((g:real->real^3->real^3^3) (&0)) /\
                riemannian_metric (open_set_atlas (ball(vec 0:real^3,r))) (g (&0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `rfs_flow_upto (subtopology euclidean (ball(vec 0:real^3,rb)),
                                  open_set_atlas (ball(vec 0:real^3,rb))) a (&0)
                                 (g:real->real^3->real^3^3)`;
      UNDISCH_TAC `rfs_flow_upto (subtopology euclidean (ball(vec 0:real^3,r)),
                                  open_set_atlas (ball(vec 0:real^3,r))) a (&0)
                                 (g:real->real^3->real^3^3)`] THEN
    MESON_TAC[rfs_flow_upto];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (ball(vec 0:real^3,rb)))
                                      (open_set_atlas (ball(vec 0:real^3,rb))) /\
                smooth_manifold_atlas (subtopology euclidean (ball(vec 0:real^3,r)))
                                      (open_set_atlas (ball(vec 0:real^3,r)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_SET_ATLAS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* CONE_REGULAR on the ball of radius rb. *)
  USE_THEN "creg" (MP_TAC o SPECL [`subtopology euclidean (ball(vec 0:real^3,rb))`;
                                   `open_set_atlas (ball(vec 0:real^3,rb))`;
                                   `(g:real->real^3->real^3^3) (&0)`;
                                   `ball(vec 0:real^3,r)`; `rho:real^3->real`] o
                   REWRITE_RULE[P2BK_CONE_REGULAR_STATEMENT]) THEN
  ANTS_TAC THENL
   [SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hess")) THEN
  (* MT Prop 4.22 on the ball of radius r. *)
  MP_TAC(REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]
          (SPECL [`subtopology euclidean (ball(vec 0:real^3,r))`;
                  `open_set_atlas (ball(vec 0:real^3,r))`;
                  `g:real->real^3->real^3^3`; `a:real`; `rho:real^3->real`]
                 (REWRITE_RULE[P2B_REQ_RFA_CONE_STATEMENT]
                              (ISPEC `(:real^3)` RFA_P2B_REQ_CONE)))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN];
      REWRITE_TAC[CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY; CONNECTED_BALL];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      SIMP_TAC[P2BK_OSA_SECT; OPEN_BALL; ASSUME `(x:real^3) IN ball(vec 0,r)`] THEN
      USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BK_OSA_SMOOTH_TRANSFER THEN
      EXISTS_TAC `ball(vec 0:real^3,rb)` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`x:real^3`; `u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN ball(vec 0,rb)` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN ball(vec 0,r)`;
                               `ball(vec 0:real^3,r) SUBSET ball(vec 0,rb)`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(vec 0:real^3,rb)`; `ball(vec 0:real^3,r)`;
                     `(g:real->real^3->real^3^3) (&0)`;
                     `\y:real^3. (rho:real^3->real) y pow 2 / &2`;
                     `x:real^3`; `u:real^3`; `v:real^3`] P2BK_OSA_HESS_TRANSFER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "hess" (MP_TAC o SPECL [`(ball(vec 0:real^3,rb),(\x:real^3. x))`;
                                       `x:real^3`; `u:real^3`; `v:real^3`]) THEN
      REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND] THEN BETA_TAC THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; OPEN_BALL;
               ASSUME `(x:real^3) IN ball(vec 0,rb)`]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "flat") THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0:real^3,u,v}
                      ==> mfd_sectional (open_set_atlas (ball(vec 0:real^3,r)))
                                        ((g:real->real^3->real^3^3) (&0)) (vec 0) u v = &0`
  (LABEL_TAC "sec0") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "flat" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_scalar (open_set_atlas (ball(vec 0:real^3,r)))
                                 ((g:real->real^3->real^3^3) (&0)) (vec 0) /\
                mfd_scalar (open_set_atlas (ball(vec 0:real^3,r))) (g (&0)) (vec 0) <= &0`
  MP_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,r))`;
                   `open_set_atlas (ball(vec 0:real^3,r))`;
                   `(g:real->real^3->real^3^3) (&0)`; `vec 0:real^3`; `&0`]
                  P2BS_MFD_SCALAR_SECT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
    USE_THEN "sec0" (fun th -> SIMP_TAC[th; REAL_LE_REFL; REAL_MUL_RZERO]);
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (open_set_atlas (ball(vec 0:real^3,r)))
                           ((g:real->real^3->real^3^3) (&0)) (vec 0) =
                lscalar (g (&0)) (vec 0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_MFD_SCALAR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "scal" MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Curvature of limits.  Collinear pairs have sectional curvature 0          *)
(* (lsectional is a quotient); LCK_CURVATURE_STABILITY for a fixed limit     *)
(* metric G0 at a point y; nonnegative sectional curvature and the value of  *)
(* the scalar curvature pass to C2 limits at a point.                        *)
(* ------------------------------------------------------------------------- *)

let P2BK_LSECT_COLLINEAR = prove
 (`!(G:real^N->real^N^N) y u v. collinear {vec 0,u,v} ==> lsectional G y u v = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA; lsectional; real_div] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(MESON[REAL_INV_0; REAL_MUL_RZERO] `!a b:real. b = &0 ==> a * inv b = &0`) THEN
  ASM_REWRITE_TAC[DOT_LZERO; DOT_RZERO; MATRIX_VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RMUL;
                  DOT_LMUL; DOT_RMUL] THEN
  CONV_TAC REAL_RING);;

let P2BK_LIMIT_CURV = prove
 (`!s (G0:real^N->real^N^N) y alpha.
     metric_field s G0 /\ y IN s /\ &0 < alpha
     ==> ?eta. &0 < eta /\
               !G. metric_field s G /\ lck_dist2 2 G0 G y < eta
                   ==> abs(lscalar G y - lscalar G0 y) <= alpha /\
                       (!u v. ~collinear {vec 0,u,v}
                              ==> abs(lsectional G y u v - lsectional G0 y u v) <= alpha)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sqrt(abs(lrm_deriv_norm2 0 (G0:real^N->real^N^N) y) + &1)`; `alpha:real`]
                LCK_CURVATURE_STABILITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `G:real^N->real^N^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                `G:real^N->real^N^N`; `y:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SQRT_POW_2; REAL_ARITH `!x. &0 <= abs x + &1`;
             REAL_ARITH `!x. x <= abs x + &1`];
    SIMP_TAC[]]);;

let P2BK_LIMIT_SECT_NONNEG = prove
 (`!s (G0:real^N->real^N^N) y.
     metric_field s G0 /\ y IN s /\
     (!eta. &0 < eta
            ==> ?G. metric_field s G /\ lck_dist2 2 G0 G y < eta /\
                    !u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> !u v. &0 <= lsectional G0 y u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  ASM_CASES_TAC `collinear {vec 0:real^N,u,v}` THENL
   [ASM_SIMP_TAC[P2BK_LSECT_COLLINEAR; REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `--(lsectional (G0:real^N->real^N^N) y u v) / &2`] P2BK_LIMIT_CURV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lsectional (G0:real^N->real^N^N) y u v < &0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->real^N^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "st" (MP_TAC o SPEC `G:real^N->real^N^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lsectional (G0:real^N->real^N^N) y u v < &0` THEN REAL_ARITH_TAC);;

let P2BK_LIMIT_SCALAR_EQ = prove
 (`!s (G0:real^N->real^N^N) y c.
     metric_field s G0 /\ y IN s /\
     (!eta. &0 < eta
            ==> ?G. metric_field s G /\ lck_dist2 2 G0 G y < eta /\ lscalar G y = c)
     ==> lscalar G0 y = c`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(x - c)) ==> x = c`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `abs(lscalar (G0:real^N->real^N^N) y - c) / &2`] P2BK_LIMIT_CURV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < abs(lscalar (G0:real^N->real^N^N) y - c)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->real^N^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "st" (MP_TAC o SPEC `G:real^N->real^N^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < abs(lscalar (G0:real^N->real^N^N) y - c)` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* In a regular view, the pullback of the time-t metric by a parametrization *)
(* of the time-0 slice with image in a set persisting on (a,0]               *)
(* (P2BK_VIEW_PARAM_AT of pc_p2b_cone6) is a metric field with sectional     *)
(* curvature >= 0 if the slice has sec >= 0; sec >= 0 passes to C2 limits of *)
(* such pullbacks.                                                           *)
(* ------------------------------------------------------------------------- *)

let P2BK_VIEW_PB_SECT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a s (e:real^3->A) t y.
     p2c_regular_view V /\ rfs_persists V W a (&0) /\ a < t /\ t <= &0 /\
     mfd_param (rfs_vtop V (&0)) (rfs_vatlas V (&0)) s e /\ IMAGE e s SUBSET W /\
     (!x u v. x IN topspace (rfs_vtop V t) /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional (rfs_vatlas V t) (rfs_vmetric V t) x u v) /\
     y IN s
     ==> metric_field s (rfs_pullback (rfs_vatlas V t) e (rfs_vmetric V t)) /\
         !u v. &0 <= lsectional (rfs_pullback (rfs_vatlas V t) e (rfs_vmetric V t)) y u v`,
  REPEAT GEN_TAC THEN INTRO_TAC "reg pers at t0 par im sec ys" THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop V t) (rfs_vatlas V t) s (e:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_VIEW_PARAM_AT THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas
                  (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) t) (rfs_vatlas V t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `&0`; `t:real`]
                  P2BK_PERSISTS_AT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace (rfs_vtop V t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t`;
                   `s:real^3->bool`; `e:real^3->A`; `s:real^3->bool`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t:A->real^3^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view
                  (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(e:real^3->A) y IN topspace (rfs_vtop V t)` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t`;
                 `s:real^3->bool`; `e:real^3->A`; `y:real^3`; `u:real^3`; `v:real^3`]
                APX_PULLBACK_SECTIONAL_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `p = frechet_derivative
                    (SND(chart_at (rfs_vatlas V t) ((e:real^3->A) y)) o e) (at y) u` THEN
  ABBREV_TAC `q = frechet_derivative
                    (SND(chart_at (rfs_vatlas V t) ((e:real^3->A) y)) o e) (at y) v` THEN
  ASM_CASES_TAC `collinear {vec 0:real^3,p,q}` THENL
   [ASM_SIMP_TAC[mfd_sectional; P2BK_LSECT_COLLINEAR; REAL_LE_REFL];
    USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BK_VIEW_LIMIT_SEC = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W (phi:num->real^3->A) (G0:real^3->real^3^3) r0 a t y.
     (!k. p2c_regular_view (V k) /\ rfs_persists (V k) (W k) a (&0) /\
          mfd_param (rfs_vtop (V k) (&0)) (rfs_vatlas (V k) (&0)) (ball(vec 0,r0)) (phi k) /\
          IMAGE (phi k) (ball(vec 0,r0)) SUBSET W k /\
          (!x u v. x IN topspace (rfs_vtop (V k) t) /\ ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional (rfs_vatlas (V k) t) (rfs_vmetric (V k) t) x u v)) /\
     a < t /\ t <= &0 /\ y IN ball(vec 0,r0) /\ metric_field (ball(vec 0,r0)) G0 /\
     (!eta. &0 < eta
            ==> ?k. lck_dist2 2 G0
                      (rfs_pullback (rfs_vatlas (V k) t) (phi k) (rfs_vmetric (V k) t)) y < eta)
     ==> !u v. &0 <= lsectional G0 y u v`,
  REPEAT GEN_TAC THEN INTRO_TAC "views at t0 ys mf conv" THEN
  MATCH_MP_TAC P2BK_LIMIT_SECT_NONNEG THEN EXISTS_TAC `ball(vec 0:real^3,r0)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
  USE_THEN "conv" (MP_TAC o SPEC `eta:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  EXISTS_TAC `rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#
                                          (real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) k) t)
                           ((phi:num->real^3->A) k) (rfs_vmetric (V k) t)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) k`;
                 `(W:num->A->bool) k`; `a:real`; `ball(vec 0:real^3,r0)`;
                 `(phi:num->real^3->A) k`; `t:real`; `y:real^3`] P2BK_VIEW_PB_SECT) THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The bad tube near E.  A sequence x n with dE(x n) -> 0, and at a point x  *)
(* with dE x < s1/2 the neck data of P2BK_NECK_REQN_HYPS (with eps' = 2 eps, *)
(* len = 1/2 and C = (8 eps c2)^2): points y of the unit ball of R(x) g      *)
(* about x have dE(y) in (dE(x)/2, 3 dE(x)/2), so they are neck centres, and *)
(* R(y) <= C R(x) by the bounds of P2BK_END_CONE_STATEMENT.                  *)
(* ------------------------------------------------------------------------- *)

let P2BK_RATIO_ARITH = prove
 (`!eps c2 Q Ry dx dy d.
     &0 < eps /\ eps <= &1 / &8 /\ &0 < Q /\ &0 < Ry /\ &0 < dx /\
     inv(&4 * eps) <= sqrt Q * dx /\ abs(dx - dy) <= d /\ d < &1 / sqrt Q
     ==> dx / &2 < dy /\ dy < &3 / &2 * dx /\
         (sqrt Ry * dy <= c2 ==> Ry <= (&8 * eps * c2) pow 2 * Q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = sqrt Q` THEN ABBREV_TAC `ry = sqrt Ry` THEN
  SUBGOAL_THEN `&0 < q /\ &0 < ry /\ q pow 2 = Q /\ ry pow 2 = Ry` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "ry"] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&4 * eps) * (q * dx)` ASSUME_TAC THENL
   [UNDISCH_TAC `inv(&4 * eps) <= q * dx` THEN
    ASM_SIMP_TAC[P2BK_INV_LE_EQ; REAL_ARITH `&0 < eps ==> &0 < &4 * eps`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / q <= &4 * eps * dx` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `&1 <= (&4 * eps) * (q * dx)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * eps * dx <= dx / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 / &2 - &4 * eps) * dx ==> &4 * eps * dx <= dx / &2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dx / &2 < dy /\ dy < &3 / &2 * dx` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ry * dx < &2 * c2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `ry * (&2 * dy)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `ry * dy <= c2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ry <= &8 * eps * c2 * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ry * ((&4 * eps) * (q * dx))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `ry * ((&4 * eps) * (q * dx)) = (&4 * eps * q) * (ry * dx) /\
                    &8 * eps * c2 * q = (&4 * eps * q) * (&2 * c2)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ry pow 2 <= (&8 * eps * c2 * q) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

let P2BK_SEQ_TO_ZERO = prove
 (`!S (f:B->real) s1.
     &0 < s1 /\ (!s. &0 < s ==> ?x. x IN S /\ f x < s)
     ==> ?x:num->B. (!n. x n IN S /\ f(x n) < s1) /\
                    (!e. &0 < e ==> ?k0. !k. k0 <= k ==> f(x k) < e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `min s1 (inv(&n + &1))`) THEN
  REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->B` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&k + &1)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;

let P2BK_TUBE_NECK_HYPS = prove
 (`!eps top atlas (g:B->real^3^3) V H dE s1 c2 x.
     p2b_bad_tube eps (top,atlas) g V H /\ &0 < eps /\ eps <= &1 / &8 /\
     (!y. y IN topspace top ==> &0 < dE y) /\
     (!y z. y IN topspace top /\ z IN topspace top
            ==> abs(dE y - dE z) <= mfd_dist (top,atlas) g y z) /\
     (!y. y IN topspace top /\ dE y <= s1
          ==> (?e. rfs_evolving_neck V (&2 * eps) y (&0) (&1 / &2) e) /\
              inv(&4 * eps) <= sqrt(mfd_scalar atlas g y) * dE y /\
              sqrt(mfd_scalar atlas g y) * dE y <= c2) /\
     x IN topspace top /\ dE x < s1 / &2
     ==> (?e. rfs_evolving_neck V (&2 * eps) x (&0) (&1 / &2) e) /\
         &1 <= (&8 * eps * c2) pow 2 /\
         (!y. y IN mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0))
                            (\z. rfs_vscalar V (&0) x %% rfs_vmetric V (&0) z) x (&1)
              ==> (?e'. rfs_evolving_neck V (&2 * eps) y (&0) (&1 / &2) e') /\
                  rfs_vscalar V (&0) y <= (&8 * eps * c2) pow 2 * rfs_vscalar V (&0) x)`,
  REPEAT GEN_TAC THEN INTRO_TAC "tube eps eps8 dpos lip neck x dx" THEN
  SUBGOAL_THEN `rfs_vtop V (&0) = top /\ rfs_vatlas V (&0) = atlas /\
                rfs_vmetric V (&0) = (g:B->real^3^3) /\
                smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
                (!y. y IN topspace top ==> &0 < mfd_scalar atlas g y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_bad_tube eps (top,atlas) (g:B->real^3^3) V H` THEN
    SIMP_TAC[p2b_bad_tube];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x /\ &0 < dE(x:B)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "neck" (MP_TAC o SPEC `x:B`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real^3->B`) STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL [EXISTS_TAC `e:real^3->B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN
    SUBGOAL_THEN `inv(&4 * eps) <= c2` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2BK_INV_LE_EQ; REAL_ARITH `&0 < eps ==> &0 < &4 * eps`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN ASM_SIMP_TAC[MFD_BALL_SCALE] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `c2:real`; `mfd_scalar atlas (g:B->real^3^3) x`;
                `mfd_scalar atlas (g:B->real^3^3) y`; `dE(x:B):real`; `dE(y:B):real`;
                `mfd_dist (top,atlas) (g:B->real^3^3) x y`] P2BK_RATIO_ARITH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN USE_THEN "lip" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "neck" (MP_TAC o SPEC `y:B`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e':real^3->B`) STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `e':real^3->B` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for the assembly.  Nonnegative sectional curvature of a view       *)
(* passes to its rescalings; the pullback of R(e y) g by a parametrization e *)
(* has scalar curvature 1 at y; subsequences of null sequences are null.     *)
(* ------------------------------------------------------------------------- *)

let P2BK_VIEW_SEC_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    Q t.
     p2c_regular_view V /\
     (!t x u v. t <= &0 /\ x IN topspace(rfs_vtop V t) /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (rfs_vatlas V t) (rfs_vmetric V t) x u v) /\
     &0 < Q /\ t <= &0
     ==> !x u v. x IN topspace (rfs_vtop (p2b_rescale_view V (&0) Q) t) /\
                 ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional (rfs_vatlas (p2b_rescale_view V (&0) Q) t)
                                         (rfs_vmetric (p2b_rescale_view V (&0) Q) t) x u v`,
  REPEAT GEN_TAC THEN INTRO_TAC "reg sec Q t" THEN REWRITE_TAC[P2BK_RV0] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t / Q <= &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop V (t / Q)) (rfs_vatlas V (t / Q)) /\
                riemannian_metric (rfs_vatlas V (t / Q))
                                  (rfs_vmetric V (t / Q):A->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "reg" (MP_TAC o SPEC `t / Q` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(x:A) IN topspace (rfs_vtop V (t / Q))` THEN SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop V (t / Q):A topology`;
                 `rfs_vatlas V (t / Q):((A->bool)#(A->real^3))->bool`;
                 `rfs_vmetric V (t / Q):A->real^3^3`; `Q:real`; `x:A`; `u:real^3`; `v:real^3`]
                P2BCS_SECT_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BK_PB_SCALAR_ONE = prove
 (`!top atlas (g:A->real^3^3) s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s /\ &0 < mfd_scalar atlas g (e y)
     ==> metric_field s (rfs_pullback atlas e (\z. mfd_scalar atlas g (e y) %% g z)) /\
         lscalar (rfs_pullback atlas e (\z. mfd_scalar atlas g (e y) %% g z)) y = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas (\z. mfd_scalar atlas g ((e:real^3->A) y) %%
                                             (g:A->real^3^3) z)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\z. mfd_scalar atlas g ((e:real^3->A) y) %% (g:A->real^3^3) z`;
                 `s:real^3->bool`; `e:real^3->A`; `y:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `s:real^3->bool`; `e:real^3->A`; `s:real^3->bool`] MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y)`; `(e:real^3->A) y`]
                P2BCS_SCALAR_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_DIV_REFL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

let P2BK_SUBSEQ_NULL = prove
 (`!(f:num->real) sub.
     p3_subseq sub /\ (!e. &0 < e ==> ?k0. !k. k0 <= k ==> f k < e)
     ==> !e. &0 < e ==> ?k0. !k. k0 <= k ==> f(sub k) < e`,
  REWRITE_TAC[p3_subseq] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `!m n. m < n ==> (sub:num->num) m < sub n` THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The blow-up (MT Sec 10.6).  Given the local compactness statement         *)
(* (REQ_N), the end-cone data (END_CONE) and CONE_REGULAR at (:real^3),      *)
(* there is no bad tube: rescale at points x n with dE(x n) -> 0 by R(x n),  *)
(* the neck data give the hypotheses of REQ_N (P2BK_NECK_REQN_HYPS), the     *)
(* limit carries a cone function (P2BK_LIMIT_CONE), has sec >= 0 and R = 1   *)
(* at the base point, which contradicts P2BK_FLAT_CONTRA.                    *)
(* ------------------------------------------------------------------------- *)

let P2BK_BLOWUP = prove
 (`!w:B->bool.
     P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT w /\ P2BK_END_CONE_STATEMENT w /\
     P2BK_CONE_REGULAR_STATEMENT (:real^3)
     ==> P2B_NO_BAD_TUBE_STATEMENT w`,
  GEN_TAC THEN INTRO_TAC "reqn endc creg" THEN
  USE_THEN "endc" (X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ec0")) o
                   REWRITE_RULE[P2BK_END_CONE_STATEMENT]) THEN
  X_CHOOSE_THEN `eps1:real` (X_CHOOSE_THEN `K1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nreqn"))))
    (INST_TYPE [`:B`,`:A`] P2BK_NECK_REQN_HYPS) THEN
  REWRITE_TAC[P2B_NO_BAD_TUBE_STATEMENT] THEN
  EXISTS_TAC `min eps0 (min (eps1 / &2) (&1 / &8))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
    `V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
    `H:real^3->B`] THEN
  DISCH_TAC THEN
  USE_THEN "ec0" (MP_TAC o SPECL
   [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
    `V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
    `H:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dE:B->real` (X_CHOOSE_THEN `s1:real`
    (X_CHOOSE_THEN `c2:real` (DESTRUCT_TAC "s1 c2 dpos lip small neck ray ang")))) THEN
  (* The bad tube. *)
  SUBGOAL_THEN
   `hausdorff_space (top:B topology) /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas (g:B->real^3^3) /\
    p2c_regular_view (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                        (real->B->real^3^3)) /\
    rfs_vtop V (&0) = top /\ rfs_vatlas V (&0) = atlas /\ rfs_vmetric V (&0) = g /\
    (!y. y IN topspace top ==> &0 < mfd_scalar atlas g y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_bad_tube eps (top,atlas) (g:B->real^3^3) V H` THEN
    SIMP_TAC[p2b_bad_tube];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z. y IN topspace top /\ z IN topspace top
          ==> mfd_joinable (top,atlas) y z /\
              abs(dE y - dE z) <= mfd_dist (top,atlas) (g:B->real^3^3) y z`
  (LABEL_TAC "jl") THENL
   [UNDISCH_TAC `p2b_bad_tube eps (top,atlas) (g:B->real^3^3) V H` THEN
    REWRITE_TAC[p2b_bad_tube] THEN STRIP_TAC THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[]; USE_THEN "lip" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y u v. t <= &0 /\ y IN topspace(rfs_vtop V t) /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional (rfs_vatlas V t)
                                      (rfs_vmetric (V:(real->B topology)#
                                         (real->((B->bool)#(B->real^3))->bool)#
                                         (real->B->real^3^3)) t) y u v`
  (LABEL_TAC "secv") THENL
   [UNDISCH_TAC `p2b_bad_tube eps (top,atlas) (g:B->real^3^3) V H` THEN
    SIMP_TAC[p2b_bad_tube];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Q (z:B) r. rfs_vtop (p2b_rescale_view V (&0) Q) (&0) = top /\
                rfs_vatlas (p2b_rescale_view V (&0) Q) (&0) = atlas /\
                rfs_vmetric (p2b_rescale_view V (&0) Q) (&0) = (\y. Q %% (g:B->real^3^3) y) /\
                rfs_vball (p2b_rescale_view V (&0) Q) (&0) z r =
                mfd_ball (top,atlas) (\y. Q %% g y) z r`
  (LABEL_TAC "rv") THENL
   [ASM_REWRITE_TAC[P2BK_RV0; P2BK_DIV_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. rfs_vscalar V (&0) z = mfd_scalar atlas (g:B->real^3^3) z`
  (LABEL_TAC "rvs") THENL
   [ASM_REWRITE_TAC[P2BN_RFS_VSCALAR]; ALL_TAC] THEN
  (* The sequence. *)
  MP_TAC(ISPECL [`topspace top:B->bool`; `dE:B->real`; `s1 / &2`] P2BK_SEQ_TO_ZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->B` (CONJUNCTS_THEN2 (LABEL_TAC "xs") (LABEL_TAC "xnull"))) THEN
  SUBGOAL_THEN
   `!n. (?e. rfs_evolving_neck V (&2 * eps) ((x:num->B) n) (&0) (&1 / &2) e) /\
        &1 <= (&8 * eps * c2) pow 2 /\
        (!y. y IN mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0))
                           (\z. rfs_vscalar V (&0) (x n) %% rfs_vmetric V (&0) z) (x n) (&1)
             ==> (?e'. rfs_evolving_neck V (&2 * eps) y (&0) (&1 / &2) e') /\
                 rfs_vscalar V (&0) y <= (&8 * eps * c2) pow 2 * rfs_vscalar V (&0) (x n))`
  (LABEL_TAC "nk") THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BK_TUBE_NECK_HYPS THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `H:real^3->B`; `dE:B->real`; `s1:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&8 * eps * c2) pow 2 /\ --(&1 / &2) / (&8 * eps * c2) pow 2 < &0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nk" (MP_TAC o SPEC `0`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&1 <= c ==> &0 < c`; REAL_MUL_LZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. p2c_regular_view (p2b_rescale_view V (&0) (rfs_vscalar V (&0) ((x:num->B) n))) /\
        x n IN topspace (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0)) /\
        compact_in (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0))
          (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0) closure_of
           rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0) (x n) (&1)) /\
        rfs_persists (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n)))
          (rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0) (x n) (&1))
          (--(&1 / &2) / (&8 * eps * c2) pow 2) (&0) /\
        (!s y. --(&1 / &2) / (&8 * eps * c2) pow 2 < s /\ s <= &0 /\
               y IN rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0)
                              (x n) (&1)
               ==> mfd_rm_norm
                     (rfs_vatlas (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) s)
                     (rfs_vmetric (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) s) y
                   <= K1 * (&8 * eps * c2) pow 2) /\
        (?v. mfd_has_volume
               (rfs_vtop (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0),
                rfs_vatlas (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0))
               (rfs_vmetric (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0))
               (rfs_vball (p2b_rescale_view V (&0) (rfs_vscalar V (&0) (x n))) (&0)
                          (x n) (&1)) v /\
             pi / &750 * min (&1) (inv(sqrt K1)) pow 3 <= v)`
  (LABEL_TAC "hyps") THENL
   [GEN_TAC THEN USE_THEN "nk" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real^3->B`) STRIP_ASSUME_TAC) THEN
    USE_THEN "nreqn" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&2 * eps`; `e:real^3->B`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* The local compactness statement. *)
  USE_THEN "reqn" (MP_TAC o SPECL
   [`\n. p2b_rescale_view (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                             (real->B->real^3^3)) (&0) (rfs_vscalar V (&0) ((x:num->B) n))`;
    `x:num->B`; `&1`; `--(&1 / &2) / (&8 * eps * c2) pow 2`; `K1 * (&8 * eps * c2) pow 2`;
    `pi / &750 * min (&1) (inv(sqrt K1)) pow 3`] o
   REWRITE_RULE[P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT]) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_01] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MP_TAC PI_POS THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; REAL_LT_INV_EQ] THEN
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `sub:num->num`
    (X_CHOOSE_THEN `phi:num->real^3->B` (X_CHOOSE_THEN `gl:real->real^3->real^3^3`
      (DESTRUCT_TAC "r0pos r01 subseq phis mfs flows conv"))))) THEN
  SUBGOAL_THEN
   `!k. mfd_param top atlas (ball(vec 0,r0)) ((phi:num->real^3->B) k) /\
        phi k (vec 0) = (x:num->B) ((sub:num->num) k) /\
        IMAGE (phi k) (ball(vec 0,r0)) SUBSET
        mfd_ball (top,atlas) (\y. rfs_vscalar V (&0) (x (sub k)) %% (g:B->real^3^3) y)
                 (x (sub k)) (&1)`
  (LABEL_TAC "ph") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "phis" (MP_TAC o SPEC `k:num`) THEN
    USE_THEN "rv" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!eta. &0 < eta
          ==> ?k0. !k w. k0 <= k /\ w IN cball(vec 0,r0 / &2)
                         ==> lck_dist2 0 ((gl:real->real^3->real^3^3) (&0))
                               (rfs_pullback atlas ((phi:num->real^3->B) k)
                                  (\y. rfs_vscalar V (&0) ((x:num->B) ((sub:num->num) k)) %%
                                       (g:B->real^3^3) y)) w < eta`
  (LABEL_TAC "conv0") THENL
   [X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPECL [`cball(vec 0:real^3,r0 / &2)`; `0`; `eta:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_CBALL; SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `w:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `&0`; `w:real^3`]) THEN
    USE_THEN "rv" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &0 < rfs_vscalar V (&0) ((x:num->B) ((sub:num->num) k)) /\ x (sub k) IN topspace top /\
        inv(&4 * eps) <= sqrt(rfs_vscalar V (&0) (x (sub k))) * dE(x (sub k)) /\
        sqrt(rfs_vscalar V (&0) (x (sub k))) * dE(x (sub k)) <= c2`
  (LABEL_TAC "qk") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "rvs" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "xs" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k`) THEN
    USE_THEN "neck" (MP_TAC o SPEC `(x:num->B) ((sub:num->num) k)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * eps) /\ inv(&4 * eps) <= c2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "qk" (MP_TAC o SPEC `0`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?k0. !k. k0 <= k ==> dE((x:num->B) ((sub:num->num) k)) < e`
  (LABEL_TAC "subnull") THENL
   [MP_TAC(ISPECL [`\n. dE((x:num->B) n):real`; `sub:num->num`] P2BK_SUBSEQ_NULL) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,r0)) ((gl:real->real^3->real^3^3) (&0))`
  ASSUME_TAC THENL
   [USE_THEN "mfs" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. mfd_param top atlas (ball(vec 0,r0)) ((phi:num->real^3->B) k) /\
                    phi k (vec 0) = (x:num->B) ((sub:num->num) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bk_lcdata (top,atlas) (g:B->real^3^3) dE s1 (\k. (x:num->B) ((sub:num->num) k))
                (\k. rfs_vscalar V (&0) (x (sub k))) (inv(&4 * eps)) c2
                (phi:num->real^3->B) ((gl:real->real^3->real^3^3) (&0)) r0 (r0 / &2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bk_lcdata] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BK_LIMIT_CONE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `rho:real^3->real` STRIP_ASSUME_TAC)) THEN
  (* Nonnegative sectional curvature of the limit on ball(vec 0,r). *)
  SUBGOAL_THEN
   `!t y u v. --(&1 / &2) / (&8 * eps * c2) pow 2 / &2 < t /\ t <= &0 /\
              y IN ball(vec 0,r) /\ ~collinear {vec 0,u,v}
              ==> &0 <= lsectional ((gl:real->real^3->real^3^3) t) y u v`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN ball(vec 0,r0)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball(vec 0,r)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`\k. p2b_rescale_view (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                              (real->B->real^3^3)) (&0) (rfs_vscalar V (&0) ((x:num->B) ((sub:num->num) k)))`;
      `\k. mfd_ball (top,atlas)
             (\y. rfs_vscalar V (&0) ((x:num->B) ((sub:num->num) k)) %% (g:B->real^3^3) y) (x (sub k)) (&1)`;
      `phi:num->real^3->B`; `(gl:real->real^3->real^3^3) t`; `r0:real`;
      `--(&1 / &2) / (&8 * eps * c2) pow 2`; `t:real`; `y:real^3`] P2BK_VIEW_LIMIT_SEC)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `k:num` THEN USE_THEN "hyps" (MP_TAC o SPEC `(sub:num->num) k`) THEN
        USE_THEN "rv" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2BK_VIEW_SEC_RESCALE THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "qk" (MP_TAC o SPEC `k:num`) THEN
        USE_THEN "rvs" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "mfs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
        USE_THEN "conv" (MP_TAC o SPECL [`{y:real^3}`; `2`; `eta:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPECL [`k0:num`; `t:real`; `y:real^3`])) THEN
        REWRITE_TAC[LE_REFL; IN_SING] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN EXISTS_TAC `k0:num` THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* R = 1 at the centre at time 0. *)
  SUBGOAL_THEN `lscalar ((gl:real->real^3->real^3^3) (&0)) (vec 0) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_LIMIT_SCALAR_EQ THEN EXISTS_TAC `ball(vec 0:real^3,r0)` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPECL [`{vec 0:real^3}`; `2`; `eta:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET; CENTRE_IN_BALL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPECL [`k0:num`; `&0`; `vec 0:real^3`])) THEN
    REWRITE_TAC[LE_REFL; IN_SING; REAL_LE_REFL] THEN
    USE_THEN "rv" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    EXISTS_TAC `rfs_pullback atlas ((phi:num->real^3->B) k0)
                  (\y. rfs_vscalar V (&0) ((x:num->B) ((sub:num->num) k0)) %% (g:B->real^3^3) y)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `ball(vec 0:real^3,r0)`; `(phi:num->real^3->B) k0`; `vec 0:real^3`]
                  P2BK_PB_SCALAR_ONE) THEN
    USE_THEN "ph" (MP_TAC o SPEC `k0:num`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    USE_THEN "rvs" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "qk" (MP_TAC o SPEC `k0:num`) THEN USE_THEN "rvs" (fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* The contradiction. *)
  MATCH_MP_TAC(ISPECL [`r0:real`; `r0 / &2`; `r:real`;
                       `--(&1 / &2) / (&8 * eps * c2) pow 2 / &2`;
                       `gl:real->real^3->real^3^3`; `rho:real^3->real`] P2BK_FLAT_CONTRA) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN ASM_REAL_ARITH_TAC);;

