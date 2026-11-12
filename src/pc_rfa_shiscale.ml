(* ========================================================================= *)
(* Unit pc_rfa_shiscale: Shi's interior estimate for nabla Rm in             *)
(* scale-invariant form, the statement P2A_REQ_SHI_SCALED_STATEMENT of       *)
(* pc_p2a_defs (RFA_P2A_REQ_SHI_SCALED), from RFA_P2_THM_3_28                *)
(* (pc_rfa_shi328) at l = 1, K = r = tau = 1 applied to the parabolically    *)
(* rescaled flow r^-2 g(r^2 t) (MT Claim 8.5).                               *)
(* ========================================================================= *)

needs "src/pc_rfa_shi328.ml";;
needs "src/pc_p2a_defs.ml";;

prioritize_real();;
type_invention_error := true;;



(* ========================================================================= *)
(* Scaling of flows on (a,b], of sectional curvatures and |Rm|,              *)
(* and of |nabla^l Rm|^2.                                                   *)
(* ========================================================================= *)

(* Parabolic rescaling of a flow on (a,b] with a smooth extension past b.  *)

let RFA_RFS_FLOW_UPTO_RESCALE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) q.
     rfs_flow_upto (top,atlas) a b g /\ &0 < q
     ==> rfs_flow_upto (top,atlas) (q * a) (q * b) (\t x. q %% g (t / q) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RICCI_FLOW_RESCALE] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(q * b) / q = b` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN; ricci_flow_on]; ALL_TAC] THEN
  EXISTS_TAC `q * e` THEN
  EXISTS_TAC `\z:real^(1,3)finite_sum.
                q % (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                      (pastecart (lift(inv q * drop(fstcart z) + &0)) (sndcart z))` THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MP_TAC(ISPECL
     [`Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`;
      `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
      `a:real`; `b + e:real`; `q * a:real`; `q * b + q * e:real`; `inv q:real`; `&0`]
     RFB_SMOOTH_TIME_AFFINE) THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN
    SUBGOAL_THEN `inv q * t = t / q` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_SYM]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_ADD_RID] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL; ETA_AX] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `inv q * t = t / q` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_SYM]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Sectional curvatures and |Rm| of c g are those of g divided by c.        *)

let RFA_SEC_SCALE_ARITH = prove
 (`!c n a b d. &0 < c
               ==> (c * n) / ((c * a) * (c * b) - (c * d) pow 2) =
                   n / (a * b - d pow 2) / c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a * b - d pow 2 = &0` THENL
   [SUBGOAL_THEN `(c * a) * (c * b) - (c * d) pow 2 = c pow 2 * (a * b - d pow 2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_MUL_LZERO];
    UNDISCH_TAC `~(a * b - d pow 2 = &0)` THEN UNDISCH_TAC `&0 < c` THEN
    CONV_TAC REAL_FIELD]);;

let RFA_MFD_SECTIONAL_CMUL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < c
     ==> mfd_sectional atlas (\z. c %% g z) x u v = mfd_sectional atlas g x u v / c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sectional; METRIC_LOCAL_CMUL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `ch = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(ch:(A->bool)#(A->real^N))) (FST ch))
                  (metric_local atlas ch (g:A->real^N^N)) /\
                SND ch (x:A) IN IMAGE (SND ch) (FST ch)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[lsectional; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  MP_TAC(ISPECL [`IMAGE (SND(ch:(A->bool)#(A->real^N))) (FST ch)`;
                 `metric_local atlas (ch:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `c:real`; `SND (ch:(A->bool)#(A->real^N)) (x:A)`;
                 `u:real^N`; `v:real^N`; `v:real^N`] LRIEMANN_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RFA_SEC_SCALE_ARITH THEN ASM_REWRITE_TAC[]);;

let RFA_MFD_RM_NORM_CMUL_LE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x B.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < c /\ 2 <= dimindex(:N) /\
     mfd_rm_norm atlas g x <= B
     ==> mfd_rm_norm atlas (\z. c %% g z) x <= B / c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:real`; `x:A`; `u:real^N`; `v:real^N`] RFA_MFD_SECTIONAL_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_rm_norm atlas (g:A->real^N^N) x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* The norm |nabla^l Rm|^2 of c G is c^-(l+2) times that of G; first the     *)
(* metric scaling RFA_LTNORM2_METRIC_SCALE, the statement of                 *)
(* P2C_LTNORM2_METRIC_SCALE of pc_p2c_cderiv, which is not in this load      *)
(* closure.                                                                  *)

let RFA_LTNORM2_METRIC_SCALE = prove
 (`!k (G:real^N->real^N^N) c tf y.
     ltnorm2 k (\z. c %% G z) tf y = inv c pow k * ltnorm2 k G tf y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltnorm2; MATRIX_INV_CMUL; MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[PRODUCT_MUL_NUMSEG; PRODUCT_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC);;

let RFA_LRM_DERIV_NORM2_SCALE = prove
 (`!U (G:real^N->real^N^N) c l y.
     metric_field U G /\ y IN U /\ &0 < c
     ==> lrm_deriv_norm2 l (\z. c %% G z) y = inv c pow (l + 2) * lrm_deriv_norm2 l G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRM4_TENSOR_FIELD) THEN
  SUBGOAL_THEN
   `!z u. z IN U ==> lrm4 (\z. c %% (G:real^N->real^N^N) z) z u = c * lrm4 G z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRIEMANN_SCALE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z u. z IN U
          ==> lnabla_iter 4 l (\z. c %% (G:real^N->real^N^N) z) (lrm4 (\z. c %% G z)) z u =
              c * lnabla_iter 4 l G (lrm4 G) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `lnabla_iter 4 l (G:real^N->real^N^N) (lrm4 (\z. c %% G z)) z u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `\z. c %% (G:real^N->real^N^N) z`; `G:real^N->real^N^N`;
                     `lrm4 (\z. c %% (G:real^N->real^N^N) z)`; `U:real^N->bool`]
             LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SCALE THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `lnabla_iter 4 l (G:real^N->real^N^N) (\x u. c * lrm4 G x u) z u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `G:real^N->real^N^N`; `G:real^N->real^N^N`;
                     `lrm4 (\z. c %% (G:real^N->real^N^N) z)`;
                     `\x:real^N u. c * lrm4 (G:real^N->real^N^N) x u`; `U:real^N->bool`]
             LRG_LNABLA_ITER_LOCAL) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                   `lrm4 (G:real^N->real^N^N)`; `c:real`; `&0`] LRG_LNABLA_ITER_LINCOMB) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    DISCH_THEN(MP_TAC o SPECL [`l:num`; `z:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lrm_deriv_norm2; RFA_LTNORM2_METRIC_SCALE] THEN
  SUBGOAL_THEN
   `ltnorm2 (4 + l) (G:real^N->real^N^N)
      (lnabla_iter 4 l (\z. c %% G z) (lrm4 (\z. c %% G z))) y =
    ltnorm2 (4 + l) G (\x u. c * lnabla_iter 4 l G (lrm4 G) x u) y`
  SUBST1_TAC THENL [REWRITE_TAC[ltnorm2] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LRG_LTNORM2_CMUL; REAL_MUL_ASSOC; ETA_AX] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_INV] THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;



(* ========================================================================= *)
(* The main theorem RFA_P2A_REQ_SHI_SCALED: Shi's interior estimate for      *)
(* nabla Rm in scale-invariant form, from RFA_P2_THM_3_28 at l = 1,          *)
(* K = r = tau = 1 for the parabolically rescaled flow r^-2 g(r^2 t).        *)
(* ========================================================================= *)

let RFA_P2A_REQ_SHI_SCALED = prove
 (`!u:A->bool. P2A_REQ_SHI_SCALED_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_REQ_SHI_SCALED_STATEMENT] THEN
  MP_TAC(SPEC `u:A->bool` RFA_P2_THM_3_28) THEN REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`1`; `&1`; `&1`; `&1`]) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `max C1 (&1)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `x:A`; `r:real`] THEN
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
  ABBREV_TAC `q = inv(r pow 2)` THEN
  SUBGOAL_THEN `&0 < q /\ sqrt q = inv r /\ q * r pow 2 = &1 /\ q pow 3 = inv(r pow 6)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SQRT_INV] THEN AP_TERM_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q * b) / q = b /\ &1 / sqrt q = r /\ (&1 / &2) / sqrt q = r / &2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < q` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
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
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
        `q * r pow 2 = &1`) (concl th))) THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `a < t / q /\ t / q <= b` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) b) x r` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 = q / q` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) b) x (r / &2)` THEN
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
                 `q:real`; `1`; `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`]
         RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) b)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `1 + 2 = 3`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * inv(r pow 6)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
      `q pow 3 = inv(r pow 6)`) (concl th))) THEN
    UNDISCH_TAC `inv q pow 3 *
                 lrm_deriv_norm2 1
                   (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                      ((g:real->A->real^3^3) b))
                   (SND(chart_at atlas y) y) <= C1` THEN
    SUBGOAL_THEN `&0 < q pow 3` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_INV] THEN
    SPEC_TAC(`q pow 3`,`p:real`) THEN
    SPEC_TAC(`lrm_deriv_norm2 1
                (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                   ((g:real->A->real^3^3) b))
                (SND(chart_at atlas y) y)`,`D:real`) THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_INV] THEN
    REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

