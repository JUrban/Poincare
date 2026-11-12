(* ========================================================================= *)
(* pc_p2b_vscale: parabolic rescaling of regular views, shared by the        *)
(* no-bad-tube and the bad-tube units of MT Thm 10.2.  For                   *)
(* Q > 0 the view p2b_rescale_view V t Q (slices at t + s / Q, metrics       *)
(* multiplied by Q) of a regular view is regular                             *)
(* (P2BK_REGULAR_VIEW_RESCALE).  Reusable parts:                             *)
(*   P2BK_VS_PARTS (slices of the rescaled view), P2BK_VS_AFFINE_TIME,      *)
(*   P2BK_PERSISTS_RESCALE (time reparametrization of rfs_persists),        *)
(*   P2BK_RICCI_FLOW_ON_AFFINE, P2BK_RICCI_FLOW_FROM_AFFINE,                *)
(*   P2BK_RFS_FLOW_UPTO_AFFINE (the flow under g'(s) = Q g(t + s / Q)),     *)
(*   P2BK_RESTRICT_METRIC_CMUL, P2BK_PULLBACK_METRIC_CMUL,                  *)
(*   P2BK_VFAM_RESCALE (linearity of restriction, pullback and p2c_vfam),   *)
(*   P2BK_VFLOW_RESCALE, P2BK_VFLOW_FROM_RESCALE.                           *)
(* Uses RICCI_FLOW_TRANSLATE and RICCI_FLOW_RESCALE (pc_rf_basic; Ricci     *)
(* scale invariance RFB_MFD_RICCI_CMUL), RFB_SMOOTH_TIME_AFFINE,            *)
(* METRIC_LOCAL_CMUL and RIEMANNIAN_METRIC_CMUL (pc_mfd_riem).  The proofs  *)
(* of the ricci_flow_from and flow-upto cases follow                        *)
(* P2AU_RICCI_FLOW_FROM_RESCALE and P2AU_FLOW_UPTO_RESCALE (pc_p2a_flow),   *)
(* which are pure rescalings (no translation), are stated for p2a_flow_upto  *)
(* and lie in a 305-file closure; this unit needs only pc_p2b_defs.         *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The slices of a rescaled view, the affine time change, and               *)
(* the flow under g'(s) = Q g(t + s / Q).                                   *)
(* ========================================================================= *)

let P2BK_VS_PARTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t Q s.
     rfs_vtop (p2b_rescale_view V t Q) s = rfs_vtop V (t + s / Q) /\
     rfs_vatlas (p2b_rescale_view V t Q) s = rfs_vatlas V (t + s / Q) /\
     rfs_vmetric (p2b_rescale_view V t Q) s = (\y. Q %% rfs_vmetric V (t + s / Q) y)`,
  REWRITE_TAC[p2b_rescale_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2BK_VS_AFFINE_TIME = prove
 (`!Q t x s.
     &0 < Q
     ==> (Q * (x - t) < s <=> x < inv Q * s + t) /\
         (Q * (x - t) <= s <=> x <= inv Q * s + t) /\
         (s < Q * (x - t) <=> inv Q * s + t < x) /\
         (s <= Q * (x - t) <=> inv Q * s + t <= x) /\
         t + s / Q = inv Q * s + t /\
         Q * ((t + x / Q) - t) = x /\
         t + (Q * (x - t)) / Q = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv Q * s + t = s / Q + t` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x < s / Q + t <=> x - t < s / Q`;
              REAL_ARITH `x <= s / Q + t <=> x - t <= s / Q`;
              REAL_ARITH `s / Q + t < x <=> s / Q < x - t`;
              REAL_ARITH `s / Q + t <= x <=> s / Q <= x - t`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LE_LDIV_EQ] THEN
  REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
  UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD);;

let P2BK_PERSISTS_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t Q W a b.
     &0 < Q
     ==> (rfs_persists (p2b_rescale_view V t Q) W a b <=>
          rfs_persists V W (t + a / Q) (t + b / Q))`,
  REWRITE_TAC[FORALL_PAIR_THM; p2b_rescale_view; rfs_persists; rfs_vtop; rfs_vatlas;
              rfs_vmetric] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q * (u - t):real`) THEN
    ASM_SIMP_TAC[P2BK_VS_AFFINE_TIME] THEN
    ANTS_TAC THENL
     [MP_TAC(SPECL [`Q:real`; `t:real`; `u:real`; `a:real`] P2BK_VS_AFFINE_TIME) THEN
      MP_TAC(SPECL [`Q:real`; `t:real`; `u:real`; `b:real`] P2BK_VS_AFFINE_TIME) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_LADD; REAL_LE_LADD; REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ]]);;

let P2BK_RICCI_FLOW_ON_AFFINE = prove
 (`!top atlas a b (g:real->A->real^N^N) t Q.
     ricci_flow_on (top,atlas) a b g /\ &0 < Q
     ==> ricci_flow_on (top,atlas) (Q * (a - t)) (Q * (b - t))
                       (\s x. Q %% g (t + s / Q) x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `--t:real` o MATCH_MP RICCI_FLOW_TRANSLATE) THEN
  DISCH_THEN(MP_TAC o SPEC `Q:real` o MATCH_MP (REWRITE_RULE[IMP_CONJ] RICCI_FLOW_RESCALE)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `a:real = a' /\ b:real = b' /\ (g:real->A->real^N^N) = g'
                        ==> ricci_flow_on (top,atlas) a b g
                            ==> ricci_flow_on (top,atlas) a' b' g'`) THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC;
    REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `s / Q - --t = t + s / Q`]]);;

(* ========================================================================= *)
(* The affine time change g'(s) = Q g(t + s / Q) of flows                    *)
(* smooth up to the initial time (ricci_flow_from) and up to the final time  *)
(* (rfs_flow_upto): the chart extensions are composed with the affine map.   *)
(* ========================================================================= *)

let P2BK_RICCI_FLOW_FROM_AFFINE = prove
 (`!top atlas a b (g:real->A->real^N^N) t Q.
     ricci_flow_from (top,atlas) a b g /\ &0 < Q
     ==> ricci_flow_from (top,atlas) (Q * (a - t)) (Q * (b - t))
                         (\s x. Q %% g (t + s / Q) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2BK_RICCI_FLOW_ON_AFFINE] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[P2BK_VS_AFFINE_TIME] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN; ricci_flow_on]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `Q * e` THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum.
                Q % (Fm:real^(1,N)finite_sum->real^(N,N)finite_prod)
                      (pastecart (lift(inv Q * drop(fstcart z) + t)) (sndcart z))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MATCH_MP_TAC RFB_SMOOTH_TIME_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`a - e:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv Q * s + t = s / Q + t` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x < s / Q + t <=> x - t < s / Q`;
                REAL_ARITH `x <= s / Q + t <=> x - t <= s / Q`;
                REAL_ARITH `s / Q + t < x <=> s / Q < x - t`;
                REAL_ARITH `s / Q + t <= x <=> s / Q <= x - t`] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv Q * s + t`; `y:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `vectorize:real^N^N->real^(N,N)finite_prod`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv Q * s + t = s / Q + t` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `x < s / Q + t <=> x - t < s / Q`;
                  REAL_ARITH `x <= s / Q + t <=> x - t <= s / Q`;
                  REAL_ARITH `s / Q + t < x <=> s / Q < x - t`;
                  REAL_ARITH `s / Q + t <= x <=> s / Q <= x - t`] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL] THEN
    ASM_SIMP_TAC[P2BK_VS_AFFINE_TIME; ETA_AX]]);;

let P2BK_RFS_FLOW_UPTO_AFFINE = prove
 (`!top atlas a b (g:real->A->real^3^3) t Q.
     rfs_flow_upto (top,atlas) a b g /\ &0 < Q
     ==> rfs_flow_upto (top,atlas) (Q * (a - t)) (Q * (b - t))
                       (\s x. Q %% g (t + s / Q) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2BK_RICCI_FLOW_ON_AFFINE] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[P2BK_VS_AFFINE_TIME] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN; ricci_flow_on]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fm:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `Q * e` THEN
  EXISTS_TAC `\z:real^(1,3)finite_sum.
                Q % (Fm:real^(1,3)finite_sum->real^(3,3)finite_prod)
                      (pastecart (lift(inv Q * drop(fstcart z) + t)) (sndcart z))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MATCH_MP_TAC RFB_SMOOTH_TIME_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b + e:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv Q * s + t = s / Q + t` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x < s / Q + t <=> x - t < s / Q`;
                REAL_ARITH `x <= s / Q + t <=> x - t <= s / Q`;
                REAL_ARITH `s / Q + t < x <=> s / Q < x - t`;
                REAL_ARITH `s / Q + t <= x <=> s / Q <= x - t`] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv Q * s + t`; `y:real^3`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `vectorize:real^3^3->real^(3,3)finite_prod`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv Q * s + t = s / Q + t` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `x < s / Q + t <=> x - t < s / Q`;
                  REAL_ARITH `x <= s / Q + t <=> x - t <= s / Q`;
                  REAL_ARITH `s / Q + t < x <=> s / Q < x - t`;
                  REAL_ARITH `s / Q + t <= x <=> s / Q <= x - t`] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL] THEN
    ASM_SIMP_TAC[P2BK_VS_AFFINE_TIME; ETA_AX]]);;

(* ========================================================================= *)
(* Linearity of restriction, pullback and p2c_vfam in the                   *)
(* metric; the flow clauses of a rescaled view; regularity.                 *)
(* ========================================================================= *)

let P2BK_RESTRICT_METRIC_CMUL = prove
 (`!atlas W (g:A->real^N^N) k.
     restrict_metric atlas W (\x. k %% g x) = (\x. k %% restrict_metric atlas W g x)`,
  REWRITE_TAC[restrict_metric; METRIC_LOCAL_CMUL]);;

let P2BK_PULLBACK_METRIC_CMUL = prove
 (`!atlas atlas' (f:A->B) (g:B->real^N^N) k.
     mfd_pullback_metric atlas atlas' f (\y. k %% g y) =
     (\x. k %% mfd_pullback_metric atlas atlas' f g x)`,
  REWRITE_TAC[mfd_pullback_metric; METRIC_LOCAL_CMUL; mpullback; FUN_EQ_THM] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P2BK_VFAM_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t Q W b.
     &0 < Q
     ==> p2c_vfam (p2b_rescale_view V t Q) W b =
         (\s x. Q %% p2c_vfam V W (t + b / Q) (t + s / Q) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_vfam; P2BK_VS_PARTS; FUN_EQ_THM] THEN
  X_GEN_TAC `s:real` THEN
  SUBGOAL_THEN `(t + s / Q = t + b / Q) <=> (s = b)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EQ_ADD_LCANCEL; real_div; REAL_EQ_MUL_RCANCEL; REAL_INV_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = b` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[P2BK_PULLBACK_METRIC_CMUL; P2BK_RESTRICT_METRIC_CMUL; ETA_AX]);;

let P2BK_VFLOW_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t Q W a b.
     &0 < Q /\ p2c_vflow V W (t + a / Q) (t + b / Q)
     ==> p2c_vflow (p2b_rescale_view V t Q) W a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_vflow] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2BK_PERSISTS_RESCALE; P2BK_VFAM_RESCALE; P2BK_VS_PARTS] THEN
  SUBGOAL_THEN `Q * ((t + a / Q) - t) = a /\ Q * ((t + b / Q) - t) = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BK_VS_AFFINE_TIME]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop V (t + b / Q)) (W:A->bool)`;
                 `restrict_atlas (rfs_vatlas V (t + b / Q)) (W:A->bool)`;
                 `t + a / Q`; `t + b / Q`; `p2c_vfam V (W:A->bool) (t + b / Q)`;
                 `t:real`; `Q:real`] P2BK_RFS_FLOW_UPTO_AFFINE) THEN
  ASM_REWRITE_TAC[]);;

let P2BK_VFLOW_FROM_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t Q W a b.
     &0 < Q /\ p2c_vflow_from V W (t + a / Q) (t + b / Q)
     ==> p2c_vflow_from (p2b_rescale_view V t Q) W a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_vflow_from] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2BK_VFLOW_RESCALE; P2BK_VS_PARTS; P2BK_VFAM_RESCALE] THEN
  SUBGOAL_THEN `Q * ((t + a / Q) - t) = a /\ Q * ((t + b / Q) - t) = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BK_VS_AFFINE_TIME]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop V (t + b / Q)) (W:A->bool)`;
                 `restrict_atlas (rfs_vatlas V (t + b / Q)) (W:A->bool)`;
                 `t + a / Q`; `t + b / Q`; `p2c_vfam V (W:A->bool) (t + b / Q)`;
                 `t:real`; `Q:real`] P2BK_RICCI_FLOW_FROM_AFFINE) THEN
  ASM_REWRITE_TAC[]);;

let P2BK_REGULAR_VIEW_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t Q.
     p2c_regular_view V /\ &0 < Q ==> p2c_regular_view (p2b_rescale_view V t Q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (l,t) -> LABEL_TAC l t)
    (zip ["sl"; "fl"; "ff"; "ds"; "da"] (CONJUNCTS th))) THEN
  REWRITE_TAC[P2BK_VS_PARTS] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REMOVE_THEN "sl" (MP_TAC o SPEC `t + s / Q`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BK_VFLOW_RESCALE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fl" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GSYM P2BK_PERSISTS_RESCALE; REAL_LT_LADD; REAL_LT_DIV2_EQ];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BK_VFLOW_FROM_RESCALE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ff" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GSYM P2BK_PERSISTS_RESCALE; REAL_LT_LADD; REAL_LT_DIV2_EQ];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "ds" MATCH_MP_TAC THEN EXISTS_TAC `t + a / Q` THEN
    ASM_SIMP_TAC[GSYM P2BK_PERSISTS_RESCALE; REAL_LT_LADD; REAL_LE_LADD; REAL_LT_DIV2_EQ;
                 REAL_LE_DIV2_EQ];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    USE_THEN "da" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GSYM P2BK_PERSISTS_RESCALE; REAL_LT_LADD; REAL_LT_DIV2_EQ]]);;

