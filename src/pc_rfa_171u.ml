(* ========================================================================= *)
(* Unit pc_rfa_171u: piece U of the proof of MT Prop 17.1.  At the earlier   *)
(* base time tt n = ts n - Tb / Q n, Q n = R(x n, ts n), the scalar          *)
(* curvature of the counterexample sequence is bounded on the rescaled       *)
(* tt-balls along a subsequence (RFA_171_UTB, used in pc_p3_c171d):          *)
(* P2BU_SLICE_DBOUND at tt n.  Its inputs at tt come from the Step B bounds  *)
(* on ts-balls through RFA_171_BALL_FWD: tt-balls lie in ts-balls of twice   *)
(* the radius, by a one-sided metric comparison g(ts) <= exp(4 k (ts - s))   *)
(* g(s) under sec >= -k (RFA_171_VIEW_BALL_UP), with k = e Q from            *)
(* Hamilton-Ivey pinching where R <= K Q and Q is large                      *)
(* (RFA_171_PINCH_SECMIN).                                                   *)
(* ========================================================================= *)

needs "src/pc_p3_c171a.ml";;
needs "src/pc_p2c_bugq.ml";;
needs "src/pc_p2c_blowup.ml";;
needs "src/pc_p2c_horns.ml";;
needs "src/pc_p2c_cg.ml";;
needs "src/pc_p2c_t533.ml";;
needs "src/pc_p2b_capfix.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_p2b_a4s.ml";;
needs "src/pc_p3_c172e.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The one-sided comparison of the metrics of a Ricci flow on                *)
(* a fixed manifold.  If Ric(v,v) >= --k |v|^2 at z on (sg,b), then          *)
(* |v|^2 at b is at most exp(2 k (b - sg)) |v|^2 at sg (the upper half of    *)
(* RFA_UPTO_QFORM_EQUIV with its proof, the one-sided Gronwall               *)
(* RFU_GRONWALL_UP in place of RFA_GRONWALL_2SIDED).                         *)
(* ------------------------------------------------------------------------- *)

let RFA_171_QFORM_UP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) z sg k v.
     ricci_flow_on (top,atlas) a b g /\
     (!c. c IN atlas
          ==> ?e Fx. &0 < e /\
                     smooth_map_on
                       (interval(lift a,lift(b + e)) PCROSS IMAGE (SND c) (FST c)) Fx /\
                     !t y. a < t /\ t <= b /\ y IN IMAGE (SND c) (FST c)
                           ==> Fx(pastecart (lift t) y) =
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c (g t) y)) /\
     z IN topspace top /\ a < sg /\ sg <= b /\
     (!s. sg < s /\ s < b
          ==> --(k * (v dot (g s z ** v))) <= mfd_ricci atlas (g s) z v v)
     ==> v dot (g b z ** v) <= exp(&2 * k * (b - sg)) * (v dot (g sg z ** v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ext")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ric")))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  ASM_CASES_TAC `sg:real = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0;
                    REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "ext" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A) IN atlas`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `y0 = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) z` THEN
  SUBGOAL_THEN `y0 IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                             (FST(chart_at atlas z))` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. v dot ((g:real->A->real^N^N) s z ** v)`;
                 `\s. --(&2) * mfd_ricci atlas ((g:real->A->real^N^N) s) (z:A) v v`;
                 `&2 * k`; `sg:real`; `b:real`] RFU_GRONWALL_UP) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC
       `\r. drop((\m:real^(N,N)finite_prod. lift(v dot ((matrify m:real^N^N) ** v)))
                 ((FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                  (pastecart (lift r) y0)))` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        REWRITE_TAC[LIFT_DROP] THEN
        SUBGOAL_THEN
         `(FF:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift r) y0) =
          vectorize(metric_local atlas (chart_at atlas (z:A))
                                 ((g:real->A->real^N^N) r) y0)`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[MATRIFY_VECTORIZE] THEN EXPAND_TAC "y0" THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `(g:real->A->real^N^N) r`; `z:A`] METRIC_LOCAL_AT) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MP_TAC(ISPECL
         [`interval(lift a,lift(b + e)) PCROSS
           IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                 (FST(chart_at atlas z))`;
          `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`;
          `\m:real^(N,N)finite_prod. lift(v dot ((matrify m:real^N^N) ** v))`;
          `y0:real^N`; `r:real`] RFA_TSLICE_CONTINUOUS) THEN
        REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS;
                       IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[]]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      USE_THEN "ric" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* sec_min of the region family p2c_vfam V W b at a time s in                *)
(* (a,b] is at least sec_min of the slice s (the sectional curvatures of the *)
(* family are those of the slice in the directions moved by the chart        *)
(* transition; the proof of P2AP_VFAM_RM_NORM_LE with the lower bound        *)
(* RFA_SEC_GE_SECMIN in place of MFD_SECTIONAL_LE_RM_NORM).                   *)
(* ------------------------------------------------------------------------- *)

let RFA_171_VFAM_SECMIN_GE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s x.
     p2a_svs V /\ p2a_region V W a b /\ a < s /\ s <= b /\ x IN W
     ==> mfd_sec_min (rfs_vatlas V s) (rfs_vmetric V s) x <=
         mfd_sec_min (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b s) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AP_REGION_PERSISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s) /\
    x IN topspace(rfs_vtop V b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `x:A`] P2AP_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[p2c_vfam; ETA_AX] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MFD_SEC_MIN_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P3S_SECMIN_GE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `x:A`]
         MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[mfd_sectional; SND] THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^3) (U INTER W)` THEN
  SUBGOAL_THEN `open(O:real^3->bool) /\ (phi:A->real^3) x IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s) (rfs_vatlas V s) O
              (chart_inv (U:A->bool,phi:A->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_EQ THEN EXISTS_TAC `(\y:A. y) o chart_inv (U:A->bool,phi:A->real^3)` THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
      `W:A->bool`; `W:A->bool`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "O" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2AP_REGION_DIFFEO THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "O" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                     `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lsectional (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                 (U INTER W,phi:A->real^3) (p2c_vfam V W b s)) (phi x) u v =
    lsectional (rfs_pullback (rfs_vatlas V s) (chart_inv (U,phi)) (rfs_vmetric V s))
               (phi x) u v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AP_VFAM_PULLBACK_LOCAL THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s`;
                 `O:real^3->bool`; `chart_inv (U:A->bool,phi:A->real^3)`;
                 `(phi:A->real^3) x`; `u:real^3`; `v:real^3`]
         APX_PULLBACK_SECTIONAL_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN
  EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (x:A)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U':A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `U:A->bool`; `phi:A->real^3`; `U':A->bool`;
                 `psi:A->real^3`] MFDR_DIFFEO_CHART_REP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MATCH_MP_TAC P2AP_REGION_DIFFEO THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^3) x` o MATCH_MP P2AP_DIFFEO_DERIV_INJ) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->real^3) o (\y:A. y) o chart_inv (U:A->bool,phi:A->real^3) =
                psi o chart_inv (U,phi)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`frechet_derivative ((psi:A->real^3) o chart_inv (U:A->bool,phi:A->real^3))
                                     (at (phi(x:A)))`; `{vec 0:real^3,u,v}`]
         COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]));;


(* ------------------------------------------------------------------------- *)
(* The one-sided comparison on a persisting set of a view.                   *)
(* With sec >= --k on (a,b] x W the metric at b is at most exp(4 k (b - s))  *)
(* times the metric at s (Ric >= --2 k g in dimension 3,                    *)
(* CMPZ_MFD_RICCI_SEC_LOWER), on the region family (RFA_171_METRIC_UP, after *)
(* P2AP_METRIC_COMPARE) and unrestricted (RFA_171_VIEW_QF_UP, after          *)
(* P2BU_VIEW_QF_CMP); then earlier balls lie in later balls                  *)
(* (RFA_171_VIEW_BALL_UP, the proof of P2BU_VIEW_BALL_IN with this          *)
(* comparison).  No upper curvature bound is needed.                        *)
(* ------------------------------------------------------------------------- *)

let RFA_171_METRIC_UP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b k s y w.
     p2a_svs V /\ p2a_region V W a b /\
     (!t z. a < t /\ t <= b /\ z IN W
            ==> --k <= mfd_sec_min (rfs_vatlas V t) (rfs_vmetric V t) z) /\
     a < s /\ s <= b /\ y IN W
     ==> w dot (p2a_rmetric V W b b y ** w) <=
         exp(&4 * k * (b - s)) * (w dot (p2a_rmetric V W b s y ** w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[P2AP_RMETRIC_VFAM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AP_REGION_UPTO) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop V b) W)
      (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b) W)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:A) IN topspace(subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
                  P2AP_REGION_PERSISTS) THEN
    ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `a:real`; `b:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b`;
                 `y:A`; `s:real`; `&2 * k`; `w:real^3`] RFA_171_QFORM_UP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                        (p2c_vfam V W b t)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `a:real`; `b:real`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W b`; `t:real`] P2AP_UPTO_RIEM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `--k <= mfd_sec_min (restrict_atlas (rfs_vatlas (V:(real->A topology)#
               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
               (p2c_vfam V W b t) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_sec_min (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                    (rfs_vmetric V t) y` THEN
      CONJ_TAC THENL
       [USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFA_171_VFAM_SECMIN_GE THEN EXISTS_TAC `a:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W b t`; `y:A`; `--k`; `w:real^3`]
                  CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_sec_min (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                    (p2c_vfam V W b t) y` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN
      EXISTS_TAC `subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_ARITH `&2 * (&2 * k) * d = &4 * k * d`]]);;

let RFA_171_VIEW_QF_UP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b k s y w.
     p2c_regular_view V /\ rfs_persists V W a b /\
     (!t z. a < t /\ t <= b /\ z IN W
            ==> --k <= mfd_sec_min (rfs_vatlas V t) (rfs_vmetric V t) z) /\
     a < s /\ s < b /\ y IN W
     ==> w dot (rfs_vmetric V b y ** w) <=
         exp(&4 * k * (b - s)) *
         (w dot (mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V s) (\x. x)
                   (rfs_vmetric V s) y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
                open_in (rfs_vtop V b) (W:A->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) a b` THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `W:A->bool`; `y:A`] SNGL_RESTRICT_QF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^3->real^3` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "J"))) THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^3` o SPEC `w:real^3`) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `k:real`;
                 `s:real`; `y:A`; `v:real^3`] RFA_171_METRIC_UP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2CV_RV_SVS; REAL_LT_IMP_LE] THEN MATCH_MP_TAC P2CV_RV_REGION THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[P2AP_RMETRIC_VFAM; p2c_vfam] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NE] THEN REWRITE_TAC[ETA_AX]);;

let RFA_171_VIEW_BALL_UP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b k s x z R R0 rho.
     p2c_regular_view V /\ rfs_persists V W a b /\
     (!t y. a < t /\ t <= b /\ y IN W
            ==> --k <= mfd_sec_min (rfs_vatlas V t) (rfs_vmetric V t) y) /\
     a < s /\ s < b /\
     compact_in (rfs_vtop V b) (rfs_vtop V b closure_of rfs_vball V b x R) /\
     rfs_vtop V b closure_of rfs_vball V b x R SUBSET W /\
     z IN rfs_vball V b x R0 /\ &0 < rho /\ exp(&2 * k * (b - s)) * rho <= R - R0
     ==> rfs_vball V s z rho SUBSET rfs_vball V b x R /\
         rfs_vball V s z rho SUBSET rfs_vball V b z (exp(&2 * k * (b - s)) * rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < exp(&2 * k * (b - s))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `R0 < R` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < exp(&2 * k * (b - s)) * rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball V b (x:A) R SUBSET topspace(rfs_vtop V b)` ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL; mfd_ball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_vball V b (x:A) R0 SUBSET rfs_vball V b x R` MP_TAC THENL
     [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                   `rfs_vball V b (x:A) R`] CLOSURE_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop V b) (W:A->bool) /\ open_in (rfs_vtop V s) W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) a b` THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `b:real` th) THEN MP_TAC(SPEC `s:real` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop V b) (rfs_vatlas V b) W (rfs_vtop V s) (rfs_vatlas V s) W
               (\y:A. y) (\y. y)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2CV_SLICE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN
  SUBGOAL_THEN
   `!q. q IN rfs_vball V s (z:A) rho
        ==> q IN rfs_vball V b x R /\ q IN rfs_vball V b z (exp(&2 * k * (b - s)) * rho)`
  (fun th -> MESON_TAC[th]) THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) b`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
    `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) b`;
    `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) s`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) s`;
    `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
    `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`; `x:A`; `z:A`; `R:real`; `R0:real`;
    `exp(&4 * k * (b - s))`; `&0`; `rho:real`; `q:A`] LIM_PB_BALL_PREIMAGE) THEN
  REWRITE_TAC[REAL_SUB_RZERO; SQRT_1; REAL_MUL_LID; REAL_DIV_1; P2BU_SQRT_EXP4] THEN
  REWRITE_TAC[GSYM P2CO_VBALL; IMAGE_ID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_LE_REFL; REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `k:real`;
                   `s:real`; `y:A`; `v:real^3`] RFA_171_VIEW_QF_UP) THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Hamilton-Ivey pinching makes the negative part of the                     *)
(* sectional curvature small against a large scale Q where R <= K Q:        *)
(* sec_min >= --(e Q) once Q exceeds a bound depending on e and K (the       *)
(* arithmetic of P2CP_PINCH_CONTRA with K0 = 2 e and R0 = K - 1).            *)
(* ------------------------------------------------------------------------- *)

let RFA_171_PINCH_SECMIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t y e K Q.
     rfs_pinched V /\ &0 <= t /\ y IN topspace(rfs_vtop V t) /\ &0 < e /\ &0 < Q /\
     &2 / (&2 * e) * (exp(&3) + exp(&4 + abs((K - &1) + &1) / (&2 * e))) < Q /\
     rfs_vscalar V t y <= K * Q
     ==> --(e * Q) <= mfd_sec_min (rfs_vatlas V t) (rfs_vmetric V t) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `rfs_pinched_at (rfs_vatlas V t) (rfs_vmetric V t) t (y:A)` MP_TAC THENL
   [UNDISCH_TAC `rfs_pinched (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3))` THEN
    REWRITE_TAC[P2CP_PINCHED_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_pinched_at] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`&2 * e`; `K - &1`; `Q:real`;
                 `mfd_sec_min (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                    (rfs_vmetric V t) (y:A)`;
                 `mfd_scalar (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                    (rfs_vmetric V t) (y:A)`; `t:real`] P2CP_PINCH_CONTRA) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t y <= K * Q` THEN
  REWRITE_TAC[CONJUNCT1(SPEC_ALL P2C_VIEW_EXPAND)] THEN
  UNDISCH_TAC `mfd_sec_min (rfs_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                 (rfs_vmetric V t) (y:A) < --(e * Q)` THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Earlier balls inside later balls along the counterexample                 *)
(* sequence (RFA_171_BALL_FWD).  For z in the ts-ball of radius A / sqrt Q   *)
(* and tt <= s <= ts, the s-ball of radius rho / sqrt Q about z lies in the  *)
(* ts-ball of radius 2 rho / sqrt Q about z, for large n: the Step B bounds  *)
(* on the ts-ball of radius (A + 2 rho + 1) / sqrt Q give R <= K Q there, so *)
(* sec >= --(e Q) with e = 1 / (4 Tb) once Q is large (RFA_171_PINCH_SECMIN) *)
(* and the distortion factor over a time Tb / Q is exp(1/2) <= 2.            *)
(* ------------------------------------------------------------------------- *)

let RFA_171_EXP_LE2 = prove
 (`!e Q Tb d. &0 < e /\ &0 < Q /\ &4 * e * Tb <= &1 /\ &0 <= d /\ d <= Tb * inv Q
              ==> exp(&2 * (e * Q) * d) <= &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e * Q) * d <= e * Tb` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(e * Q) * (Tb * inv Q)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (e * Q) * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 * (e * Q) * d` REAL_EXP_BOUND_LEMMA) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The counterexample sequence: regular pinched views, histories in the     *)
(* setting, base points in the slices at ts, Q > 0 and Q -> infinity.        *)

let RFA_171_CEX_VF = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
           p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x)
           ==> (!n. p2c_regular_view (rfs_view (hs n)) /\
                    rfs_history_ok (hs n) /\ rfs_pinched (rfs_view (hs n)) /\
                    x n IN topspace(rfs_top_at (hs n) (ts n)) /\
                    &0 < rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
               (!B. ?N. !n. N <= n ==> B < rfs_vscalar (rfs_view (hs n)) (ts n) (x n))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[p3h_cexseq] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
  REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok ((hs:num->(A)rfs_history) n) /\ rfs_pinched (rfs_view (hs n))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) ((dlt:num->real) n)
                   ((rs':num->num->real) n,(ks':num->num->real) n,(dd:num->num->real) n)
                   ((hs:num->(A)rfs_history) n)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((r:num->real) n pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]]);;

(* One view: the containment for one index, from the bounds on the ts-ball *)
(* of radius (A + 2 rho + 1) / sqrt Q over (ts - (Tb + dl) / Q, ts].        *)

let RFA_171_FWD_ONE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x ts Q Tb e dl K A rho s z.
     (!t y. y IN topspace(rfs_vtop V t) ==> &0 <= t) /\
     (!t y. ts - (Tb + dl) * inv Q < t /\ t <= ts /\
            y IN rfs_vball V ts x ((A + &2 * rho + &1) * inv(sqrt Q))
            ==> rfs_vscalar V t y <= K * Q) /\
     p2c_regular_view V /\ rfs_pinched V /\ compact_space (rfs_vtop V ts) /\
     &0 < Q /\ &0 < Tb /\ &0 < e /\ &4 * e * Tb <= &1 /\ &0 < dl /\ &0 < rho /\
     &2 / (&2 * e) * (exp(&3) + exp(&4 + abs((K - &1) + &1) / (&2 * e))) < Q /\
     rfs_persists V (rfs_vball V ts x ((A + &2 * rho + &1) * inv(sqrt Q)))
       (ts - (Tb + dl) * inv Q) ts /\
     ts - Tb * inv Q <= s /\ s <= ts /\ z IN rfs_vball V ts x (A * inv(sqrt Q))
     ==> rfs_vball V s z (rho * inv(sqrt Q)) SUBSET
         rfs_vball V ts z (&2 * rho * inv(sqrt Q))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tpos") (CONJUNCTS_THEN2 (LABEL_TAC "RK")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < inv(sqrt Q) /\ &0 < inv Q /\ &0 < rho * inv(sqrt Q) /\ &0 < dl * inv Q`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]) THEN
    ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace(rfs_vtop V ts) /\ (x:A) IN topspace(rfs_vtop V ts)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN rfs_vball V ts x (A * inv(sqrt Q))` THEN
    REWRITE_TAC[P2CO_VBALL; mfd_ball; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `ts:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = ts` THENL
   [ASM_REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN
    UNDISCH_TAC `&0 < rho * inv(sqrt Q)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s < ts` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * (e * Q) * (ts - s)) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_171_EXP_LE2 THEN EXISTS_TAC `Tb:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* sec >= --(e Q) on the persisting ball *)
  SUBGOAL_THEN
   `!t y. ts - (Tb + dl) * inv Q < t /\ t <= ts /\
          y IN rfs_vball V ts (x:A) ((A + &2 * rho + &1) * inv(sqrt Q))
          ==> --(e * Q) <= mfd_sec_min (rfs_vatlas V t) (rfs_vmetric V t) y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop V t)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`;
                     `rfs_vball V ts (x:A) ((A + &2 * rho + &1) * inv(sqrt Q))`;
                     `ts - (Tb + dl) * inv Q`; `ts:real`; `t:real`] P2CV_PERSISTS_AT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_171_PINCH_SECMIN THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "tpos" MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      USE_THEN "RK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ts - (Tb + dl) * inv Q < s` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in (rfs_vtop V ts)
      (rfs_vtop V ts closure_of rfs_vball V ts (x:A) ((A + &2 * rho) * inv(sqrt Q)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_vtop V ts closure_of rfs_vball V ts (x:A) ((A + &2 * rho) * inv(sqrt Q)) SUBSET
    rfs_vball V ts x ((A + &2 * rho + &1) * inv(sqrt Q))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_cball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) (x:A)
                  ((A + &2 * rho) * inv(sqrt Q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[P2CO_VBALL; mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[P2CO_VBALL; mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(A + &2 * rho) * inv(sqrt Q)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < inv(sqrt Q)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * (e * Q) * (ts - s)) * rho * inv(sqrt Q) <=
                (A + &2 * rho) * inv(sqrt Q) - A * inv(sqrt Q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * rho * inv(sqrt Q)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`;
                 `rfs_vball V ts (x:A) ((A + &2 * rho + &1) * inv(sqrt Q))`;
                 `ts - (Tb + dl) * inv Q`; `ts:real`; `e * Q`; `s:real`; `x:A`; `z:A`;
                 `(A + &2 * rho) * inv(sqrt Q)`; `A * inv(sqrt Q)`; `rho * inv(sqrt Q)`]
                RFA_171_VIEW_BALL_UP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(SET_RULE `(t:A->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* The exported form, in the setting of RFA_171_UTB: the counterexample      *)
(* sequence and the Step B bounds.                                           *)

let RFA_171_BALL_FWD = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x Tb.
           &0 < Tb /\
           p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
           (!A. &0 < A
                ==> ?dl K N. &0 < dl /\ &0 <= K /\
                      !n. N <= n
                          ==> rfs_persists (rfs_view (hs n))
                                (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                   (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                (ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                (ts n) /\
                              !s y. ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                    s <= ts n /\
                                    y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                           (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                    ==> rfs_vscalar (rfs_view (hs n)) s y <=
                                        K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n))
           ==> !A rho. &0 < A /\ &0 < rho
                 ==> ?N. !n z s.
                       N <= n /\
                       ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) <= s /\
                       s <= ts n /\
                       z IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                              (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                       ==> rfs_vball (rfs_view (hs n)) s z
                             (rho * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))) SUBSET
                           rfs_vball (rfs_view (hs n)) (ts n) z
                             (&2 * rho * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (LABEL_TAC "SB"))) THEN
  MP_TAC(ISPEC `u:A->bool` RFA_171_CEX_VF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`]) THEN
  USE_THEN "CEX" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "VF") (LABEL_TAC "QINF")) THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `rho:real`] THEN STRIP_TAC THEN
  USE_THEN "SB" (MP_TAC o SPEC `A + &2 * rho + &1`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SBA")))))) THEN
  USE_THEN "QINF" (X_CHOOSE_TAC `N2:num` o SPEC
    `&2 / (&2 * inv(&4 * Tb)) *
     (exp(&3) + exp(&4 + abs((K - &1) + &1) / (&2 * inv(&4 * Tb))))`) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:A`; `s:real`] THEN STRIP_TAC THEN
  USE_THEN "VF" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "SBA" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * Tb) /\ &4 * inv(&4 * Tb) * Tb <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < Tb` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!t y. y IN topspace(rfs_vtop (rfs_view ((hs:num->(A)rfs_history) n)) t) ==> &0 <= t) /\
    compact_space (rfs_vtop (rfs_view (hs n)) (ts n))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfs_view; rfs_vtop] THEN CONJ_TAC THENL
     [MESON_TAC[P3H_TOPSPACE_TIME_POS];
      MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) n)`; `(x:num->A) n`; `(ts:num->real) n`;
                 `rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) ((ts:num->real) n)
                    ((x:num->A) n)`;
                 `Tb:real`; `inv(&4 * Tb)`; `dl:real`; `K:real`; `A:real`; `rho:real`;
                 `s:real`; `z:A`] RFA_171_FWD_ONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The inputs of P2BU_SLICE_DBOUND at the base time                          *)
(* tt n = ts n - Tb / Q n with the scale Q n = R(x n, ts n).  Each tt-ball   *)
(* of radius A / sqrt Q lies in the ts-ball of radius 2 A / sqrt Q           *)
(* (RFA_171_BALL_FWD), so it persists over (tt - dl / Q, tt] with           *)
(* abs Rm <= K Q there (RFA_171_TT_ONE, RFA_171_TT_FACTS); the volume at     *)
(* (x n, tt n) from the noncollapsing hypothesis (RFA_171_VOL_ONE, the       *)
(* argument of P2BU_SEQ_VOL with a general scale q); canonical               *)
(* neighbourhoods at tt for R >= 4 Q (RFA_171_CANON_TT, from                 *)
(* P3H_171_CANON_ABOVE).                                                      *)
(* ------------------------------------------------------------------------- *)

let RFA_171_ARITH_WIN = prove
 (`!t d Q. &0 < Q ==> d <= Q * (t - (t - d * inv Q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Q * (t - (t - d * inv Q)) = d` (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
  UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD);;

let RFA_171_VOL_ONE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t q kappa r0 dl K.
     (!s y. t - dl * inv q < s /\ s <= t /\ y IN rfs_vball V t x (&1 * inv(sqrt q))
            ==> &0 <= s /\ y IN topspace(rfs_vtop V s) /\ p3_vrm V s y <= K * q) /\
     p3_noncoll_at V kappa r0 x t /\
     p2c_regular_view V /\ x IN topspace(rfs_vtop V t) /\
     &0 < kappa /\ &0 < r0 /\ &0 < dl /\ &0 < K /\ &0 < q /\
     (min (&1) (min (sqrt dl) (inv(sqrt K))) / r0) pow 2 < q /\
     rfs_persists V (rfs_vball V t x (&1 * inv(sqrt q))) (t - dl * inv q) t
     ==> ?v. mfd_has_volume (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t)
               (rfs_vball V t x (min (&1) (min (sqrt dl) (inv(sqrt K))) * inv(sqrt q))) v /\
             kappa * (min (&1) (min (sqrt dl) (inv(sqrt K))) * inv(sqrt q)) pow 3 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vrm") (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(min (&1) (min (sqrt dl) (inv(sqrt K))) / r0) pow 2 < q` THEN
  ABBREV_TAC `eta = min (&1) (min (sqrt dl) (inv(sqrt K)))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 /\ eta pow 2 <= dl /\ K * eta pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt dl /\ &0 < inv(sqrt K) /\ sqrt dl pow 2 = dl /\
                  inv(sqrt K) pow 2 = inv K` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_POW_INV];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `eta <= sqrt dl /\ eta <= inv(sqrt K)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      EXPAND_TAC "eta" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt dl pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * inv(sqrt K) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_IMP_LE];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  ABBREV_TAC `r = eta * inv(sqrt q)` THEN
  SUBGOAL_THEN `&0 < sqrt q /\ sqrt q pow 2 = q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ r <= &1 * inv(sqrt q) /\ r pow 2 <= dl * inv q /\
                K * q <= inv(r pow 2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r pow 2 = eta pow 2 / q` ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
      ASM_REWRITE_TAC[real_div];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV];
      EXPAND_TAC "r" THEN REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `eta / r0 < sqrt q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_INV_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
      SUBGOAL_THEN `(K * q) * eta pow 2 = (K * eta pow 2) * q` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dl * inv q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  REWRITE_TAC[p3_noncoll_at] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_parabolic_exists] THEN MATCH_MP_TAC P2CD_PERSISTS_MONO THEN
    EXISTS_TAC `t - dl * inv q` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    EXISTS_TAC `rfs_vball V t (x:A) (&1 * inv(sqrt q))` THEN
    EXISTS_TAC `t:real` THEN ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_REFL];
      UNDISCH_TAC `rfs_persists V (rfs_vball V t (x:A) (&1 * inv(sqrt q))) (t - dl * inv q) t` THEN
      REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM p3_vrm] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * q` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "vrm" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:A) IN rfs_vball V t x r` THEN
      REWRITE_TAC[P2CO_VBALL] THEN
      SUBGOAL_THEN `mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) (x:A) r SUBSET
                    mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x
                      (&1 * inv(sqrt q))` MP_TAC THENL
       [MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[]; SET_TAC[]]]]);;

(* One view: from the Step B bounds on the ts-ball of radius 2 A / sqrt Q   *)
(* and the containment of the tt-ball of radius A / sqrt Q in it.           *)

let RFA_171_TT_ONE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x ts Q Tb dl K A.
     (!s y. ts - (Tb + dl) * inv Q < s /\ s <= ts /\
            y IN rfs_vball V ts x ((&2 * A) * inv(sqrt Q))
            ==> rfs_vscalar V s y <= K * Q) /\
     (!t y. y IN topspace(rfs_vtop V t) ==> &0 <= t) /\
     p2c_regular_view V /\ rfs_pinched V /\
     &1 <= Q /\ &0 < Tb /\ &0 < dl /\ &0 <= K /\ &0 < A /\ x IN topspace(rfs_vtop V ts) /\
     rfs_persists V (rfs_vball V ts x ((&2 * A) * inv(sqrt Q))) (ts - (Tb + dl) * inv Q) ts /\
     rfs_vball V (ts - Tb * inv Q) x (A * inv(sqrt Q)) SUBSET
     rfs_vball V ts x (&2 * A * inv(sqrt Q))
     ==> x IN topspace(rfs_vtop V (ts - Tb * inv Q)) /\
         rfs_persists V (rfs_vball V (ts - Tb * inv Q) x (A * inv(sqrt Q)))
           (ts - Tb * inv Q - dl * inv Q) (ts - Tb * inv Q) /\
         !s y. ts - Tb * inv Q - dl * inv Q < s /\ s <= ts - Tb * inv Q /\
               y IN rfs_vball V (ts - Tb * inv Q) x (A * inv(sqrt Q))
               ==> &0 <= s /\ y IN topspace(rfs_vtop V s) /\
                   p3_vrm V s y <= (&2 * K + &12 + &2 * exp(&4)) * Q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RK") (CONJUNCTS_THEN2 (LABEL_TAC "tpos")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt Q) /\ &0 < inv Q /\ &0 < Tb * inv Q /\ &0 < dl * inv Q`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]) THEN
    ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball V (ts - Tb * inv Q) (x:A) (A * inv(sqrt Q)) SUBSET
                rfs_vball V ts x ((&2 * A) * inv(sqrt Q))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ts - (Tb + dl) * inv Q < ts - Tb * inv Q /\ ts - Tb * inv Q <= ts`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`;
                 `rfs_vball V ts (x:A) ((&2 * A) * inv(sqrt Q))`;
                 `ts - (Tb + dl) * inv Q`; `ts:real`; `ts - Tb * inv Q`] P2CV_PERSISTS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN rfs_vball V ts x ((&2 * A) * inv(sqrt Q))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2CO_VBALL; MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop V (ts - Tb * inv Q))` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `ts - Tb * inv Q`; `x:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2HN_PERSIST_OPEN_SUB THEN
    EXISTS_TAC `rfs_vball V ts (x:A) ((&2 * A) * inv(sqrt Q))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`ts - (Tb + dl) * inv Q`; `ts:real`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN rfs_vball V ts x ((&2 * A) * inv(sqrt Q))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ts - (Tb + dl) * inv Q < s /\ s <= ts` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop V s)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`;
                   `rfs_vball V ts (x:A) ((&2 * A) * inv(sqrt Q))`;
                   `ts - (Tb + dl) * inv Q`; `ts:real`; `s:real`] P2CV_PERSISTS_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [USE_THEN "tpos" MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BU_VIEW_PINCH_RM_Q THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "RK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The tt-facts along the counterexample sequence, for every A > 0.         *)

let RFA_171_TT_FACTS = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x Tb.
           &0 < Tb /\
           p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
           (!A. &0 < A
                ==> ?dl K N. &0 < dl /\ &0 <= K /\
                      !n. N <= n
                          ==> rfs_persists (rfs_view (hs n))
                                (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                   (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                (ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                (ts n) /\
                              !s y. ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                    s <= ts n /\
                                    y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                           (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                    ==> rfs_vscalar (rfs_view (hs n)) s y <=
                                        K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n))
           ==> !A. &0 < A
                 ==> ?dl K N. &0 < dl /\ &0 < K /\
                       !n. N <= n
                           ==> x n IN topspace(rfs_vtop (rfs_view (hs n))
                                 (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))) /\
                               rfs_persists (rfs_view (hs n))
                                 (rfs_vball (rfs_view (hs n))
                                    (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                    (x n)
                                    (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                 (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) -
                                  dl * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                 (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))) /\
                               !s y. ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) -
                                     dl * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                     s <= ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
                                     y IN rfs_vball (rfs_view (hs n))
                                            (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                            (x n)
                                            (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                     ==> &0 <= s /\ y IN topspace(rfs_vtop (rfs_view (hs n)) s) /\
                                         p3_vrm (rfs_view (hs n)) s y <=
                                         K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (LABEL_TAC "SB"))) THEN
  MP_TAC(ISPEC `u:A->bool` RFA_171_CEX_VF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`]) THEN
  USE_THEN "CEX" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "VF") (LABEL_TAC "QINF")) THEN
  MP_TAC(ISPEC `u:A->bool` RFA_171_BALL_FWD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `Tb:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "BF")] THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "SB" (MP_TAC o SPEC `&2 * A`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SBA")))))) THEN
  USE_THEN "BF" (MP_TAC o SPECL [`&1`; `A:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "BFA")) THEN
  USE_THEN "QINF" (X_CHOOSE_TAC `N3:num` o SPEC `&1`) THEN
  MAP_EVERY EXISTS_TAC [`dl:real`; `&2 * K + &12 + &2 * exp(&4)`; `N1 + N2 + N3:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `&4` REAL_EXP_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "VF" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "SBA" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) ((x:num->A) n)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `N3:num`)) (concl th))) THEN
    UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. y IN topspace(rfs_vtop (rfs_view ((hs:num->(A)rfs_history) n)) t) ==> &0 <= t`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN MESON_TAC[P3H_TOPSPACE_TIME_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_vball (rfs_view ((hs:num->(A)rfs_history) n))
      (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) ((x:num->A) n))) (x n)
      (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))) SUBSET
    rfs_vball (rfs_view (hs n)) (ts n) (x n)
      (&2 * A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))`
  ASSUME_TAC THENL
   [USE_THEN "BFA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= d ==> t - d <= t`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ];
      MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) n)`; `(ts:num->real) n`;
                     `(x:num->A) n`] P2C_REGULAR_SLICE) THEN
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[P2CO_VBALL; P2C_RFS_VIEW_PARTS] THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) n)`; `(x:num->A) n`; `(ts:num->real) n`;
                 `rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) ((ts:num->real) n)
                    ((x:num->A) n)`;
                 `Tb:real`; `dl:real`; `K:real`; `A:real`] RFA_171_TT_ONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* Canonical neighbourhoods at all times s <= ts a where R >= 4 R(x a, ts a). *)

let RFA_171_CANON_TT = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
     p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x)
     ==> !a y s. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s) /\
                 &4 * rfs_vscalar (rfs_view (hs a)) (ts a) (x a) <=
                 rfs_vscalar (rfs_view (hs a)) s y
                 ==> p3_canon_at (rfs_view (hs a)) C eps y s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3h_cexseq] THEN STRIP_TAC THEN
  X_GEN_TAC `a:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
  REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &4` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `(dlt:num->real) a`; `(rs':num->num->real) a`;
                 `(ks':num->num->real) a`; `(dd:num->num->real) a`;
                 `(hs:num->(A)rfs_history) a`; `(r:num->real) a`; `(ts:num->real) a`;
                 `(x:num->A) a`; `&4`] P3H_171_CANON_ABOVE) THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The main theorem RFA_171_UTB.  eps0 is the bound of P2BU_SLICE_DBOUND;    *)
(* the sequence is shifted by an index N0 from which the base points lie in  *)
(* the slices at tt (RFA_171_TT_FACTS at A = 1), and the subsequence of      *)
(* P2BU_SLICE_DBOUND is shifted back.                                        *)
(* ------------------------------------------------------------------------- *)

let RFA_171_UTB = prove
 (`!u:A->bool.
   P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
   ==> ?eps0. &0 < eps0 /\
         !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa Tb.
            eps <= eps0 /\ &0 < kappa /\ &0 < Tb /\
            p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
            (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
                     ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
            (!a s. apx_sphere_sep (rfs_top_at (hs a) s) (rfs_atlas_at (hs a) s)) /\
            (!A. &0 < A
                 ==> ?dl K N. &0 < dl /\ &0 <= K /\
                       !n. N <= n
                           ==> rfs_persists (rfs_view (hs n))
                                 (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                 (ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                 (ts n) /\
                               !s y. ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                     s <= ts n /\
                                     y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                            (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                     ==> rfs_vscalar (rfs_view (hs n)) s y <=
                                         K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n))
            ==> ?sub D. p3_subseq sub /\ &0 < D /\
                  !A. &0 < A
                      ==> ?N. !n y. N <= n /\
                                y IN rfs_vball (rfs_view (hs (sub n)))
                                       (ts (sub n) - Tb * inv(rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) (x (sub n))))
                                       (x (sub n))
                                       (A * inv(sqrt(rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) (x (sub n)))))
                                ==> rfs_vscalar (rfs_view (hs (sub n)))
                                      (ts (sub n) - Tb * inv(rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) (x (sub n))))
                                      y <=
                                    D * rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) (x (sub n))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `(:real^3)`] P2BU_SLICE_DBOUND) THEN
  REWRITE_TAC[P2CK_CG_COMPACT; P2CP_THM_5_33; P2C_REQ_SLICE_FIX;
              MATCH_MP P2B_NONNEG_BOUNDED_SLICE_ROUTE (ISPEC `(:real^3)` P2AS_PROP_2_19_SEP)] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SD"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
    `dlt:num->real`; `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`;
    `dd:num->(num->real)`; `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`;
    `kappa:real`; `Tb:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (CONJUNCTS_THEN2 (LABEL_TAC "NC")
    (CONJUNCTS_THEN2 (LABEL_TAC "SEP") (LABEL_TAC "SB"))))))) THEN
  MP_TAC(ISPEC `u:A->bool` RFA_171_CEX_VF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`]) THEN
  USE_THEN "CEX" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "VF") (LABEL_TAC "QINF")) THEN
  SUBGOAL_THEN `&0 < eps /\ &2 <= C` STRIP_ASSUME_TAC THENL
   [USE_THEN "CEX" (MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[p3h_cexseq]) THEN
    REWRITE_TAC[p3h_inst] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:A->bool` RFA_171_TT_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `Tb:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "TT")] THEN
  USE_THEN "TT" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `N0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1")))))) THEN
  (* P2BU_SLICE_DBOUND for the sequence shifted by N0, at tt and with Q = R(x, ts) *)
  USE_THEN "SD" (MP_TAC o SPECL
    [`C:real`; `eps:real`;
     `\n. rfs_view ((hs:num->(A)rfs_history) (n + N0))`;
     `\n. (x:num->A) (n + N0)`;
     `\n. (ts:num->real) (n + N0) -
          Tb * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) (n + N0))) (ts (n + N0))
                     ((x:num->A) (n + N0)))`;
     `\n. rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) (n + N0))) ((ts:num->real) (n + N0))
            ((x:num->A) (n + N0))`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* the views, base points in the slices at tt, Q > 0 *)
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      USE_THEN "VF" (STRIP_ASSUME_TAC o SPEC `n + N0:num`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN MESON_TAC[P2C_HIST_NEG_EMPTY];
        USE_THEN "T1" (MP_TAC o SPEC `n + N0:num`) THEN
        ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    (* sphere separation *)
    CONJ_TAC THENL [REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* Q -> infinity *)
    CONJ_TAC THENL
     [X_GEN_TAC `B:real` THEN USE_THEN "QINF" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `N:num`)) (concl th))) THEN
      UNDISCH_TAC `N <= n:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    (* canonical neighbourhoods at tt for R >= 4 Q *)
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN
      STRIP_TAC THEN USE_THEN "VF" (STRIP_ASSUME_TAC o SPEC `n + N0:num`) THEN
      MP_TAC(ISPECL
        [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`] RFA_171_CANON_TT) THEN
      USE_THEN "CEX" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= d ==> t - d <= t`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ];
      ALL_TAC] THEN
    (* compact closures at tt *)
    CONJ_TAC THENL
     [X_GEN_TAC `A:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN
      USE_THEN "VF" (MP_TAC o SPEC `n + N0:num`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    (* Shi at tt *)
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
      USE_THEN "TT" (MP_TAC o SPEC `&4 * A`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TA")))))) THEN
      MP_TAC(ISPECL [`l:num`; `K:real`; `A:real`; `dl:real`] P2BU_SHI_VIEW_CC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CA:real` (LABEL_TAC "SHI")) THEN
      MAP_EVERY EXISTS_TAC [`CA:real`; `N:num`] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "TA" (MP_TAC o SPEC `n + N0:num`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `N <= n:num` THEN ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "VF" (STRIP_ASSUME_TAC o SPEC `n + N0:num`) THEN
      USE_THEN "SHI" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`(x:num->A) (n + N0)`;
        `(ts:num->real) (n + N0) -
         Tb * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) (n + N0))) (ts (n + N0))
                    ((x:num->A) (n + N0))) -
         dl * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) (n + N0))) (ts (n + N0))
                    ((x:num->A) (n + N0)))`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
        REWRITE_TAC[CLOSED_IN_CLOSURE_OF; P2C_RFS_VIEW_PARTS] THEN
        MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d < t`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_INV];
        MATCH_MP_TAC RFA_171_ARITH_WIN THEN ASM_REWRITE_TAC[];
        USE_THEN "TA" (MP_TAC o SPEC `n + N0:num`) THEN
        ANTS_TAC THENL [UNDISCH_TAC `N <= n:num` THEN ARITH_TAC; MESON_TAC[]]];
      ALL_TAC] THEN
    (* the volume at (x n, tt n) *)
    USE_THEN "QINF" (X_CHOOSE_TAC `N2:num` o SPEC
      `(min (&1) (min (sqrt dl1) (inv(sqrt K1))) / eps) pow 2`) THEN
    MAP_EVERY EXISTS_TAC [`min (&1) (min (sqrt dl1) (inv(sqrt K1)))`; `kappa:real`; `N2:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; REAL_LT_01];
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "T1" (MP_TAC o SPEC `n + N0:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "VF" (STRIP_ASSUME_TAC o SPEC `n + N0:num`) THEN
    MP_TAC(ISPECL
     [`rfs_view ((hs:num->(A)rfs_history) (n + N0))`; `(x:num->A) (n + N0)`;
      `(ts:num->real) (n + N0) -
       Tb * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) (n + N0))) (ts (n + N0))
                  ((x:num->A) (n + N0)))`;
      `rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) (n + N0))) ((ts:num->real) (n + N0))
         ((x:num->A) (n + N0))`;
      `kappa:real`; `eps:real`; `dl1:real`; `K1:real`] RFA_171_VOL_ONE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "NC" MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= d ==> t - d <= t`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ];
        RULE_ASSUM_TAC(REWRITE_RULE[P2C_RFS_VIEW_PARTS]) THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `N2:num`)) (concl th))) THEN
      UNDISCH_TAC `N2 <= n:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `D:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  EXISTS_TAC `\n. (sub:num->num) n + N0` THEN EXISTS_TAC `D:real` THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p3_subseq (sub:num->num)` THEN REWRITE_TAC[p3_subseq; LT_ADD_RCANCEL]);;

