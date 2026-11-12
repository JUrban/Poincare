(* ========================================================================= *)
(* Unit pc_p3_s16small (Part 3 proofs; Ch 16): the small-scale part of MT    *)
(* Prop 16.1, i.e. Kleiner-Lott Sublemma 79.23 in a Ricci flow with surgery, *)
(* statement in pc_p3_s16sst.  MT's proof of Prop 16.1 treats a point of     *)
(* large curvature only at the scale R^(-1/2), while Def 14.15 quantifies    *)
(* over every scale r <= r0; KL's argument covers all of them.               *)
(*                                                                           *)
(* Take the largest admissible scale s in [r0,rr] (P3N_MAXSCALE; p3n_adm:    *)
(* the parabolic ball persists with abs Rm <= s^-2).  If s = rr the large-  *)
(* scale bound at rr steps down (P3N_ADM_STEPDOWN, Bishop-Gromov).  If      *)
(* s < rr, a point of the parabolic ball has R >= min(H/2, rr^-2/8)         *)
(* (P3N_TIGHT_EXISTS): either a larger ball persists and the joint          *)
(* continuity of R on persisting regions gives a cool tube, so a larger     *)
(* scale is admissible (P3N_TIGHT_B, contradiction), or the ball is exposed *)
(* by a surgery in the window, whose hot caps lie near (P3N_TIGHT_A).  At   *)
(* the hot point the canonical neighbourhood with KL's volume clause gives *)
(* small-ball noncollapsing at an inward point (P3N_CANONV_SMALL,           *)
(* P3N_INWARD_POINT), transported to time t0 by the metric comparison on   *)
(* the admissible region (P3N_PARAB_COMPARE, P3N_PARAB_XGEOM, P3N_XVOL),    *)
(* then stepped down (P3N_TIGHT_VOL).  Main theorem                          *)
(* P3N_SMALL_SCALE : |- !u. P3N_SMALL_SCALE_STATEMENT u.                     *)
(* ========================================================================= *)

needs "src/pc_p3_s16sst.ml";;
needs "src/pc_p3_s163.ml";;
needs "src/pc_p2b_flatknc.ml";;
needs "src/pc_p2c_hreg.ml";;
needs "src/pc_rfa_histc2c.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_p2b_cap.ml";;
needs "src/pc_p3_c17vol.ml";;
needs "src/pc_p3_s16end.ml";;
needs "src/pc_p2b_neckbd.ml";;
needs "src/pc_p2b_slice.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Prop 16.1, small scales, KL Sublemma 79.23: the Bishop-                   *)
(* Gromov step down.  If |Rm| <= rho^-2 on B(x,rho) and Vol B(x,rho) >=    *)
(* k rho^3, then Vol B(x,r) >= (k/2) r^3 for every 0 < r <= rho: relative  *)
(* volume comparison (CMP_RELVOL) with Ric >= -2 rho^-2 (P2AP_MFD_RICCI_ABS) *)
(* and the model volume bounds FLT_VMODEL_LOWER, FLT_VMODEL_UPPER.           *)
(* ========================================================================= *)

let P3N_BG_STEPDOWN = prove
 (`!top atlas (g:A->real^3^3) x rho k r v v'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < r /\ r <= rho /\
     compact_in top (top closure_of mfd_ball (top,atlas) g x rho) /\
     (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= inv(rho pow 2)) /\
     mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x rho) v /\ k * rho pow 3 <= v /\
     mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v'
     ==> k / &2 * r pow 3 <= v'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `r <= rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = inv(rho pow 2)` THEN
  SUBGOAL_THEN `&0 <= K /\ K * rho pow 2 <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBGOAL_THEN `&0 < rho pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
    ALL_TAC] THEN
  (* relative volume comparison *)
  MP_TAC(ISPECL [`(:A)`; `(:3)`] CMP_RELVOL) THEN REWRITE_TAC[CMP_RELVOL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `x:A`; `K:real`; `rho:real`; `r:real`; `rho:real`;
                            `v':real`; `v:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x rho` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `w:real^3`] P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `&0 <= w dot ((g:A->real^3^3) y ** w)` ASSUME_TAC THENL
     [ASM_CASES_TAC `w = vec 0:real^3` THENL
       [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `y:A`] RIEMANNIAN_METRIC_POS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_rm_norm atlas (g:A->real^3^3) y * (w dot (g y ** w)) <=
                  K * (w dot (g y ** w))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  (* the model volume bounds *)
  SUBGOAL_THEN `K * r pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * rho pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real`; `r:real`] (INST_TYPE [`:3`,`:N`] FLT_VMODEL_LOWER)) THEN
  MP_TAC(ISPECL [`K:real`; `rho:real`] FLT_VMODEL_UPPER) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `!s. &0 <= s ==> measure(ball(vec 0:real^3,s)) = s pow 3 * measure(ball(vec 0:real^3,&1))`
  (fun th -> ASM_SIMP_TAC[th; REAL_LT_IMP_LE]) THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `s:real`; `&1`] MEASURE_BALL_SCALING) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; DIMINDEX_3];
    ALL_TAC] THEN
  ABBREV_TAC `m = measure(ball(vec 0:real^3,&1))` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01]; ALL_TAC] THEN
  ABBREV_TAC `Vr = cmp_vmodel (:3) (--K) r` THEN
  ABBREV_TAC `Vrho = cmp_vmodel (:3) (--K) rho` THEN
  REPEAT DISCH_TAC THEN
  (* v' Vrho >= v Vr >= k rho^3 r^3 m, and Vrho <= 2 rho^3 m *)
  SUBGOAL_THEN `&0 < rho pow 3 /\ &0 < r pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `k * rho pow 3 * (r pow 3 * m) <= v' * (&2 * rho pow 3 * m)` MP_TAC THENL
   [ASM_CASES_TAC `&0 <= k` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v * Vr` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v' * Vrho` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_POS_LE) THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:A->real^3^3`; `mfd_ball (top,atlas) (g:A->real^3^3) x r`] THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_POS_LE) THEN
          MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                `g:A->real^3^3`; `mfd_ball (top,atlas) (g:A->real^3^3) x r`] THEN
          ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ARITH `&0 <= &2`]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * rho pow 3 * (r pow 3 * m) = (k / &2 * r pow 3) * (&2 * rho pow 3 * m) /\
                &0 < &2 * rho pow 3 * m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [CONV_TAC REAL_FIELD; ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < &2`]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ]);;

(* ========================================================================= *)
(* Prop 16.1, small scales, KL Sublemma 79.23: admissible                    *)
(* scales.  p3n_adm V t0 x0 s is the hypothesis of p3_noncoll_at at scale s *)
(* (the parabolic neighbourhood P(x0,t0,s,-s^2) exists and abs Rm <= s^-2   *)
(* on it).  Admissibility passes to smaller scales (subsets of a persisting *)
(* open set persist, by the regularity of history views P2CY_HISTORY_       *)
(* REGULAR), it is closed from below, so a maximal admissible scale exists  *)
(* in [r0,R].                                                               *)
(* ========================================================================= *)

let p3n_adm = new_definition
 `p3n_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
          (t0:real) (x0:A) (s:real) <=>
    &0 < s /\ rfs_parabolic_exists V t0 x0 s (s pow 2) /\
    (!t y. t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball V t0 x0 s
           ==> mfd_rm_norm (rfs_vatlas V t) (rfs_vmetric V t) y <= inv(s pow 2))`;;

(* an open subset of a persisting open set persists, in a history view *)

let P3N_PERSIST_SUBOPEN = prove
 (`!(hs:(A)rfs_history) W W' a b.
     rfs_history_ok hs /\ rfs_persists (rfs_view hs) W a b /\ a < b /\
     W' SUBSET W /\ open_in (rfs_top_at hs b) W'
     ==> rfs_persists (rfs_view hs) W' a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
  REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(LABEL_TAC "df") THEN
  UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
  DISCH_THEN(fun th -> LABEL_TAC "pW" th THEN MP_TAC th) THEN
  REWRITE_TAC[rfs_persists; rfs_view; rfs_vtop; rfs_vatlas] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "df" (MP_TAC o SPEC `s:real`) THEN
  USE_THEN "pW" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s`; `W:A->bool`; `W':A->bool`]
                OPEN_IN_OPEN_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && can (find_term (fun t -> t = `subtopology`)) (concl th) = false &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "subtopology" with Failure _ -> false))) THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) b`; `W:A->bool`; `W':A->bool`]
                OPEN_IN_OPEN_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[]);;

(* the slices of a history are Hausdorff Riemannian manifolds where nonempty *)

let P3N_HIST_SLICE = prove
 (`!(hs:(A)rfs_history) t x.
     rfs_history_ok hs /\ x IN topspace(rfs_top_at hs t)
     ==> hausdorff_space (rfs_top_at hs t) /\
         smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t) /\
         riemannian_metric (rfs_atlas_at hs t) (rfs_metric_at hs t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let P3N_ADM_MONO = prove
 (`!(hs:(A)rfs_history) t0 x0 s s'.
     rfs_history_ok hs /\ x0 IN topspace(rfs_top_at hs t0) /\
     p3n_adm (rfs_view hs) t0 x0 s /\ &0 < s' /\ s' <= s
     ==> p3n_adm (rfs_view hs) t0 x0 s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_adm; rfs_parabolic_exists] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s' pow 2 <= s pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball (rfs_view (hs:(A)rfs_history)) t0 x0 s' SUBSET
                rfs_vball (rfs_view hs) t0 x0 s` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_view; rfs_vball] THEN MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `t0 - s' pow 2 < t0` THENL
     [ALL_TAC;
      REWRITE_TAC[rfs_persists; rfs_view] THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P3N_PERSIST_SUBOPEN THEN
    EXISTS_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) t0 x0 s` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history))
                     (rfs_vball (rfs_view hs) t0 x0 s) (t0 - s pow 2) t0` THEN
      REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
      DISCH_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`; `x0:A`] P3N_HIST_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[rfs_view; rfs_vball] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(s pow 2)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT]]);;

(* choice of an intermediate scale *)

let P3N_MID_SCALE = prove
 (`!c s. c < s ==> c < (c + s) / &2 /\ (c + s) / &2 < s`,
  REAL_ARITH_TAC);;

(* admissibility is closed from below *)

let P3N_ADM_SUP = prove
 (`!(hs:(A)rfs_history) t0 x0 a s.
     rfs_history_ok hs /\ x0 IN topspace(rfs_top_at hs t0) /\ &0 < a /\ a < s /\
     (!s'. a <= s' /\ s' < s ==> p3n_adm (rfs_view hs) t0 x0 s')
     ==> p3n_adm (rfs_view hs) t0 x0 s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "adm"))))) THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `a < s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* a scale strictly between max(a,c) and s is admissible *)
  SUBGOAL_THEN
   `!c. c < s ==> ?s''. a <= s'' /\ c < s'' /\ s'' < s /\
                        p3n_adm (rfs_view (hs:(A)rfs_history)) t0 (x0:A) s''`
  (LABEL_TAC "mid") THENL
   [X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    EXISTS_TAC `(max a c + s) / &2` THEN
    MP_TAC(SPECL [`max a c`; `s:real`] P3N_MID_SCALE) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `a < s` THEN UNDISCH_TAC `c < s` THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `max a c < (max a c + s) / &2` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `max a c < (max a c + s) / &2` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "adm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `max a c < (max a c + s) / &2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p3n_adm; rfs_parabolic_exists] THEN CONJ_TAC THENL
   [(* the parabolic neighbourhood *)
    REWRITE_TAC[rfs_persists; rfs_view; rfs_vtop; rfs_vatlas] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM rfs_view] THEN
    SUBGOAL_THEN `&0 <= t0 - t /\ sqrt(t0 - t) < s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "mid" (MP_TAC o C MP (ASSUME `sqrt(t0 - t) < s`) o SPEC `sqrt(t0 - t)`) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!s2. s1 <= s2 /\ s2 < s
                       ==> smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t) /\
                           open_in (rfs_top_at (hs:(A)rfs_history) t)
                                   (rfs_vball (rfs_view hs) t0 x0 s2)`
    (LABEL_TAC "op") THENL
     [X_GEN_TAC `s2:real` THEN STRIP_TAC THEN
      USE_THEN "adm" (MP_TAC o SPEC `s2:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[p3n_adm; rfs_parabolic_exists; rfs_persists; rfs_view; rfs_vtop; rfs_vatlas] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[rfs_view]] THEN
      SUBGOAL_THEN `sqrt(t0 - t) pow 2 < s2 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
        ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "op" (MP_TAC o C MP (CONJ (SPEC `s1:real` REAL_LE_REFL) (ASSUME `s1 < s`)) o
                     SPEC `s1:real`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rfs_vball (rfs_view (hs:(A)rfs_history)) t0 x0 s =
      UNIONS {rfs_vball (rfs_view hs) t0 x0 s2 | s2 | s1 <= s2 /\ s2 < s}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:A` THEN EQ_TAC THENL
       [DISCH_TAC THEN
        ABBREV_TAC `d = mfd_dist (rfs_top_at hs t0,rfs_atlas_at (hs:(A)rfs_history) t0)
                                 (rfs_metric_at hs t0) x0 (y:A)` THEN
        SUBGOAL_THEN `mfd_joinable (rfs_top_at hs t0,rfs_atlas_at (hs:(A)rfs_history) t0)
                                   x0 (y:A) /\ d < s` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view hs) t0 x0 s` THEN
          ASM_REWRITE_TAC[rfs_view; rfs_vball; mfd_ball; IN_ELIM_THM];
          ALL_TAC] THEN
        EXISTS_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) t0 x0 ((max s1 d + s) / &2)` THEN
        CONJ_TAC THENL
         [EXISTS_TAC `(max s1 d + s) / &2` THEN REWRITE_TAC[] THEN
          UNDISCH_TAC `s1 < s` THEN UNDISCH_TAC `d < s` THEN REAL_ARITH_TAC;
          ASM_REWRITE_TAC[rfs_view; rfs_vball; mfd_ball; IN_ELIM_THM] THEN
          UNDISCH_TAC `s1 < s` THEN UNDISCH_TAC `d < s` THEN REAL_ARITH_TAC];
        DISCH_THEN(X_CHOOSE_THEN `B:A->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC) MP_TAC)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t0`; `rfs_atlas_at (hs:(A)rfs_history) t0`;
                       `rfs_metric_at (hs:(A)rfs_history) t0`; `x0:A`; `s2:real`; `s:real`]
                      P2BN_MFD_BALL_MONO) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view hs) t0 x0 s2` THEN
        REWRITE_TAC[rfs_view; rfs_vball] THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `s2:real` THEN STRIP_TAC THEN
    USE_THEN "op" (MP_TAC o C MP (CONJ (ASSUME `s1 <= s2`) (ASSUME `s2 < s`)) o
                   SPEC `s2:real`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the curvature bound, by contradiction *)
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `M = mfd_rm_norm (rfs_vatlas (rfs_view (hs:(A)rfs_history)) t)
                              (rfs_vmetric (rfs_view hs) t) (y:A)` THEN
  SUBGOAL_THEN `&0 < M /\ inv(sqrt M) < s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(s pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv s < sqrt M` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_SIMP_TAC[REAL_POW_INV];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t0 - t /\ sqrt(t0 - t) < s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (rfs_top_at hs t0,rfs_atlas_at (hs:(A)rfs_history) t0)
                         (rfs_metric_at hs t0) x0 (y:A) < s` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view hs) t0 x0 s` THEN
    REWRITE_TAC[rfs_view; rfs_vball; mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "mid" (MP_TAC o SPEC
    `max (inv(sqrt M)) (max (sqrt(t0 - t))
       (mfd_dist (rfs_top_at hs t0,rfs_atlas_at (hs:(A)rfs_history) t0)
                 (rfs_metric_at hs t0) x0 (y:A)))`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 s2` THEN
  REWRITE_TAC[p3n_adm] THEN DISCH_THEN(MP_TAC o SPECL [`t:real`; `y:A`] o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `sqrt(t0 - t) pow 2 < s2 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
        ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2] THEN ASM_REAL_ARITH_TAC];
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view hs) t0 x0 s` THEN
      REWRITE_TAC[rfs_view; rfs_vball; mfd_ball; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_NOT_LE] THEN
  SUBGOAL_THEN `inv(sqrt M) pow 2 < s2 pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_INV]);;

(* a maximal admissible scale in [r0,R] *)

let P3N_MAXSCALE = prove
 (`!(hs:(A)rfs_history) t0 x0 r0 R.
     rfs_history_ok hs /\ x0 IN topspace(rfs_top_at hs t0) /\
     p3n_adm (rfs_view hs) t0 x0 r0 /\ r0 <= R
     ==> ?s. r0 <= s /\ s <= R /\ p3n_adm (rfs_view hs) t0 x0 s /\
             (s = R \/ !s'. s < s' /\ s' <= R ==> ~p3n_adm (rfs_view hs) t0 x0 s')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 r0` THEN SIMP_TAC[p3n_adm];
    ALL_TAC] THEN
  ABBREV_TAC `S = {s | r0 <= s /\ s <= R /\ p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 s}` THEN
  SUBGOAL_THEN `!s. s IN S <=> r0 <= s /\ s <= R /\ p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 s`
  MP_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "S1" (GEN `s:real` (fst(EQ_IMP_RULE(SPEC `s:real` th)))) THEN
                       LABEL_TAC "S2" (GEN `s:real` (snd(EQ_IMP_RULE(SPEC `s:real` th))))) THEN
  SUBGOAL_THEN `(r0:real) IN S` ASSUME_TAC THENL
   [USE_THEN "S2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (!s. s IN S ==> s <= R)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "S1" (MP_TAC o C MATCH_MP (ASSUME `(s:real) IN S`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = sup(S:real->bool)` THEN
  SUBGOAL_THEN `r0 <= m /\ m <= R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "m" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `R:real` THEN FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 m` ASSUME_TAC THENL
   [ASM_CASES_TAC `m = r0:real` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P3N_ADM_SUP THEN EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real->bool`; `s':real`] SUP_APPROACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `R:real` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s'':real` STRIP_ASSUME_TAC) THEN
    USE_THEN "S1" (MP_TAC o C MATCH_MP (ASSUME `(s'':real) IN S`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC P3N_ADM_MONO THEN EXISTS_TAC `s'':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `m = R:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s':real` THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(s':real) IN S` ASSUME_TAC THENL
   [USE_THEN "S2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s' <= m` MP_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `R:real` THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: two tools.  Pinching bounds the                  *)
(* curvature norm by the scalar curvature where R is large (abs Rm <= 2 R    *)
(* once R >= 4 e^4; the Hamilton-Ivey form of rfs_pinched_at and the upper  *)
(* bound P3N_SEC_UPPER).  The Bishop-Gromov step down with a curvature bound *)
(* K and K rho^2 <= L loses the factor exp(2 sqrt L) (sinh x <= x e^x).     *)
(* ========================================================================= *)

let P3N_PINCH_RM_HIGH = prove
 (`!top atlas (g:A->real^3^3) t x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     rfs_pinched_at atlas g t x /\ &0 <= t /\ &4 * exp(&4) <= mfd_scalar atlas g x
     ==> mfd_rm_norm atlas g x <= &2 * mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `nu = mfd_sec_min atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < exp(&4)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  (* the negative part of the sectional curvature *)
  SUBGOAL_THEN `--nu <= R / &2` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= nu` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_pinched_at atlas (g:A->real^3^3) t x` THEN
    ASM_REWRITE_TAC[rfs_pinched_at] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `exp(&4) <= --nu` THENL
     [SUBGOAL_THEN `&4 <= log(--nu) /\ &0 <= log(&1 + t)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [SUBGOAL_THEN `&4 = log(exp(&4))` SUBST1_TAC THENL
           [REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
          MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&2 * --nu * &1 <= &2 * --nu * (log(--nu) + log(&1 + t) - &3)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `u:real^3`; `v:real^3`] P3N_SEC_UPPER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `u:real^3`; `v:real^3`] RFA_SEC_GE_SECMIN) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `--nu <= R / &2` THEN UNDISCH_TAC `&4 * exp(&4) <= R` THEN
  UNDISCH_TAC `&0 < exp(&4)` THEN REAL_ARITH_TAC);;

(* sinh x <= x exp x, in the form of the model function *)

let P3N_SN_NEG_UPPER = prove
 (`!K t. &0 <= K /\ &0 <= t ==> cmp_sn (--K) t <= t * exp(sqrt K * t)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; SQRT_0; REAL_MUL_LZERO; REAL_EXP_0; REAL_MUL_RID;
                    CMP_SN_FLAT; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CMP_SN_NEG_CURV] THEN
  ABBREV_TAC `y = sqrt K * t` THEN
  SUBGOAL_THEN `&0 < sqrt K /\ &0 <= y` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp y - exp(--y) <= &2 * y * exp y` ASSUME_TAC THENL
   [MP_TAC(SPEC `--y` REAL_EXP_LE_X) THEN MP_TAC(SPEC `y:real` REAL_EXP_POS_LT) THEN
    SUBGOAL_THEN `&1 <= exp y` ASSUME_TAC THENL
     [MP_TAC(SPEC `y:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(--y) * exp y = &1` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ADD_LINV; REAL_EXP_0]; ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(&1 - y) * exp y <= &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&1 - y) * exp y <= exp(--y) * exp y` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `y <= y * exp y` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < s ==> &0 < &2 * s`] THEN
  SUBGOAL_THEN `(t * exp y) * &2 * sqrt K = &2 * y * exp y` SUBST1_TAC THENL
   [EXPAND_TAC "y" THEN REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]);;

(* the model volume with K r^2 <= L *)

let P3N_VMODEL_NEG_UPPER = prove
 (`!K L r. &0 <= K /\ &0 <= L /\ &0 < r /\ K * r pow 2 <= L
           ==> cmp_vmodel (:3) (--K) r <= exp(&2 * sqrt L) * measure(ball(vec 0:real^3,r))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CMP_VMODEL_FLAT; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[cmp_vmodel; CMP_SN_FLAT; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `sqrt K * r <= sqrt L` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt K * r = sqrt(K * r pow 2)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,r]) (\t. cmp_sn (--K) t pow 2) <=
    exp(&2 * sqrt L) * real_integral (real_interval[&0,r]) (\t. t pow 2)`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`\t:real. t pow 2`; `exp(&2 * sqrt L)`; `real_interval[&0,r]`]
      REAL_INTEGRAL_LMUL)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[ETA_AX; CMPV_SN_CONTINUOUS_ON];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN BETA_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= cmp_sn (--K) t` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FLT_SN_NEG_LOWER THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t * exp(sqrt K * t)) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[P3N_SN_NEG_UPPER];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_MUL; GSYM REAL_EXP_N] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `sqrt K * t <= sqrt K * r` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
        UNDISCH_TAC `sqrt K * r <= sqrt L` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&3 * measure(ball(vec 0:real^3,&1))`;
                 `real_integral (real_interval[&0,r]) (\t. cmp_sn (--K) t pow 2)`;
                 `exp(&2 * sqrt L) * real_integral (real_interval[&0,r]) (\t. t pow 2)`]
                REAL_LE_LMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POS; MEASURE_POS_LE; MEASURABLE_BALL];
    REAL_ARITH_TAC]);;

(* the Bishop-Gromov step down with abs Rm <= K and K rho^2 <= L *)

let P3N_BG_STEPDOWN_L = prove
 (`!top atlas (g:A->real^3^3) x rho K L k r v v'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < r /\ r <= rho /\ &0 <= K /\ &0 <= L /\ K * rho pow 2 <= L /\
     compact_in top (top closure_of mfd_ball (top,atlas) g x rho) /\
     (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= K) /\
     mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x rho) v /\ k * rho pow 3 <= v /\
     mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v'
     ==> k * inv(exp(&2 * sqrt L)) * r pow 3 <= v'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `r <= rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:3)`] CMP_RELVOL) THEN REWRITE_TAC[CMP_RELVOL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `x:A`; `K:real`; `rho:real`; `r:real`; `rho:real`;
                            `v':real`; `v:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x rho` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `w:real^3`] P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `&0 <= w dot ((g:A->real^3^3) y ** w)` ASSUME_TAC THENL
     [ASM_CASES_TAC `w = vec 0:real^3` THENL
       [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `y:A`] RIEMANNIAN_METRIC_POS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_rm_norm atlas (g:A->real^3^3) y * (w dot (g y ** w)) <=
                  K * (w dot (g y ** w))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`K:real`; `r:real`] (INST_TYPE [`:3`,`:N`] FLT_VMODEL_LOWER)) THEN
  MP_TAC(ISPECL [`K:real`; `L:real`; `rho:real`] P3N_VMODEL_NEG_UPPER) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `!s. &0 <= s ==> measure(ball(vec 0:real^3,s)) = s pow 3 * measure(ball(vec 0:real^3,&1))`
  (fun th -> ASM_SIMP_TAC[th; REAL_LT_IMP_LE]) THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `s:real`; `&1`] MEASURE_BALL_SCALING) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; DIMINDEX_3];
    ALL_TAC] THEN
  ABBREV_TAC `m = measure(ball(vec 0:real^3,&1))` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01]; ALL_TAC] THEN
  ABBREV_TAC `Vr = cmp_vmodel (:3) (--K) r` THEN
  ABBREV_TAC `Vrho = cmp_vmodel (:3) (--K) rho` THEN
  ABBREV_TAC `E = exp(&2 * sqrt L)` THEN
  SUBGOAL_THEN `&0 < E` ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < rho pow 3 /\ &0 < r pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v'` ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_POS_LE) THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `mfd_ball (top,atlas) (g:A->real^3^3) x r`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * rho pow 3 * (r pow 3 * m) <= v' * (E * rho pow 3 * m)` MP_TAC THENL
   [ASM_CASES_TAC `&0 <= k` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v * Vr` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v' * Vrho` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * rho pow 3 * (r pow 3 * m) =
                (k * inv E * r pow 3) * (E * rho pow 3 * m) /\
                &0 < E * rho pow 3 * m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&0 < E` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_MUL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: canonical neighbourhoods at small                *)
(* scales, the strong neck.  On B(x,R(x)^-1/2) the neck has R within 1/2 of *)
(* R(x) (P2BN_NECK_SCALAR, P2BN_NECK_BALL_IN), so abs Rm <= 3 R(x) by       *)
(* pinching; balls about the centre of radius rho <= kap R(x)^-1/2 have     *)
(* volume >= kap rho^3 (P2BN_EVNECK_RM, P2BN_NECK_BALL_VOLUME).              *)
(* ========================================================================= *)

let P3N_NECKV_DATA = prove
 (`?eps0 kap. &0 < eps0 /\ &0 < kap /\
     !TM AT (G:real->A->real^3^3) eps x t e.
       p2c_regular_view (TM,AT,G) /\ &0 < eps /\ eps <= eps0 /\
       rfs_strong_neck (TM,AT,G) eps x t e /\
       hausdorff_space (TM t) /\ compact_space (TM t) /\ riemannian_metric (AT t) (G t) /\
       &0 <= t /\ (!y. y IN topspace(TM t) ==> rfs_pinched_at (AT t) (G t) t y) /\
       &8 * exp(&4) <= mfd_scalar (AT t) (G t) x
       ==> (!y. y IN mfd_ball (TM t,AT t) (G t) x (inv(sqrt(mfd_scalar (AT t) (G t) x)))
                ==> mfd_rm_norm (AT t) (G t) y <= &3 * mfd_scalar (AT t) (G t) x /\
                    mfd_scalar (AT t) (G t) x <= &2 * mfd_scalar (AT t) (G t) y) /\
           (!rho. &0 < rho /\ rho <= kap * inv(sqrt(mfd_scalar (AT t) (G t) x))
                  ==> ?v. mfd_has_volume (TM t,AT t) (G t) (mfd_ball (TM t,AT t) (G t) x rho) v /\
                          kap * rho pow 3 <= v)`,
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm"))
    (INST_TYPE [`:A`,`:A`] P2BN_EVNECK_RM) THEN
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bv"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_BALL_VOLUME) THEN
  MP_TAC(SPEC `&1 / &2` (INST_TYPE [`:A`,`:A`] P2BN_NECK_SCALAR)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))) THEN
  EXISTS_TAC `min (min eps1 eps2) (&1 / &10)` THEN
  EXISTS_TAC `min (inv(sqrt K1)) (pi / &750)` THEN
  SUBGOAL_THEN `&0 < inv(sqrt K1) /\ &0 < pi / &750` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MP_TAC PI_POS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&0 < eps1` THEN UNDISCH_TAC `&0 < eps2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&0 < inv(sqrt K1)` THEN UNDISCH_TAC `&0 < pi / &750` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `eps:real`; `x:A`; `t:real`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= eps2 /\ eps <= &1 / &10 /\ eps <= &1 / &4`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= min (min eps1 eps2) (&1 / &10)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_evolving_neck (TM:real->A topology,AT,G) eps (x:A) t (&1) e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                         ((G:real->A->real^3^3) t) eps (x:A) e` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_evolving_neck (TM:real->A topology,AT,G) eps (x:A) t (&1) e` THEN
    REWRITE_TAC[rfs_evolving_neck] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck" with Failure _ -> false)) THEN
  ABBREV_TAC `R0 = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                              ((G:real->A->real^3^3) t) (x:A)` THEN
  SUBGOAL_THEN `&0 < inv(sqrt R0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the curvature bound on B(x,R0^-1/2) *)
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(TM:real->A topology) t`; `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                   `(G:real->A->real^3^3) t`; `eps:real`; `x:A`; `e:real^3->A`;
                   `inv(sqrt R0)`] P2BN_NECK_BALL_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv(sqrt R0) * sqrt R0 = &1` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `eps:real` P2BN_NECK_CORE_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN topspace((TM:real->A topology) t)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                              ((G:real->A->real^3^3) t) x (inv(sqrt R0))` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    USE_THEN "sc" (MP_TAC o SPECL [`(TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
                                     G:real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`;
                                   `&1`; `e:real^3->A`; `&0`; `y0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_vscalar; REAL_ARITH `&0 / x = &0`; REAL_ADD_RID; REAL_SUB_RZERO;
                REAL_DIV_1] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(y:A) = e (y0:real^3)`)) THEN
    DISCH_TAC THEN
    ABBREV_TAC `Ry = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                ((G:real->A->real^3^3) t) (y:A)` THEN
    SUBGOAL_THEN `R0 / &2 <= Ry /\ Ry <= &3 / &2 * R0` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&1 / &2 * R0 <= (Ry / R0) * R0 /\ (Ry / R0) * R0 <= &3 / &2 * R0`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        UNDISCH_TAC `abs(Ry / R0 - &1) <= &1 / &2` THEN UNDISCH_TAC `&0 < R0` THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `(Ry / R0) * R0 = Ry` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < R0` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `R0 / &2 <= Ry` THEN REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`(TM:real->A topology) t`; `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                   `(G:real->A->real^3^3) t`; `t:real`; `y:A`] P3N_PINCH_RM_HIGH) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN UNDISCH_TAC `&8 * exp(&4) <= R0` THEN
      UNDISCH_TAC `R0 / &2 <= Ry` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `Ry <= &3 / &2 * R0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* small balls about the centre *)
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_rm_norm ((AT:real->((A->bool)#(A->real^3))->bool) t) ((G:real->A->real^3^3) t) (x:A)
    <= K1 * R0`
  ASSUME_TAC THENL
   [USE_THEN "rm" (MP_TAC o SPECL [`(TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
                                     G:real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`;
                                   `&1`; `e:real^3->A`; `&0`]) THEN
    REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar; real_div; REAL_MUL_LZERO;
                REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `eps <= &1 / &4` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K1 * R0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  USE_THEN "bv" (MP_TAC o SPECL [`(TM:real->A topology) t`;
                                 `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                                 `(G:real->A->real^3^3) t`; `eps:real`; `x:A`; `e:real^3->A`;
                                 `rho:real`; `K1 * R0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rho <= inv(sqrt(K1 * R0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `min (inv(sqrt K1)) (pi / &750) * inv(sqrt R0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `min rho (inv(sqrt(K1 * R0))) = rho` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [UNDISCH_TAC `rho <= inv(sqrt(K1 * R0))` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pi / &750 * rho pow 3` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.1, small scales: the cap core at small scales.                    *)
(* With the curvature radius rx of the cap clause (P3N_CAP_RADIUS), the     *)
(* ratio bound of the cap gives rx >= (C R(x))^-1/2, R <= C R(x) and        *)
(* abs Rm <= 2 C R(x) on B(x,rx) (pinching), and the clause's volume bound  *)
(* at rx steps down by P3N_BG_STEPDOWN_L.                                    *)
(* ========================================================================= *)

let P3N_CAPV_DATA = prove
 (`!top atlas (g:A->real^3^3) C eps x U Y t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ &1 < C /\ &0 < mfd_scalar atlas g x /\
     rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
     &0 <= t /\ (!y. y IN topspace top ==> rfs_pinched_at atlas g t y) /\
     &4 * exp(&4) * C <= mfd_scalar atlas g x
     ==> (!y. y IN mfd_ball (top,atlas) g x (inv(sqrt(C * mfd_scalar atlas g x)))
              ==> mfd_rm_norm atlas g y <= &2 * C * mfd_scalar atlas g x /\
                  mfd_scalar atlas g x <= C * mfd_scalar atlas g y) /\
         (!rho. &0 < rho /\ rho <= inv(sqrt(C * mfd_scalar atlas g x))
                ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x rho) v /\
                        inv C * inv(exp(&2 * sqrt(&2 * C))) * rho pow 3 <= v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] P3N_CAP_Y_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN U /\ x IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun (l,i) -> LABEL_TAC l (el i cs)) [("upos",3); ("ratio",5); ("ballc",7)]) THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  (* the ratio bound on U *)
  USE_THEN "ratio" (MP_TAC o REWRITE_RULE[rfs_sup_lt]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z:A. z IN U ==> mfd_scalar atlas (g:A->real^3^3) z <= C * R0 /\
                                 R0 <= C * mfd_scalar atlas g z`
  (LABEL_TAC "rat") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) z` ASSUME_TAC THENL
     [USE_THEN "upos" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z / R0 <= d1 /\
                  R0 / mfd_scalar atlas g z <= d1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`z:A`; `x:A`] THEN ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`x:A`; `z:A`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) z / R0 <= d1` THEN
    UNDISCH_TAC `R0 / mfd_scalar atlas (g:A->real^3^3) z <= d1` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `d1 * R0 <= C * R0 /\ d1 * mfd_scalar atlas (g:A->real^3^3) z <=
                  C * mfd_scalar atlas g z` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the curvature norm on U *)
  SUBGOAL_THEN `!z:A. z IN U ==> mfd_rm_norm atlas (g:A->real^3^3) z <= &2 * C * R0`
  (LABEL_TAC "rmU") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "rat" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN U`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `t:real`; `z:A`] P3N_PINCH_RM_HIGH) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [ASM SET_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        SUBGOAL_THEN `&4 * exp(&4) * C <= C * mfd_scalar atlas (g:A->real^3^3) z` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `&4 * e * C <= C * s <=> C * (&4 * e) <= C * s`] THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ARITH `&1 < C ==> &0 < C`]];
      UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) z <= C * R0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the curvature radius of the clause at x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] P3N_CAP_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rs:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`] P3N_COMPACT_SCALAR_BOUND) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN DISCH_THEN(X_CHOOSE_TAC `Bd:real`) THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) x rs SUBSET topspace top` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  USE_THEN "ballc" (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL [`x:A`; `rs:real`]))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `Bd:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Bd:real`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `vs:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) x rs SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of mfd_ball (top,atlas) (g:A->real^3^3) x rs` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET];
    ALL_TAC] THEN
  (* rs >= (C R0)^-1/2 *)
  SUBGOAL_THEN `inv(rs pow 2) <= C * R0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term (fun t -> t = `inv(rs pow 2)`)) (concl th) && is_eq(concl th))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `rs:real`] P3N_SUPBALL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "rat" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C * R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(C * R0)) <= rs` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(sqrt(inv(rs pow 2)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_INV THEN
        ASM_SIMP_TAC[REAL_POW_LT];
        MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_ASSUM ACCEPT_TAC];
      ASM_SIMP_TAC[SQRT_INV; POW_2_SQRT; REAL_LT_IMP_LE; REAL_INV_INV; REAL_LE_REFL]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `mfd_ball (top,atlas) (g:A->real^3^3) x rs SUBSET U`)) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `x:A`; `inv(sqrt(C * R0))`; `rs:real`] P2BN_MFD_BALL_MONO) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "rmU" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "rat" (MP_TAC o SPEC `y:A`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `rho:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3N_BG_STEPDOWN_L THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `x:A`; `rs:real`; `&2 * C * R0`; `vs:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    (* K rs^2 <= 2 C *)
    SUBGOAL_THEN `rs pow 2 <= inv R0` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv R0 = inv(sqrt R0) pow 2` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * C * R0) * inv R0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
      UNDISCH_TAC `&0 < R0` THEN CONV_TAC REAL_FIELD];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "rmU" MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d * rs pow 3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      UNDISCH_TAC `d <= vs / rs pow 3` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT]]]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: C-components and eps-round                       *)
(* components at small scales.  On a C-component the sectional curvature is *)
(* at least d > C^-1 sup R, so 0 < K <= R/2 and abs Rm <= C R(x) on U; on   *)
(* an eps-round component it lies in [2q/5,8q/5] (P2BS_ROUND_SECT_Q), so    *)
(* abs Rm <= R(x) on U.  The 16.3 volume bounds at R(x)^-1/2 then step down *)
(* by P3N_BG_STEPDOWN_L.                                                     *)
(* ========================================================================= *)

let P3N_CCOMPV_DATA = prove
 (`!top atlas (g:A->real^3^3) C x U v0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ &1 < C /\ x IN U /\ rfs_c_component (top,atlas) g C U /\
     mfd_has_volume (top,atlas) g U v0 /\ &0 < mfd_scalar atlas g x /\
     inv C * inv(sqrt(mfd_scalar atlas g x)) pow 3 < v0
     ==> (!y. y IN mfd_ball (top,atlas) g x (inv(sqrt(mfd_scalar atlas g x)))
              ==> mfd_rm_norm atlas g y <= C * mfd_scalar atlas g x /\
                  mfd_scalar atlas g x <= C * mfd_scalar atlas g y) /\
         (!rho. &0 < rho /\ rho <= inv(sqrt(mfd_scalar atlas g x))
                ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x rho) v /\
                        inv(C pow 7) * inv(exp(&2 * sqrt C)) * rho pow 3 <= v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `x:A`; `U:A->bool`; `v0:real`] P3N_163_CCOMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `vR:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
  REWRITE_TAC[rfs_c_component] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun (l,i) -> LABEL_TAC l (el i cs))
      [("ucomp",1); ("ucpt",2); ("uinf",5)]) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [USE_THEN "ucpt" (MP_TAC o MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* balls about x stay in U *)
  SUBGOAL_THEN `!r. mfd_ball (top,atlas) (g:A->real^3^3) x r SUBSET U` (LABEL_TAC "bU") THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `x:A`; `y:A`] P3N_COMP_JOINABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  (* sup R on U *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:A->bool`] P3N_COMPACT_SCALAR_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  ABBREV_TAC `S = sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
  SUBGOAL_THEN `!y:A. y IN U ==> mfd_scalar atlas (g:A->real^3^3) y <= S` (LABEL_TAC "rsup") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "S" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN
    CONJ_TAC THENL [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `R0 <= S` ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN USE_THEN "rsup" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* the sectional lower bound d > S / C *)
  USE_THEN "uinf" (MP_TAC o REWRITE_RULE[rfs_inf_gt; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dsec"))) THEN
  SUBGOAL_THEN `!y:A u v. y IN U /\ ~collinear {vec 0,u,v}
                          ==> d <= mfd_sectional atlas (g:A->real^3^3) y u v`
  (LABEL_TAC "sec") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "dsec" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:A`; `u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d /\ S < C * d` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv C * S` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_ARITH `&1 < C ==> &0 < C`];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `S = C * (inv C * S)` SUBST1_TAC THENL
     [UNDISCH_TAC `&1 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 * d <= R0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `d:real`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the curvature norm on U *)
  SUBGOAL_THEN `!y:A. y IN U ==> mfd_rm_norm atlas (g:A->real^3^3) y <= C * R0`
  (LABEL_TAC "rmU") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `d <= mfd_sec_min atlas (g:A->real^3^3) y` ASSUME_TAC THENL
     [REWRITE_TAC[mfd_sec_min] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        EXISTS_TAC `mfd_sectional atlas (g:A->real^3^3) y (basis 1) (basis 2)` THEN
        MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN
        REWRITE_TAC[FLT_NONCOLLINEAR];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `u:real^3`; `v:real^3`] P3N_SEC_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "sec" (MP_TAC o C MP (CONJ (ASSUME `(y:A) IN U`)
                                        (ASSUME `~collinear {vec 0:real^3,u,v}`)) o
                    SPECL [`y:A`; `u:real^3`; `v:real^3`]) THEN
    DISCH_TAC THEN
    USE_THEN "rsup" (MP_TAC o C MATCH_MP (ASSUME `(y:A) IN U`)) THEN DISCH_TAC THEN
    SUBGOAL_THEN `C * d <= C * R0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&6 * d <= R0` THEN UNDISCH_TAC `&0 < d` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`&6 * d <= R0`; `S < C * d`; `&0 < d`; `&1 < C`;
                           `d <= mfd_sec_min atlas (g:A->real^3^3) y`;
                           `C * d <= C * R0`;
                           `mfd_scalar atlas (g:A->real^3^3) y <= S`;
                           `d <= mfd_sectional atlas (g:A->real^3^3) y u v`;
                           `mfd_sectional atlas (g:A->real^3^3) y u v <=
                            mfd_scalar atlas g y / &2 - &2 * mfd_sec_min atlas g y`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL
     [USE_THEN "bU" (MP_TAC o SPEC `inv(sqrt R0)`) THEN ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [USE_THEN "rmU" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&6 * d <= mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `y:A`; `d:real`] P2BS_MFD_SCALAR_SECT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `C * (&6 * d) <= C * mfd_scalar atlas (g:A->real^3^3) y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < C * d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`R0 <= S`; `S < C * d`; `&0 < d`; `&1 < C`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `rho:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3N_BG_STEPDOWN_L THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `x:A`; `inv(sqrt R0)`; `C * R0`; `vR:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN UNDISCH_TAC `&0 < R0` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "rmU" MATCH_MP_TAC THEN
    USE_THEN "bU" (MP_TAC o SPEC `inv(sqrt R0)`) THEN ASM SET_TAC[]]);;

let P3N_ROUNDV_DATA = prove
 (`!top atlas (g:A->real^3^3) eps x U.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ rfs_components_sc top /\
     &0 < eps /\ eps <= &1 / &40 /\ x IN U /\ rfs_round_component (top,atlas) g eps U
     ==> &0 < mfd_scalar atlas g x /\
         (!y. y IN mfd_ball (top,atlas) g x (inv(sqrt(mfd_scalar atlas g x)))
              ==> mfd_rm_norm atlas g y <= mfd_scalar atlas g x /\
                  mfd_scalar atlas g x <= &4 * mfd_scalar atlas g y) /\
         (!rho. &0 < rho /\ rho <= inv(sqrt(mfd_scalar atlas g x))
                ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x rho) v /\
                        cmp_vmodel (:3) (&1) (&1 / &4) / &2 * inv(exp(&2)) * rho pow 3 <= v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `U:A->bool`] P3N_163_ROUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `vR:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_round_component] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_round_component"
    with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3`
      STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* sectional bounds on U *)
  SUBGOAL_THEN `!y:A u v. y IN U /\ ~collinear {vec 0,u,v}
                          ==> &2 / &5 * q <= mfd_sectional atlas (g:A->real^3^3) y u v /\
                              mfd_sectional atlas g y u v <= &8 / &5 * q`
  (LABEL_TAC "sec") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P3N_SEC_Q_BOUNDS THEN
    EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `U:A->bool`; `y:A`; `q:real`; `g1:A->real^3^3`]
                  P2BS_ROUND_SECT_Q) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&12 / &5 * q <= mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `&2 / &5 * q`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "sec" (MP_TAC o C MP (CONJ (ASSUME `(x:A) IN U`)
                                          (ASSUME `~collinear {vec 0:real^3,u,v}`)) o
                      SPECL [`x:A`; `u:real^3`; `v:real^3`]) THEN
      SIMP_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL
   [UNDISCH_TAC `&12 / &5 * q <= R0` THEN UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* balls about x stay in U, where abs Rm <= R0 *)
  SUBGOAL_THEN `!r. mfd_ball (top,atlas) (g:A->real^3^3) x r SUBSET U` (LABEL_TAC "bU") THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `x:A`; `y:A`] P3N_COMP_JOINABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN U ==> mfd_rm_norm atlas (g:A->real^3^3) y <= R0`
  (LABEL_TAC "rmU") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "sec" (MP_TAC o C MP (CONJ (ASSUME `(y:A) IN U`)
                                        (ASSUME `~collinear {vec 0:real^3,u,v}`)) o
                    SPECL [`y:A`; `u:real^3`; `v:real^3`]) THEN
    UNDISCH_TAC `&12 / &5 * q <= R0` THEN UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `R0 <= &48 / &5 * q` ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `&8 / &5 * q`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "sec" (MP_TAC o C MP (CONJ (ASSUME `(x:A) IN U`)
                                          (ASSUME `~collinear {vec 0:real^3,u,v}`)) o
                      SPECL [`x:A`; `u:real^3`; `v:real^3`]) THEN
      SIMP_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL
     [USE_THEN "bU" (MP_TAC o SPEC `inv(sqrt R0)`) THEN ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [USE_THEN "rmU" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `&2 / &5 * q`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "sec" (MP_TAC o C MP (CONJ (ASSUME `(y:A) IN U`)
                                          (ASSUME `~collinear {vec 0:real^3,u,v}`)) o
                      SPECL [`y:A`; `u:real^3`; `v:real^3`]) THEN
      SIMP_TAC[];
      UNDISCH_TAC `R0 <= &48 / &5 * q` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `rho:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `inv(sqrt R0)`; `R0:real`; `&1`;
                 `cmp_vmodel (:3) (&1) (&1 / &4) / &2`; `rho:real`; `vR:real`; `v:real`]
                P3N_BG_STEPDOWN_L) THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN UNDISCH_TAC `&0 < R0` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "rmU" MATCH_MP_TAC THEN
    USE_THEN "bU" (MP_TAC o SPEC `inv(sqrt R0)`) THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: all canonical neighbourhoods with                *)
(* KL's volume clause (p3_canonv_at) at small scales: for R(x) >= 8 e^4 C   *)
(* there are c1, K2, kap depending only on C with abs Rm <= K2 R(x) on       *)
(* B(x, c1 R(x)^-1/2) and Vol B(x,rho) >= kap rho^3 for rho <= c1 R(x)^-1/2. *)
(* ========================================================================= *)

let P3N_SMALL_WEAKEN = prove
 (`!top atlas (g:A->real^3^3) x r1 r2 K1 K2 k1 kap c m Q1 Q2.
     (!y. y IN mfd_ball (top,atlas) g x r1
          ==> mfd_rm_norm atlas g y <= K1 /\ m <= Q1 * mfd_scalar atlas g y) /\
     (!rho. &0 < rho /\ rho <= r2
            ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x rho) v /\
                    k1 * rho pow 3 <= v) /\
     c <= r1 /\ c <= r2 /\ K1 <= K2 /\ kap <= k1 /\ &0 <= m /\ &0 < Q1 /\ Q1 <= Q2
     ==> (!y. y IN mfd_ball (top,atlas) g x c
              ==> mfd_rm_norm atlas g y <= K2 /\ m <= Q2 * mfd_scalar atlas g y) /\
         (!rho. &0 < rho /\ rho <= c
                ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x rho) v /\
                        kap * rho pow 3 <= v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rm") (CONJUNCTS_THEN2 (LABEL_TAC "vol")
    STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "rm" (MP_TAC o SPEC `y:A`) THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `x:A`; `c:real`; `r1:real`] P2BN_MFD_BALL_MONO) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `Ry = mfd_scalar atlas (g:A->real^3^3) y` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Ry` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(Ry < &0) ==> &0 <= Ry`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `Q1 * Ry < Q1 * &0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `Q1 * Ry <= Q2 * Ry` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    USE_THEN "vol" (MP_TAC o SPEC `rho:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k1 * rho pow 3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

let P3N_CANONV_SMALL = prove
 (`?eps0. &0 < eps0 /\ eps0 <= &1 / &40 /\
     !C. &1 < C
       ==> ?c1 K2 kap. &0 < c1 /\ c1 <= &1 /\ &0 < K2 /\ &0 < kap /\
             !TM AT (G:real->A->real^3^3) eps x t.
               p2c_regular_view (TM,AT,G) /\ &0 < eps /\ eps <= eps0 /\
               hausdorff_space (TM t) /\ smooth_manifold_atlas (TM t) (AT t) /\
               riemannian_metric (AT t) (G t) /\ compact_space (TM t) /\
               rfs_components_sc (TM t) /\ &0 <= t /\
               (!y. y IN topspace(TM t) ==> rfs_pinched_at (AT t) (G t) t y) /\
               p3_canonv_at (TM,AT,G) C eps x t /\
               &8 * exp(&4) * C <= mfd_scalar (AT t) (G t) x
               ==> (!y. y IN mfd_ball (TM t,AT t) (G t) x
                               (c1 * inv(sqrt(mfd_scalar (AT t) (G t) x)))
                        ==> mfd_rm_norm (AT t) (G t) y <= K2 * mfd_scalar (AT t) (G t) x /\
                            mfd_scalar (AT t) (G t) x <= &4 * C * mfd_scalar (AT t) (G t) y) /\
                   (!rho. &0 < rho /\ rho <= c1 * inv(sqrt(mfd_scalar (AT t) (G t) x))
                          ==> ?v. mfd_has_volume (TM t,AT t) (G t)
                                    (mfd_ball (TM t,AT t) (G t) x rho) v /\
                                  kap * rho pow 3 <= v)`,
  X_CHOOSE_THEN `epsn:real` (X_CHOOSE_THEN `kapn:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "neck"))))
    (INST_TYPE [`:A`,`:A`] P3N_NECKV_DATA) THEN
  EXISTS_TAC `min epsn (&1 / &40)` THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < epsn` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `C:real` THEN DISCH_TAC THEN
  ABBREV_TAC `V1 = cmp_vmodel (:3) (&1) (&1 / &4)` THEN
  SUBGOAL_THEN `&0 < V1` ASSUME_TAC THENL
   [EXPAND_TAC "V1" THEN MATCH_MP_TAC P3N_VMODEL1_POS THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `kc = inv C * inv(exp(&2 * sqrt(&2 * C)))` THEN
  ABBREV_TAC `kq = inv(C pow 7) * inv(exp(&2 * sqrt C))` THEN
  ABBREV_TAC `kr = V1 / &2 * inv(exp(&2))` THEN
  SUBGOAL_THEN `&0 < kc /\ &0 < kq /\ &0 < kr /\ &0 < inv(sqrt C)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kc"; "kq"; "kr"] THEN REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LT_INV) THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_POW_LT; SQRT_POS_LT; REAL_ARITH `&1 < C ==> &0 < C`;
                 REAL_ARITH `&0 < V1 ==> &0 < V1 / &2`];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`min (min (&1) kapn) (inv(sqrt C))`; `&2 * C + &3`;
    `min (min kapn kc) (min kq kr)`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < kapn` THEN UNDISCH_TAC `&0 < inv(sqrt C)` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`&0 < kapn`; `&0 < kc`; `&0 < kq`; `&0 < kr`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `eps:real`; `x:A`; `t:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `R0 = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                              ((G:real->A->real^3^3) t) (x:A)` THEN
  SUBGOAL_THEN `&0 < exp(&4)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R0 /\ &8 * exp(&4) <= R0 /\ &4 * exp(&4) * C <= R0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(&4) * &1 <= exp(&4) * C /\ &0 < exp(&4) * C` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN UNDISCH_TAC `&0 < exp(&4)` THEN
        UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN UNDISCH_TAC `&0 < exp(&4)` THEN
        UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `&8 * exp(&4) * C <= R0` THEN UNDISCH_TAC `exp(&4) * &1 <= exp(&4) * C` THEN
    UNDISCH_TAC `&0 < exp(&4) * C` THEN UNDISCH_TAC `&0 < exp(&4)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt R0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c1 = min (min (&1) kapn) (inv(sqrt C))` THEN
  SUBGOAL_THEN `c1 * inv(sqrt R0) <= inv(sqrt R0) /\ c1 * inv(sqrt R0) <= kapn * inv(sqrt R0) /\
                c1 * inv(sqrt R0) <= inv(sqrt(C * R0))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_INV_MUL; REAL_ARITH `&1 < C ==> &0 <= C`] THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL;
      MATCH_MP_TAC REAL_LE_RMUL;
      MATCH_MP_TAC REAL_LE_RMUL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "c1" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `min (min kapn kc) (min kq kr) <= kapn /\ min (min kapn kc) (min kq kr) <= kc /\
                min (min kapn kc) (min kq kr) <= kq /\ min (min kapn kc) (min kq kr) <= kr`
  STRIP_ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < R0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p3_canonv_at (TM:real->A topology,AT,G) C eps (x:A) t` THEN
  REWRITE_TAC[p3_canonv_at; p3_strong_canonv; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` MP_TAC) THEN
  STRIP_TAC THENL
   [(* a strong neck *)
    USE_THEN "neck" (MP_TAC o SPECL [`TM:real->A topology`;
                                     `AT:real->((A->bool)#(A->real^3))->bool`;
                                     `G:real->A->real^3^3`; `eps:real`; `x:A`; `t:real`;
                                     `e:real^3->A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `eps <= min epsn (&1 / &40)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
      `mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) ((G:real->A->real^3^3) t) (x:A)
       = R0`; REAL_MUL_ASSOC;
      ASSUME `inv C * inv(exp(&2 * sqrt(&2 * C))) = kc`;
      ASSUME `inv(C pow 7) * inv(exp(&2 * sqrt C)) = kq`;
      ASSUME `cmp_vmodel (:3) (&1) (&1 / &4) = V1`;
      ASSUME `V1 / &2 * inv(exp(&2)) = kr`]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3N_SMALL_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [`inv(sqrt R0)`; `kapn * inv(sqrt R0)`; `&3 * R0`; `kapn:real`; `&2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < R0` THEN UNDISCH_TAC `&0 <= C * R0` THEN
    REAL_ARITH_TAC;
    (* a cap *)
    MP_TAC(ISPECL [`(TM:real->A topology) t`; `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                   `(G:real->A->real^3^3) t`; `C:real`; `eps:real`; `x:A`; `U:A->bool`;
                   `Y:A->bool`; `t:real`] P3N_CAPV_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
      `mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) ((G:real->A->real^3^3) t) (x:A)
       = R0`; REAL_MUL_ASSOC;
      ASSUME `inv C * inv(exp(&2 * sqrt(&2 * C))) = kc`;
      ASSUME `inv(C pow 7) * inv(exp(&2 * sqrt C)) = kq`;
      ASSUME `cmp_vmodel (:3) (&1) (&1 / &4) = V1`;
      ASSUME `V1 / &2 * inv(exp(&2)) = kr`]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3N_SMALL_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [`inv(sqrt(C * R0))`; `inv(sqrt(C * R0))`; `(&2 * C) * R0`; `kc:real`; `C:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < R0` THEN UNDISCH_TAC `&0 <= C * R0` THEN
    REAL_ARITH_TAC;
    (* a C-component *)
    UNDISCH_TAC `p3_comp_vol (TM:real->A topology,AT,G) C (x:A) t U` THEN
    REWRITE_TAC[p3_comp_vol; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`(TM:real->A topology) t`; `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                   `(G:real->A->real^3^3) t`; `C:real`; `x:A`; `U:A->bool`; `v0:real`]
                  P3N_CCOMPV_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
      `mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) ((G:real->A->real^3^3) t) (x:A)
       = R0`; REAL_MUL_ASSOC;
      ASSUME `inv C * inv(exp(&2 * sqrt(&2 * C))) = kc`;
      ASSUME `inv(C pow 7) * inv(exp(&2 * sqrt C)) = kq`;
      ASSUME `cmp_vmodel (:3) (&1) (&1 / &4) = V1`;
      ASSUME `V1 / &2 * inv(exp(&2)) = kr`]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3N_SMALL_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [`inv(sqrt R0)`; `inv(sqrt R0)`; `C * R0`; `kq:real`; `C:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < R0` THEN UNDISCH_TAC `&0 <= C * R0` THEN
    REAL_ARITH_TAC;
    (* an eps-round component *)
    MP_TAC(ISPECL [`(TM:real->A topology) t`; `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                   `(G:real->A->real^3^3) t`; `eps:real`; `x:A`; `U:A->bool`]
                  P3N_ROUNDV_DATA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `eps <= min epsn (&1 / &40)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
      `mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) ((G:real->A->real^3^3) t) (x:A)
       = R0`; REAL_MUL_ASSOC;
      ASSUME `inv C * inv(exp(&2 * sqrt(&2 * C))) = kc`;
      ASSUME `inv(C pow 7) * inv(exp(&2 * sqrt C)) = kq`;
      ASSUME `cmp_vmodel (:3) (&1) (&1 / &4) = V1`;
      ASSUME `V1 / &2 * inv(exp(&2)) = kr`]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3N_SMALL_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [`inv(sqrt R0)`; `inv(sqrt R0)`; `R0:real`; `kr:real`; `&4`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < R0` THEN UNDISCH_TAC `&0 <= C * R0` THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: a pointwise curvature tool, the                  *)
(* converse of abs R <= 6 abs Rm (P3N_SCALAR_LE_RM of pc_p3_s16end) under   *)
(* pinching: once abs Rm >= 4 e^4, abs Rm <= 4 R (a large curvature norm    *)
(* forces a large scalar curvature).                                         *)
(* ========================================================================= *)

let P3N_PINCH_LOWER = prove
 (`!top atlas (g:A->real^3^3) t x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     rfs_pinched_at atlas g t x /\ &0 <= t /\ &4 * exp(&4) <= mfd_rm_norm atlas g x
     ==> mfd_rm_norm atlas g x <= &4 * mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `nu = mfd_sec_min atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < exp(&4)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  (* the two clauses of the pinching *)
  SUBGOAL_THEN `--(&6) <= R` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pinched_at atlas (g:A->real^3^3) t x` THEN
    ASM_REWRITE_TAC[rfs_pinched_at] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `--(&6) <= --(&6) / (&4 * t + &1)` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    SUBGOAL_THEN `&0 < &4 * t + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0:real^3,u,v}
                      ==> nu <= mfd_sectional atlas (g:A->real^3^3) x u v /\
                          mfd_sectional atlas g x u v <= R / &2 - &2 * nu`
  (LABEL_TAC "sec") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `u:real^3`; `v:real^3`] P3N_SEC_UPPER) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `u:real^3`; `v:real^3`] RFA_SEC_GE_SECMIN) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `exp(&4) <= --nu` THENL
   [(* strongly negative curvature: R >= 2 abs nu *)
    SUBGOAL_THEN `&4 <= log(--nu) /\ &0 <= log(&1 + t)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `&4 = log(exp(&4))` SUBST1_TAC THENL [REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * --nu <= R` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_pinched_at atlas (g:A->real^3^3) t x` THEN
      ASM_REWRITE_TAC[rfs_pinched_at] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * --nu * &1 <= &2 * --nu * (log(--nu) + log(&1 + t) - &3)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * R` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "sec" (MP_TAC o C MP (ASSUME `~collinear {vec 0:real^3,u,v}`) o
                      SPECL [`u:real^3`; `v:real^3`]) THEN
      UNDISCH_TAC `&2 * --nu <= R` THEN UNDISCH_TAC `exp(&4) <= --nu` THEN
      UNDISCH_TAC `&0 < exp(&4)` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&2 * --nu <= R` THEN UNDISCH_TAC `exp(&4) <= --nu` THEN
      UNDISCH_TAC `&0 < exp(&4)` THEN REAL_ARITH_TAC];
    (* mildly negative curvature: abs sec <= R / 2 + 2 e^4 *)
    SUBGOAL_THEN `mfd_rm_norm atlas (g:A->real^3^3) x <= R / &2 + &2 * exp(&4)` ASSUME_TAC THENL
     [MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "sec" (MP_TAC o C MP (ASSUME `~collinear {vec 0:real^3,u,v}`) o
                      SPECL [`u:real^3`; `v:real^3`]) THEN
      UNDISCH_TAC `~(exp(&4) <= --nu)` THEN UNDISCH_TAC `--(&6) <= R` THEN
      UNDISCH_TAC `&0 < exp(&4)` THEN
      SUBGOAL_THEN `&5 <= exp(&4)` MP_TAC THENL
       [MP_TAC(SPEC `&4` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_rm_norm atlas (g:A->real^3^3) x <= R / &2 + &2 * exp(&4)` THEN
    UNDISCH_TAC `&4 * exp(&4) <= mfd_rm_norm atlas (g:A->real^3^3) x` THEN
    UNDISCH_TAC `&0 < exp(&4)` THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: joint continuity of the scalar                   *)
(* curvature on a persisting region W over [a,b), W open in the slice at a, *)
(* in the topology of the slice at b (the region flow p2c_vfam is a Ricci   *)
(* flow from a, RFA_MFD_SCALAR_CONTINUOUS_GEN, and its scalar curvature is   *)
(* that of the slices, P2C_VFAM_CURV and P2C_VFAM_CURV_START).               *)
(* ========================================================================= *)

let P3N_REGION_SCALAR_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b.
     p2c_regular_view V /\ a < b /\ open_in (rfs_vtop V a) W /\ rfs_persists V W a b
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology (rfs_vtop V b) W),
            euclideanreal)
           (\z. rfs_vscalar V (FST z) (SND z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
         P2C_REGULAR_VFLOW_FROM) THEN
  ASM_REWRITE_TAC[p2c_vflow_from] THEN STRIP_TAC THEN
  ABBREV_TAC `NT = subtopology (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)` THEN
  ABBREV_TAC `NA = restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)` THEN
  SUBGOAL_THEN `smooth_manifold_atlas (NT:A topology) (NA:((A->bool)#(A->real^3))->bool) /\
                (!t. a <= t /\ t < b
                     ==> riemannian_metric NA (p2c_vfam (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`NT:A topology`; `NA:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W b`; `a:real`]
                    RFA_RICCI_FLOW_FROM_METRIC) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`NT:A topology`; `NA:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W b`; `t:real`]
                    RFA_RICCI_FLOW_FROM_METRIC) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`NT:A topology`; `NA:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W b`] RFA_MFD_SCALAR_CONTINUOUS_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ricci_flow_from (NT,NA) a b (p2c_vfam (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b)` THEN
    REWRITE_TAC[ricci_flow_from] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_MAP_EQ) THEN
  REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL; INTER_UNIV; IN_ELIM_THM; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
  (* the preferred chart of the restricted atlas *)
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) /\ y IN W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN topspace NT` THEN EXPAND_TAC "NT" THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`NT:A topology`; `NA:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (NA:((A->bool)#(A->real^3))->bool) (y:A)`,`c:(A->bool)#(A->real^3)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`UW:A->bool`; `phi:A->real^3`] THEN
  EXPAND_TAC "NA" THEN REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  UNDISCH_TAC `(y:A) IN UW` THEN ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                   `phi:A->real^3`; `y:A`] P2C_VFAM_CURV_START) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3))` THEN
      REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o el 4 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`]) THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "NA" THEN SIMP_TAC[]];
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `t:real`;
                   `U:A->bool`; `phi:A->real^3`; `y:A`] P2C_VFAM_CURV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "NA" THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: curve points and closed balls.                   *)
(* A point of a curve at a given length from its start (P2BC_LENGTH_IVT);  *)
(* every point at distance <= s from x is a limit of points of the open    *)
(* ball B(x,s) (via near-minimizing curves, RFA_DIST_APPROX).               *)
(* ========================================================================= *)

let P3N_CURVE_SPLIT_POINT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) lam.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     &0 <= lam /\ lam <= mfd_length atlas g gamma (&0) (&1)
     ==> ?tau. &0 <= tau /\ tau <= &1 /\
               mfd_joinable (top,atlas) (gamma(&0)) (gamma tau) /\
               mfd_joinable (top,atlas) (gamma tau) (gamma(&1)) /\
               mfd_dist (top,atlas) g (gamma(&0)) (gamma tau) <= lam /\
               mfd_dist (top,atlas) g (gamma tau) (gamma(&1)) <=
               mfd_length atlas g gamma (&0) (&1) - lam`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `lam:real`] P2BC_LENGTH_IVT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `&0`; `tau:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) tau = lam`)) THEN
    MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gamma:real->A) tau (&1)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

let P3N_CBALL_NEAR = prove
 (`!top atlas (g:A->real^N^N) x y s e.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y <= s /\ &0 < s /\ &0 < e
     ==> ?w. w IN mfd_ball (top,atlas) g x s /\ mfd_joinable (top,atlas) w y /\
             mfd_dist (top,atlas) g w y < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  ASM_CASES_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x y < s` THENL
   [EXISTS_TAC `y:A` THEN ASM_SIMP_TAC[mfd_ball; IN_ELIM_THM; MFD_JOINABLE_REFL; MFD_DIST_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `ee = min e s / &2` THEN
  SUBGOAL_THEN `&0 < ee /\ &2 * ee <= e /\ ee <= s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `y:A`; `ee:real`] RFA_DIST_APPROX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x y <= mfd_length atlas g gam (&0) (&1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:A) = gam(&0) /\ (y:A) = gam(&1)` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `s - ee`] P3N_CURVE_SPLIT_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(gam:real->A) tau` THEN ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.1, small scales: KL Sublemma 79.23 case (a).                      *)
(* If no ball B(x0,t0,s'') with s < s'' <= rr persists on [t0 - s''^2,t0],  *)
(* then a surgery cap at a time T in [t0 - s^2,t0] reaches the closed ball  *)
(* of radius s, and since caps are hot (R >= H), so are points of the open  *)
(* parabolic region P(x0,t0,s) near it (R >= H / 2).  Tools: a uniform     *)
(* choice over finite sets, the gap below t0 - s^2 between surgery times,  *)
(* compactness of the cap against the closed ball, RFA_HC2_EXPOSED_WINDOW.  *)
(* ========================================================================= *)

let P3N_FINITE_EPS = prove
 (`!(P:A->real->bool) Fs.
     FINITE Fs /\ (!x. x IN Fs ==> ?e. &0 < e /\ !d. &0 < d /\ d <= e ==> P x d)
     ==> ?e. &0 < e /\ !x d. x IN Fs /\ &0 < d /\ d <= e ==> P x d`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `Fs:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_THEN(LABEL_TAC "hyp") THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "hyp" (MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `d:real`] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `d <= e1 /\ d <= e2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* no surgery time just below t0 - s^2 *)

let P3N_SURGERY_GAP = prove
 (`!(hs:(A)rfs_history) t0 s.
     &0 < s
     ==> ?e. &0 < e /\
             !k d. 1 <= k /\ k <= hs_count hs /\ &0 < d /\ d <= e /\
                   hs_time hs k < t0 - s pow 2
                   ==> hs_time hs k < t0 - (s + d) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k d. hs_time (hs:(A)rfs_history) k < t0 - s pow 2
                        ==> hs_time hs k < t0 - (s + d) pow 2`;
                 `1..hs_count (hs:(A)rfs_history)`] P3N_FINITE_EPS) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `hs_time (hs:(A)rfs_history) k < t0 - s pow 2` THENL
     [ALL_TAC; EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]] THEN
    ABBREV_TAC `q = sqrt(t0 - hs_time (hs:(A)rfs_history) k)` THEN
    SUBGOAL_THEN `&0 <= q /\ q pow 2 = t0 - hs_time (hs:(A)rfs_history) k` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE; MATCH_MP_TAC SQRT_POW_2] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `s < q` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(q <= s) ==> s < q`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `q pow 2 <= s pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `(q - s) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s + d) pow 2 < q pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]]);;

(* the distance from a fixed point is continuous *)

let P3N_DIST_SECTION_CONT = prove
 (`!top atlas (g:A->real^N^N) x0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x0 IN topspace top
     ==> continuous_map (top,euclideanreal) (\y. mfd_dist (top,atlas) g x0 y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                MFD_DIST_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\y. mfd_dist (top,atlas) (g:A->real^N^N) x0 y) =
                (\(x,y). mfd_dist (top,atlas) g x y) o (\y:A. (x0:A),y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (top:A topology) top` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN
  ASM_REWRITE_TAC[]);;

(* a persisting region carries the same topology in all its slices *)

let P3N_REGION_SUBTOP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b s.
     p2c_regular_view V /\ rfs_persists V W a b /\ a <= s /\ s <= b /\
     (s = a ==> a < b /\ open_in (rfs_vtop V a) W)
     ==> subtopology (rfs_vtop V s) W = subtopology (rfs_vtop V b) W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) W
                           (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) b) (rfs_vatlas V b) W
                           (\y:A. y) (\y. y)` MP_TAC THENL
   [ASM_CASES_TAC `s:real = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `a:real = a ==> a < b /\ open_in (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a) W` THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3))` THEN
      REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o el 4 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN SIMP_TAC[]);;

(* the cap of event k lives in the slice at the surgery time *)

let P3N_CAP_SLICE = prove
 (`!(hs:(A)rfs_history) k i.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k)
     ==> rfs_top_at hs (hs_time hs k) = hs_top hs k /\
         rfs_atlas_at hs (hs_time hs k) = hs_atlas hs k /\
         hausdorff_space (hs_top hs k) /\
         compact_in (hs_top hs k) (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `hs_time (hs:(A)rfs_history) k`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[rfs_history_ok]; SIMP_TAC[]] THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  MATCH_MP_TAC P3H_EVENT_CAP_COMPACT THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                        `hs_metric (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                        `hs_atlas (hs:(A)rfs_history) k`; `hs_metric (hs:(A)rfs_history) k`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_history_ok]);;

(* balls of a view, for a view variable *)

let P3N_VBALL = GEN_ALL(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)));;

(* compactness of a cap against the closed ball at time t0 *)

let P3N_CAP_DIST_GAP = prove
 (`!(hs:(A)rfs_history) k i x0 t0 s s0.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
     hs_time hs k <= t0 /\ &0 < s /\ s < s0 /\
     x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\
     rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s0) (hs_time hs k) t0 /\
     open_in (rfs_vtop (rfs_view hs) (hs_time hs k)) (rfs_vball (rfs_view hs) t0 x0 s0) /\
     (!c. c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)) /\
          mfd_joinable (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0) x0 c
          ==> s < mfd_dist (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                           (rfs_vmetric (rfs_view hs) t0) x0 c)
     ==> ?e. &0 < e /\ e <= s0 - s /\
             DISJOINT (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)))
                      (rfs_vball (rfs_view hs) t0 x0 (s + e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  ABBREV_TAC `Tk = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `Cp = IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) i) (cball(vec 0:real^3,&1))` THEN
  ABBREV_TAC `W0 = rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0 x0 s0` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `i:num`] P3N_CAP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) Tk = hs_top hs k` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact_space (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0)` ASSUME_TAC
  THENL [EXPAND_TAC "V" THEN ASM_SIMP_TAC[P2C_RFS_VIEW_PARTS; P2CW_HIST_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `subtopology (hs_top hs k) W0 =
                subtopology (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) (W0:A->bool)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) Tk = hs_top hs k`)) THEN
    ASM_CASES_TAC `Tk:real = t0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P3N_REGION_SUBTOP THEN EXISTS_TAC `Tk:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s2 = (s + s0) / &2` THEN
  SUBGOAL_THEN `s < s2 /\ s2 < s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Kb = mfd_cball (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0,rfs_vatlas V t0)
                   (rfs_vmetric V t0) x0 s2` THEN
  SUBGOAL_THEN `(Kb:A->bool) SUBSET W0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kb"; "W0"] THEN
    REWRITE_TAC[SUBSET; mfd_cball; P3N_VBALL; IN_ELIM_THM; mfd_ball] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) Kb` ASSUME_TAC
  THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kb" THEN
    MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (hs_top (hs:(A)rfs_history) k) (Kb:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in (subtopology (hs_top (hs:(A)rfs_history) k) W0) (Kb:A->bool)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = (Cp:A->bool) INTER Kb` THEN
  SUBGOAL_THEN `compact_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) Kc` ASSUME_TAC
  THENL
   [SUBGOAL_THEN `compact_in (hs_top (hs:(A)rfs_history) k) (Kc:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Kc" THEN MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN
      CONJ_TAC THENL [EXPAND_TAC "Cp" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Kc:A->bool) SUBSET W0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `compact_in (subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W0)
                    (Kc:A->bool)` MP_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `subtopology (hs_top (hs:(A)rfs_history) k) W0 =
                    subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W0`)) THEN
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `Kc:A->bool = {}` THENL
   [EXISTS_TAC `s2 - s` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `Kc:A->bool = {}` THEN MAP_EVERY EXPAND_TAC ["Kc"; "Kb"] THEN
    REWRITE_TAC[DISJOINT; P3N_VBALL; mfd_ball; mfd_cball; EXTENSION; IN_INTER; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    DISCH_TAC THEN X_GEN_TAC `c:A` THEN POP_ASSUM(MP_TAC o SPEC `c:A`) THEN
    REWRITE_TAC[REAL_ARITH `s + s2 - s = s2`] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t0`; `x0:A`] P3N_DIST_SECTION_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\y. mfd_dist (rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0,rfs_vatlas V t0)
                   (rfs_vmetric V t0) x0 y) (Kc:A->bool)` REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; real_compact_def] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) t0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `cm:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  ABBREV_TAC `m = mfd_dist (rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0,rfs_vatlas V t0)
                   (rfs_vmetric V t0) x0 cm` THEN
  SUBGOAL_THEN `s < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(cm:A) IN Kc` THEN MAP_EVERY EXPAND_TAC ["Kc"; "Kb"; "Cp"] THEN
    REWRITE_TAC[IN_INTER; mfd_cball; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min (s2 - s) (m - s)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `c:A` THEN
  REWRITE_TAC[P3N_VBALL; mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:A) IN Kc` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kc"; "Kb"] THEN REWRITE_TAC[IN_INTER; mfd_cball; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "min" (MP_TAC o C MP (ASSUME `(c:A) IN Kc`) o SPEC `c:A`) THEN
  ASM_REAL_ARITH_TAC);;

(* a hot point in the closure of the parabolic region (at its bottom time  *)
(* or later) gives a hot point of the open region nearby                     *)

let P3N_HOT_NEAR = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W0 x0 t0 s Tc c H.
     p2c_regular_view V /\ &0 < s /\ t0 - s pow 2 <= Tc /\ Tc <= t0 /\
     x0 IN topspace(rfs_vtop V t0) /\ open_in (rfs_vtop V t0) W0 /\
     rfs_persists V W0 Tc t0 /\ open_in (rfs_vtop V Tc) W0 /\ c IN W0 /\
     mfd_joinable (rfs_vtop V t0,rfs_vatlas V t0) x0 c /\
     mfd_dist (rfs_vtop V t0,rfs_vatlas V t0) (rfs_vmetric V t0) x0 c <= s /\
     H <= rfs_vscalar V Tc c /\ &0 < H
     ==> ?t y. t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball V t0 x0 s /\
               H / &2 <= rfs_vscalar V t y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W0`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* a ball about c at time t0 inside a given open neighbourhood meets B(x0,t0,s) *)
  SUBGOAL_THEN
   `!N. open_in (rfs_vtop V t0) N /\ (c:A) IN N
        ==> ?w. w IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t0 x0 s /\ w IN N`
  (LABEL_TAC "meet") THENL
   [X_GEN_TAC `N:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `N:A->bool`] MFD_OPEN_IN_BALLS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:A` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ep:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `x0:A`; `c:A`; `s:real`; `ep:real`]
                  P3N_CBALL_NEAR) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[P3N_VBALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                   `c:A`; `w:A`] MFD_JOINABLE_SYM) THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `c:A`; `w:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `Tc:real = t0` THENL
   [(* the hot point is at the top time: spatial continuity *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`] MFD_SCALAR_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "meet" (MP_TAC o SPEC
      `{y | y IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t0) /\
            mfd_scalar (rfs_vatlas V t0) (rfs_vmetric V t0) y IN {r | r > H / &2}}`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC `euclideanreal` THEN
        ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_GT; ETA_AX];
        REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        UNDISCH_TAC `H <= rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) t0 c` THEN
        REWRITE_TAC[P2C_VIEW_EXPAND] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`t0:real`; `w:A`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [MP_TAC(SPECL [`s:real`; `2`] REAL_POW_LT) THEN ASM_SIMP_TAC[] THEN
                    REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:A) IN {y | y IN topspace(rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) /\
                   mfd_scalar (rfs_vatlas V t0) (rfs_vmetric V t0) y IN {r | r > H / &2}}` THEN
    REWRITE_TAC[IN_ELIM_THM; P2C_VIEW_EXPAND] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the hot point is at an earlier time: joint continuity on the region *)
  SUBGOAL_THEN `Tc < t0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W0:A->bool`; `Tc:real`; `t0:real`]
                P3N_REGION_SCALAR_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{r | r > H / &2}` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    OPEN_IN_CONTINUOUS_MAP_PREIMAGE)) THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_GT; OPEN_IN_PROD_TOPOLOGY_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`Tc:real`; `c:A`]) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL; INTER_UNIV; IN_INTER; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real->bool` (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
  (* a time interval [Tc,Tc+dl) in u *)
  UNDISCH_TAC `open_in (subtopology euclideanreal {t | Tc <= t /\ t < t0}) (u:real->bool)` THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM REAL_OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `real_open (u':real->bool)` THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `Tc:real`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `(Tc:real) IN u` THEN ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  (* a point of B(x0,t0,s) in v *)
  USE_THEN "meet" (MP_TAC o SPEC `v:A->bool`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    UNDISCH_TAC `open_in (subtopology (rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W0) v` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`Tc + min dl (t0 - Tc) / &2`; `w:A`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Tc + min dl (t0 - Tc) / &2,(w:A)) IN (u:real->bool) CROSS v` MP_TAC THENL
   [REWRITE_TAC[IN_CROSS] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Tc + min dl (t0 - Tc) / &2 IN u'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    can (find_term (fun t -> t = `(u:real->bool) CROSS (v:A->bool)`)) (concl th) &&
    is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET")) THEN
  DISCH_THEN(MP_TAC o SPEC `(Tc + min dl (t0 - Tc) / &2,(w:A))`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; FST; SND] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3N_EV_INDEX_FINITE = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs ==> FINITE(ev_index(hs_event hs k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1)) (hs_metric hs (k - 1))
                 (hs_time hs k) (hs_top hs k,hs_atlas hs k) (hs_metric hs k)
                 (hs_event (hs:(A)rfs_history) k)` MP_TAC THENL
   [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  REWRITE_TAC[rfs_event_ok; mfd_cut_cap] THEN SIMP_TAC[]);;

(* KL Sublemma 79.23 (a): no persisting larger ball ==> a hot point *)

let P3N_TIGHT_A = prove
 (`!(hs:(A)rfs_history) x0 t0 s rr H.
     rfs_history_ok hs /\ &0 < s /\ s < rr /\ rr pow 2 <= t0 /\ t0 < rfs_horizon hs /\
     x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\
     (!s'. s < s' /\ s' <= rr
           ==> ~rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s') (t0 - s' pow 2) t0) /\
     (!k i c. 1 <= k /\ k <= hs_count hs /\
              t0 - rr pow 2 <= hs_time hs k /\ hs_time hs k <= t0 /\
              i IN ev_index(hs_event hs k) /\
              c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
              ==> H <= rfs_vscalar (rfs_view hs) (hs_time hs k) c) /\
     &0 < H
     ==> ?t y. t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 s /\
               H / &2 <= rfs_vscalar (rfs_view hs) t y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "np")
    (CONJUNCTS_THEN2 (LABEL_TAC "hot") ASSUME_TAC)))))))) THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_top_at (hs:(A)rfs_history) = rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_THEN(LABEL_TAC "nohot") THEN
  (* 1. the gap below t0 - s^2 *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`; `s:real`] P3N_SURGERY_GAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "gap"))) THEN
  (* 2. caps stay away, uniformly *)
  MP_TAC(ISPECL
   [`\p:num#num d. ~(t0 - s pow 2 <= hs_time (hs:(A)rfs_history) (FST p) /\
                     hs_time hs (FST p) <= t0 /\
                     rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (rfs_vball V t0 (x0:A) (s + d)) (hs_time hs (FST p)) t0 /\
                     open_in (rfs_vtop V (hs_time hs (FST p))) (rfs_vball V t0 x0 (s + d)) /\
                     ~DISJOINT (rfs_vball V t0 x0 (s + d))
                               (IMAGE (ev_capm (hs_event hs (FST p)) (SND p)) (cball(vec 0,&1))))`;
    `{(k,i) | k IN 1..hs_count (hs:(A)rfs_history) /\ i IN ev_index(hs_event hs k)}`]
   P3N_FINITE_EPS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(,):num->num->num#num`; `1..hs_count (hs:(A)rfs_history)`;
                     `\k. ev_index(hs_event (hs:(A)rfs_history) k)`] FINITE_PRODUCT_DEPENDENT) THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_EV_INDEX_FINITE THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_NUMSEG] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `i:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC
     `?d0. &0 < d0 /\ d0 <= rr - s /\
           t0 - s pow 2 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k <= t0 /\
           rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (rfs_vball V t0 (x0:A) (s + d0)) (hs_time hs k) t0 /\
           open_in (rfs_vtop V (hs_time hs k)) (rfs_vball V t0 x0 (s + d0))` THENL
     [ALL_TAC;
      EXISTS_TAC `rr - s` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      UNDISCH_TAC `~(?d0. &0 < d0 /\ d0 <= rr - s /\
           t0 - s pow 2 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k <= t0 /\
           rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (rfs_vball V t0 (x0:A) (s + d0)) (hs_time hs k) t0 /\
           open_in (rfs_vtop V (hs_time hs k)) (rfs_vball V t0 x0 (s + d0)))` THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN STRIP_TAC THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    (* the cap does not reach the closed ball of radius s *)
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `i:num`; `x0:A`; `t0:real`; `s:real`;
                   `s + d0`] P3N_CAP_DIST_GAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `c:A` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `~(d <= s) ==> s < d`) THEN DISCH_TAC THEN
      USE_THEN "nohot" MP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC P3N_HOT_NEAR THEN
      MAP_EVERY EXISTS_TAC [`rfs_vball (V:(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                               t0 x0 (s + d0)`; `hs_time (hs:(A)rfs_history) k`; `c:A`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[P3N_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[P3N_VBALL; mfd_ball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "hot" MATCH_MP_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `s pow 2 <= rr pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (STRIP_ASSUME_TAC o
      REWRITE_RULE[ASSUME `rfs_view (hs:(A)rfs_history) = V`])) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REPEAT DISJ2_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 (x0:A) (s + d) SUBSET rfs_vball V t0 x0 (s + e)`
    MP_TAC THENL
     [REWRITE_TAC[P3N_VBALL; SUBSET; mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) i) (cball(vec 0,&1)))
                          (rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 (x0:A) (s + e))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "away"))) THEN
  (* 3. the exposed window at s' = s + d *)
  ABBREV_TAC `d = min (min e1 e2) (rr - s)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= e1 /\ d <= e2 /\ s + d <= rr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `rfs_vball (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 x0 (s + d)`;
                 `t0 - (s + d) pow 2`; `t0:real`] RFA_HC2_EXPOSED_WINDOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(s + d) pow 2 <= rr pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < (s + d) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[P3N_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      USE_THEN "np" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `i:num` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `rfs_view (hs:(A)rfs_history) = (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`;
                 ASSUME `rfs_top_at (hs:(A)rfs_history) = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`]))) THEN
  USE_THEN "away" (MP_TAC o SPECL [`(k,i):num#num`; `d:real`]) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FST; SND; IN_ELIM_PAIR_THM; IN_NUMSEG; NOT_IMP] THEN
  SUBGOAL_THEN `t0 - s pow 2 <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(x < a) ==> a <= x`) THEN DISCH_TAC THEN
    USE_THEN "gap" (MP_TAC o SPECL [`k:num`; `d:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: KL Sublemma 79.23 case (b).                      *)
(* If a larger ball B(x0,t0,s'') persists on [t0 - s''^2,t0] and R < M on   *)
(* the open region P(x0,t0,s), then R < 2M on P(x0,t0,s1) for some s1 > s  *)
(* (joint continuity of R, P3N_HOT_NEAR on the closure, Wallace's theorem), *)
(* and by pinching (P3N_PINCH_LOWER) abs Rm <= s1^-2 there: s1 is admissible.*)
(* ========================================================================= *)

(* an open set containing a closed ball contains a larger open ball *)

let P3N_CBALL_OPEN_NBHD = prove
 (`!top atlas (g:A->real^N^N) x0 s U.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ x0 IN topspace top /\ &0 < s /\ open_in top U /\
     mfd_cball (top,atlas) g x0 s SUBSET U
     ==> ?e. &0 < e /\ mfd_ball (top,atlas) g x0 (s + e) SUBSET U`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Fc = mfd_cball (top,atlas) (g:A->real^N^N) x0 (s + &1) DIFF U` THEN
  SUBGOAL_THEN `compact_in (top:A topology) Fc` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fc" THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED];
    ALL_TAC] THEN
  ASM_CASES_TAC `Fc:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    UNDISCH_TAC `Fc:A->bool = {}` THEN EXPAND_TAC "Fc" THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; NOT_IN_EMPTY; SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`] P3N_DIST_SECTION_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\y. mfd_dist (top,atlas) (g:A->real^N^N) x0 y) (Fc:A->bool)`
                REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; real_compact_def] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  ABBREV_TAC `m = mfd_dist (top,atlas) (g:A->real^N^N) x0 q` THEN
  SUBGOAL_THEN `s < m` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(m <= s) ==> s < m`) THEN DISCH_TAC THEN
    UNDISCH_TAC `(q:A) IN Fc` THEN EXPAND_TAC "Fc" THEN
    REWRITE_TAC[IN_DIFF; mfd_cball; IN_ELIM_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((q:A) IN U)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `U:A->bool`)) (concl th) && is_comb(concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET")) THEN
    ASM_REWRITE_TAC[mfd_cball; IN_ELIM_THM];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1) (m - s)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN Fc` ASSUME_TAC THENL
   [EXPAND_TAC "Fc" THEN ASM_REWRITE_TAC[IN_DIFF; mfd_cball; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "min" (MP_TAC o C MP (ASSUME `(y:A) IN Fc`) o SPEC `y:A`) THEN
  ASM_REAL_ARITH_TAC);;

(* a region persisting up to t0 persists a little beyond t0, in the same slice *)

let P3N_PERSIST_EXTEND = prove
 (`!(hs:(A)rfs_history) W a t0.
     rfs_history_ok hs /\ &0 <= t0 /\ t0 < rfs_horizon hs /\ a < t0 /\
     rfs_persists (rfs_view hs) W a t0
     ==> ?b. t0 < b /\ rfs_top_at hs b = rfs_top_at hs t0 /\
             rfs_atlas_at hs b = rfs_atlas_at hs t0 /\
             rfs_persists (rfs_view hs) W a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`] P3X_SLAB_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!u. t0 <= u /\ u < hs_time (hs:(A)rfs_history) (k + 1)
                    ==> rfs_top_at hs u = rfs_top_at hs t0 /\
                        rfs_atlas_at hs u = rfs_atlas_at hs t0` (LABEL_TAC "same") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `u:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t0:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(t0 + hs_time (hs:(A)rfs_history) (k + 1)) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "same" (MP_TAC o SPEC `(t0 + hs_time (hs:(A)rfs_history) (k + 1)) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_persists (rfs_view hs) (W:A->bool) a t0` THEN
  REWRITE_TAC[P3X_PERSISTS_VIEW] THEN DISCH_THEN(LABEL_TAC "pers") THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN ASM_CASES_TAC `u <= t0` THENL
   [USE_THEN "pers" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "same" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "pers" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* the cool region extends: R < M on P(x0,t0,s) gives R < 2M on a larger   *)
(* parabolic region, inside a persisting ball B(x0,t0,s2), s < s2           *)

let P3N_COOL_TUBE = prove
 (`!(hs:(A)rfs_history) x0 t0 s s2 M.
     rfs_history_ok hs /\ &0 < s /\ s < s2 /\ s2 pow 2 <= t0 /\ t0 < rfs_horizon hs /\
     x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\
     rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s2) (t0 - s2 pow 2) t0 /\
     &0 < M /\
     (!t y. t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 s
            ==> rfs_vscalar (rfs_view hs) t y < M)
     ==> ?s1. s < s1 /\ s1 <= s2 /\
              !t y. t0 - s1 pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 s1
                    ==> rfs_vscalar (rfs_view hs) t y < &2 * M`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cool"))))))))) THEN
  SUBGOAL_THEN `!t. compact_space (rfs_top_at (hs:(A)rfs_history) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2CW_HIST_COMPACT]; ALL_TAC] THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_top_at (hs:(A)rfs_history) = rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) /\
                rfs_atlas_at hs = rfs_vatlas V`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact_space (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0)` ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W2 = rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0 x0 s2` THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W2` ASSUME_TAC
  THENL
   [EXPAND_TAC "W2" THEN REWRITE_TAC[P3N_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ s pow 2 < s2 pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* 1. persistence a little beyond t0, and the start time a' *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W2:A->bool`; `t0 - s2 pow 2`; `t0:real`]
                P3N_PERSIST_EXTEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `a1 = t0 - (s pow 2 + s2 pow 2) / &2` THEN
  SUBGOAL_THEN `t0 - s2 pow 2 < a1 /\ a1 < t0 - s pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W2 a1 b /\
                open_in (rfs_vtop V a1) W2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W2:A->bool) (t0 - s2 pow 2) b` THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `a1:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b = rfs_vtop V t0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* 2. joint continuity and the cool open set *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W2:A->bool`; `a1:real`; `b:real`]
                P3N_REGION_SCALAR_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `PT = prod_topology (subtopology euclideanreal {t | a1 <= t /\ t < b})
                                 (subtopology (rfs_vtop (V:(real->A topology)#
                                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0)
                                   (W2:A->bool))` THEN
  ABBREV_TAC `Oc = {z | z IN topspace PT /\
                       (\z. rfs_vscalar (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                              (FST z) (SND z)) z IN {r | r < &2 * M}}` THEN
  SUBGOAL_THEN `open_in PT (Oc:real#A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Oc" THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT];
    ALL_TAC] THEN
  (* 3. the compact closure of P(x0,t0,s) lies in the cool open set *)
  ABBREV_TAC `K2 = mfd_cball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0,rfs_vatlas V t0) (rfs_vmetric V t0) x0 s` THEN
  SUBGOAL_THEN `(K2:A->bool) SUBSET W2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K2"; "W2"] THEN
    REWRITE_TAC[SUBSET; mfd_cball; P3N_VBALL; IN_ELIM_THM; mfd_ball] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W2) K2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K2" THEN MATCH_MP_TAC MFD_CBALL_CLOSED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (subtopology euclideanreal {t | a1 <= t /\ t < b})
                  (real_interval[t0 - s pow 2,t0])` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[t0 - s pow 2,t0] CROSS (K2:A->bool) SUBSET Oc` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN W2 /\ y IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W2`)) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "Oc" THEN EXPAND_TAC "PT" THEN
    REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL; INTER_UNIV; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `~(&2 * M <= r) ==> r < &2 * M`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W2:A->bool`; `x0:A`; `t0:real`; `s:real`;
                   `t:real`; `y:A`; `&2 * M`] P3N_HOT_NEAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `rfs_persists V (W2:A->bool) a1 b` THEN
        REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
        DISCH_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `rfs_persists V (W2:A->bool) a1 b` THEN
        REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
        DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        UNDISCH_TAC `(y:A) IN K2` THEN EXPAND_TAC "K2" THEN
        REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN SIMP_TAC[];
        UNDISCH_TAC `(y:A) IN K2` THEN EXPAND_TAC "K2" THEN
        REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN SIMP_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real` (X_CHOOSE_THEN `y':A` STRIP_ASSUME_TAC)) THEN
    USE_THEN "cool" (MP_TAC o SPECL [`t':real`; `y':A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* 4. Wallace's theorem: a product neighbourhood *)
  MP_TAC(ISPECL [`subtopology euclideanreal {t | a1 <= t /\ t < b}`;
                 `subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W2`; `Oc:real#A->bool`;
                 `real_interval[t0 - s pow 2,t0]`; `K2:A->bool`]
                WALLACE_THEOREM_PROD_TOPOLOGY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "PT" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:real->bool` (X_CHOOSE_THEN `U2:A->bool` STRIP_ASSUME_TAC)) THEN
  (* 5. a time margin below t0 - s^2 *)
  UNDISCH_TAC `open_in (subtopology euclideanreal {t | a1 <= t /\ t < b}) (U1:real->bool)` THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM REAL_OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1':real->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `real_open (U1':real->bool)` THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `t0 - s pow 2`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `t0 - s pow 2 IN (U1:real->bool)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `U1:real->bool`)) (concl th) &&
        can (find_term (fun t -> t = `real_interval[t0 - s pow 2,t0]`)) (concl th))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `dl1 = min dl (t0 - s pow 2 - a1)` THEN
  SUBGOAL_THEN `&0 < dl1 /\ dl1 <= dl /\ dl1 <= t0 - s pow 2 - a1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t0 - s pow 2 - dl1 < t /\ t <= t0 ==> t IN (U1:real->bool)`
  (LABEL_TAC "U1") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t0 - s pow 2 <= t` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `U1:real->bool`)) (concl th) &&
        can (find_term (fun t -> t = `real_interval[t0 - s pow 2,t0]`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* 6. a space margin beyond s *)
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `x0:A`; `s:real`; `U2:A->bool`]
                P3N_CBALL_OPEN_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `open_in (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W2) (U2:A->bool)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` STRIP_ASSUME_TAC) THEN
  (* 7. the larger cool region *)
  EXISTS_TAC `min (min (s + ep) s2) (sqrt(s pow 2 + dl1))` THEN
  ABBREV_TAC `s1 = min (min (s + ep) s2) (sqrt(s pow 2 + dl1))` THEN
  SUBGOAL_THEN `s < sqrt(s pow 2 + dl1) /\ sqrt(s pow 2 + dl1) pow 2 = s pow 2 + dl1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < s1 /\ s1 <= s2 /\ s1 <= s + ep /\ s1 <= sqrt(s pow 2 + dl1)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 <= s pow 2 + dl1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `sqrt(s pow 2 + dl1) pow 2 = s pow 2 + dl1`)) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real,(y:A)) IN Oc` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `(U1:real->bool) CROSS (U2:A->bool)`)) (concl th))) THEN
    REWRITE_TAC[IN_CROSS] THEN CONJ_TAC THENL
     [USE_THEN "U1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `U2:A->bool`)) (concl th) &&
        can (find_term (fun t -> t = `s + ep`)) (concl th))) THEN
      UNDISCH_TAC `(y:A) IN rfs_vball V t0 x0 s1` THEN
      REWRITE_TAC[P3N_VBALL; mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXPAND_TAC "Oc" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]);;

(* pinching in a view variable *)

let P3N_PINCHED_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     rfs_pinched V /\ &0 <= t /\ x IN topspace(rfs_vtop V t)
     ==> rfs_pinched_at (rfs_vatlas V t) (rfs_vmetric V t) t x`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_pinched; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  MESON_TAC[]);;

(* KL Sublemma 79.23 (b): a persisting larger ball and no hot point make a  *)
(* larger scale admissible (pinching turns R < 2M into abs Rm <= s1^-2)       *)

let P3N_TIGHT_B = prove
 (`!(hs:(A)rfs_history) x0 t0 s s2 M.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     &0 < s /\ s < s2 /\ s2 pow 2 <= t0 /\ t0 < rfs_horizon hs /\
     x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\
     rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s2) (t0 - s2 pow 2) t0 /\
     &0 < M /\ &8 * M <= inv(s2 pow 2) /\ &4 * exp(&4) <= inv(s2 pow 2) /\
     (!t y. t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 s
            ==> rfs_vscalar (rfs_view hs) t y < M)
     ==> ?s1. s < s1 /\ s1 <= s2 /\ p3n_adm (rfs_view hs) t0 x0 s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `s2:real`; `M:real`]
                P3N_COOL_TUBE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "tube")))) THEN
  EXISTS_TAC `s1:real` THEN ASM_REWRITE_TAC[p3n_adm] THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 pow 2 <= s2 pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 pow 2 /\ inv(s2 pow 2) <= inv(s1 pow 2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W2 = rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0 x0 s2` THEN
  SUBGOAL_THEN `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) t0 x0 s1 SUBSET W2` ASSUME_TAC THENL
   [EXPAND_TAC "W2" THEN REWRITE_TAC[P3N_VBALL; SUBSET; mfd_ball; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W2 (t0 - s1 pow 2) t0` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W2:A->bool) (t0 - s2 pow 2) t0` THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    DISCH_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_parabolic_exists] THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC P3N_PERSIST_SUBOPEN THEN EXISTS_TAC `W2:A->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P3N_VBALL; GSYM P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_BALL_OPEN THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `t0:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) /\ &0 <= t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `rfs_persists V (W2:A->bool) (t0 - s1 pow 2) t0` THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) W2`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `W2:A->bool`)) (concl th) && is_comb(concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET")) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t:real`; `y:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "tube" (MP_TAC o SPECL [`t:real`; `y:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(i < r) ==> r <= i`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`; `rfs_vatlas (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`; `t:real`; `y:A`] P3N_PINCH_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3N_PINCHED_AT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: the dichotomy of KL Sublemma                     *)
(* 79.23 at the maximal admissible scale s < rr: either case (b) (a larger  *)
(* ball persists; then without a hot point a larger scale would be          *)
(* admissible) or case (a) (no larger ball persists; then a cap is near).   *)
(* In both cases P(x0,t0,s) contains a point with R >= min (H/2) (rr^-2/8).  *)
(* ========================================================================= *)

let P3N_TIGHT_EXISTS = prove
 (`!(hs:(A)rfs_history) x0 t0 s rr H.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     &0 < s /\ s < rr /\ rr pow 2 <= t0 /\ t0 < rfs_horizon hs /\
     x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\ p3n_adm (rfs_view hs) t0 x0 s /\
     (!s'. s < s' /\ s' <= rr ==> ~p3n_adm (rfs_view hs) t0 x0 s') /\
     (!k i c. 1 <= k /\ k <= hs_count hs /\
              t0 - rr pow 2 <= hs_time hs k /\ hs_time hs k <= t0 /\
              i IN ev_index(hs_event hs k) /\
              c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
              ==> H <= rfs_vscalar (rfs_view hs) (hs_time hs k) c) /\
     &0 < H /\ &4 * exp(&4) <= inv(rr pow 2)
     ==> ?t y. t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 s /\
               min (H / &2) (inv(rr pow 2) / &8) <= rfs_vscalar (rfs_view hs) t y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "max") (CONJUNCTS_THEN2 (LABEL_TAC "hot")
    STRIP_ASSUME_TAC)))))))))) THEN
  ABBREV_TAC `M = min (H / &2) (inv(rr pow 2) / &8)` THEN
  SUBGOAL_THEN `&0 < inv(rr pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < M /\ M <= H / &2 /\ &8 * M <= inv(rr pow 2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_THEN(LABEL_TAC "nohot") THEN
  SUBGOAL_THEN `!t y. t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 s
                      ==> rfs_vscalar (rfs_view (hs:(A)rfs_history)) t y < M`
  (LABEL_TAC "cool") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(M <= r) ==> r < M`) THEN DISCH_TAC THEN
    USE_THEN "nohot" MP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t:real`; `y:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?s2. s < s2 /\ s2 <= rr /\
                      rfs_persists (rfs_view hs) (rfs_vball (rfs_view (hs:(A)rfs_history)) t0 x0 s2)
                                   (t0 - s2 pow 2) t0` THENL
   [(* case (b) *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `s2:real`; `M:real`]
                  P3N_TIGHT_B) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s2 pow 2 <= rr pow 2 /\ &0 < s2 pow 2` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(rr pow 2) <= inv(s2 pow 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "max" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    (* case (a) *)
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `rr:real`; `H:real`]
                  P3N_TIGHT_A) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s':real` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
    USE_THEN "cool" (MP_TAC o SPECL [`t:real`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: cross-slice geometry on a                        *)
(* persisting region W over (a,b].  A curve of the slice at u inside W is a *)
(* curve of the slice at b, with b-length <= lam times its u-length when    *)
(* the region metric at b is <= lam^2 times the one at u (P3N_XCURVE_UB);  *)
(* by a first-exit argument (as RFA_CURVE_STAYS), the u-ball of radius r/lam *)
(* about z lies in the b-ball of radius r when that ball lies in W          *)
(* (P3N_XBALL_IN).                                                          *)
(* ========================================================================= *)

let P3N_XCURVE_UB = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b u (gam:real->A) c1 lam.
     p2c_regular_view V /\ a < u /\ u < b /\ rfs_persists V W a b /\
     mfd_c1_curve (rfs_vtop V u,rfs_vatlas V u) gam (&0) c1 /\ &0 < c1 /\
     (!s. s IN real_interval[&0,c1] ==> gam s IN W) /\ &0 < lam /\
     (!y w. y IN W
            ==> w dot (p2c_vfam V W b b y ** w) <= lam pow 2 * (w dot (p2c_vfam V W b u y ** w)))
     ==> mfd_c1_curve (rfs_vtop V b,rfs_vatlas V b) gam (&0) c1 /\
         mfd_length (rfs_vatlas V b) (rfs_vmetric V b) gam (&0) c1 <=
         lam * mfd_length (rfs_vatlas V u) (rfs_vmetric V u) gam (&0) c1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inW")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cmp"))))))))) THEN
  (* the slices and the region *)
  SUBGOAL_THEN `(gam:real->A)(&0) IN W` ASSUME_TAC THENL
   [USE_THEN "inW" MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(SPEC `u:real` (REWRITE_RULE[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] th)) THEN
    MP_TAC(SPEC `b:real` (REWRITE_RULE[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `(gam:real->A)(&0)`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `u:real`; `(gam:real->A)(&0)`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`]
                P2C_REGULAR_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`] P2C_REGULAR_VFLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2c_vflow] THEN STRIP_TAC THEN
  (* the curve in the slice at b and in the region chart *)
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) u`; `rfs_vatlas (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                 `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `gam:real->A`; `&0`; `c1:real`] P2B9S_PB_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y:A. y) o (gam:real->A) = gam` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (subtopology (rfs_vtop V b) W,
                  restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                 (gam:real->A) (&0) c1` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HC2_C1_CURVE_SUBTOP THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inW" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `u:real`; `b:real`; `gam:real->A`;
                 `&0`; `c1:real`] RFA_HC2_REGION_LENGTH_START) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `mfd_length (rfs_vatlas V b) (rfs_vmetric V b) (gam:real->A) (&0) c1 =
    mfd_length (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
               (p2c_vfam V W b b) gam (&0) c1` SUBST1_TAC THENL
   [REWRITE_TAC[p2c_vfam; ETA_AX] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2AP_LENGTH_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b u`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b b`;
                 `lam pow 2`; `gam:real->A`; `&0`; `c1:real`] MFD_LENGTH_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `a:real`; `b:real`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W b`; `u:real`] P2AP_UPTO_RIEM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `a:real`; `b:real`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W b`; `b:real`] P2AP_UPTO_RIEM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `v:real^3`] THEN STRIP_TAC THEN
      USE_THEN "cmp" MATCH_MP_TAC THEN USE_THEN "inW" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]);;

let P3N_XBALL_IN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b u z r lam.
     p2c_regular_view V /\ a < u /\ u < b /\ rfs_persists V W a b /\
     compact_space (rfs_vtop V b) /\ &0 < r /\ &0 < lam /\ z IN W /\
     mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) z r SUBSET W /\
     (!y w. y IN W
            ==> w dot (p2c_vfam V W b b y ** w) <= lam pow 2 * (w dot (p2c_vfam V W b u y ** w)))
     ==> mfd_ball (rfs_vtop V u,rfs_vatlas V u) (rfs_vmetric V u) z (r / lam) SUBSET
         mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) z r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inW") (LABEL_TAC "cmp")))))))))) THEN
  UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(SPEC `u:real` (REWRITE_RULE[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] th)) THEN
    MP_TAC(SPEC `b:real` (REWRITE_RULE[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) /\
                z IN topspace(rfs_vtop V u)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `u:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Rb = mfd_ball (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b,rfs_vatlas V b)
                   (rfs_vmetric V b) z r` THEN
  (* one topology on W *)
  SUBGOAL_THEN `subtopology (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) W =
                subtopology (rfs_vtop V b) W` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_REGION_SUBTOP THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) Rb` ASSUME_TAC
  THENL
   [SUBGOAL_THEN `open_in (subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) W) Rb`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY] THEN
      EXPAND_TAC "Rb" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:A` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  (* a near-minimizing curve of the slice at u *)
  ABBREV_TAC `ee = (r / lam - mfd_dist (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u,rfs_vatlas V u)
                     (rfs_vmetric V u) z p) / &2` THEN
  SUBGOAL_THEN `&0 < ee` ASSUME_TAC THENL [EXPAND_TAC "ee" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) u`; `rfs_vatlas (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) u`; `z:A`; `p:A`; `ee:real`] RFA_DIST_APPROX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = mfd_length (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                  (rfs_vmetric V u) gam (&0) (&1)` THEN
  SUBGOAL_THEN `lam * L < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `L < r / lam` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> (gam:real->A) s IN Rb` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`; `gam:real->A`; `Rb:A->bool`]
                  GRGD_FIRST_TIME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Rb" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
        ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL];
        EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `Fb = mfd_cball (rfs_vtop (V:(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b,rfs_vatlas V b)
                     (rfs_vmetric V b) z (lam * L)` THEN
    SUBGOAL_THEN `(Fb:A->bool) SUBSET Rb` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Fb"; "Rb"] THEN
      REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `closed_in (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) Fb` ASSUME_TAC
    THENL
     [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `compact_in (subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) W) Fb`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fb" THEN
          MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~((gam:real->A) t1 IN Rb)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `(Fb:A->bool) SUBSET Rb`)) THEN
    MATCH_MP_TAC GRGD_CLOSED_LEFT_CURVE THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) u` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
    X_GEN_TAC `sg:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `sg = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fb" THEN
      REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "L" THEN
      MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `rfs_vtop (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`; `gam:real->A`; `&0`; `sg:real`; `&1`]
                  MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`;
                   `gam:real->A`; `sg:real`; `lam:real`] P3N_XCURVE_UB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `q:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gam:real->A) q IN Rb` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN EXPAND_TAC "Fb" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(z:A) = gam(&0)` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b)
                (rfs_vmetric V b) (gam:real->A) (&0) sg` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * mfd_length (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                (rfs_vmetric V u) (gam:real->A) (&0) sg` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`; `gam:real->A`; `sg:real`; `&1`]
                  MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN Rb` MP_TAC THENL
   [SUBGOAL_THEN `(p:A) = gam(&1)` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    EXPAND_TAC "Rb" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM]]);;

(* the identity pullback of a metric agrees with it on the region *)

let P3N_SAME_METRIC_PULLBACK = prove
 (`!top atlas W top' atlas' (g':A->real^3^3).
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas W top' atlas' W (\y:A. y) (\y. y)
     ==> rfs_same_metric_on atlas (mfd_pullback_metric atlas atlas' (\y:A. y) g') atlas' g' W`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_same_metric_on; FORALL_PAIR_THM; IN_IMAGE; IN_INTER; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`; `V':A->bool`; `psi:A->real^3`; `y:real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `g':A->real^3^3`; `U:A->bool`; `phi:A->real^3`;
                 `V':A->bool`; `psi:A->real^3`; `x:A`] P2C_PULLBACK_METRIC_LOCAL_W) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* volumes at u and b of a subset of the region *)

let P3N_XVOL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b u S vu vb lam.
     p2c_regular_view V /\ a < u /\ u < b /\ rfs_persists V W a b /\ S SUBSET W /\
     ~(S = {}) /\ &0 <= lam /\
     mfd_has_volume (rfs_vtop V u,rfs_vatlas V u) (rfs_vmetric V u) S vu /\
     mfd_has_volume (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) S vb /\
     (!y w. y IN W
            ==> w dot (p2c_vfam V W b u y ** w) <= lam * (w dot (p2c_vfam V W b b y ** w)))
     ==> vu <= lam * sqrt lam * vb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y0:A. y0 IN W` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(SPEC `u:real` (REWRITE_RULE[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] th)) THEN
    MP_TAC(SPEC `b:real` (REWRITE_RULE[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `y0:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `u:real`; `y0:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`]
                P2C_REGULAR_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`] P2C_REGULAR_VFLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2c_vflow] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p2c_vfam V W b u)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `a:real`; `b:real`; `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b`; `u:real`] P2AP_UPTO_RIEM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p2c_vfam V W b b)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `a:real`; `b:real`; `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b`; `b:real`] P2AP_UPTO_RIEM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the volume at u as a volume of the region metric *)
  SUBGOAL_THEN
   `mfd_has_volume (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W)
      (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) W b u) S vu`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(u:real = b)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[p2c_vfam; ETA_AX] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                   `mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V u) (\y:A. y)
                      (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) u)`;
                   `W:A->bool`; `S:A->bool`; `vu:real`] P2BC_VOLUME_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                   `mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V u) (\y:A. y)
                      (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) u)`;
                   `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`; `W:A->bool`; `S:A->bool`; `vu:real`]
                  P3H_RETAINED_VOLUME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P3N_SAME_METRIC_PULLBACK THEN
        MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p2c_vfam V W b u)` THEN
        ASM_REWRITE_TAC[p2c_vfam; ETA_AX]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_volume (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W)
      (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) W b b) S vb`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2c_vfam; ETA_AX] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#
                                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `S:A->bool`; `vb:real`]
                  P2BC_VOLUME_RESTRICT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_COMPARE_QF THEN
  MAP_EVERY EXISTS_TAC [`subtopology (rfs_vtop (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                        `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                        `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) W b u`;
                        `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) W b b`; `S:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: KL Sublemma 79.23, the tight                     *)
(* case.  The inward point (P3N_INWARD_POINT), metric comparison on the      *)
(* parabolic region (P3N_PARAB_COMPARE, factor e^4 both ways), and the      *)
(* volume bound: a point (y,t) of P(x0,t0,s) with R(y,t) >= 4 C Rthr has a  *)
(* canonical neighbourhood; the inward point z (within 2 e^2 rho of y at    *)
(* time t) has R(z,t) >= Rthr by the ratio bound, hence a small ball of     *)
(* volume >= kap rho'^3 at time t, which lies in B(x0,t0,s) and keeps      *)
(* volume >= e^-6 kap rho'^3 at time t0 (P3N_TIGHT_VOL).                     *)
(* ========================================================================= *)

let P3N_INWARD_POINT = prove
 (`!top atlas (g:A->real^N^N) x0 y s rho.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN mfd_ball (top,atlas) g x0 s /\ &0 < rho /\ &2 * rho <= s
     ==> ?z. z IN mfd_ball (top,atlas) g x0 s /\
             mfd_ball (top,atlas) g z (&2 * rho) SUBSET mfd_ball (top,atlas) g x0 s /\
             y IN mfd_ball (top,atlas) g z (&2 * rho)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`; `y:A`; `s:real`] RFA_HC2_BALL_CURVE_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = mfd_length atlas (g:A->real^N^N) (gam:real->A) (&0) (&1)` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `min L (s - &2 * rho)`] P3N_CURVE_SPLIT_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(gam:real->A) tau` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM; SUBSET] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x0 ((gam:real->A) tau) +
                mfd_dist (top,atlas) g (gam tau) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* metric comparison on an admissible parabolic region, both ways *)

let P3N_PARAB_COMPARE = prove
 (`!(hs:(A)rfs_history) x0 t0 s u.
     rfs_history_ok hs /\ p3n_adm (rfs_view hs) t0 x0 s /\ t0 - s pow 2 < u /\ u <= t0
     ==> !y w. y IN rfs_vball (rfs_view hs) t0 x0 s
               ==> w dot (p2c_vfam (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s) t0 u y ** w) <=
                   exp(&4) *
                   (w dot (p2c_vfam (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s) t0 t0 y ** w)) /\
                   w dot (p2c_vfam (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s) t0 t0 y ** w) <=
                   exp(&4) *
                   (w dot (p2c_vfam (rfs_view hs) (rfs_vball (rfs_view hs) t0 x0 s) t0 u y ** w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_adm; rfs_parabolic_exists] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  ABBREV_TAC `W = rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) t0 x0 s` THEN
  SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W (t0 - s pow 2) t0` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `t0 - s pow 2`; `t0:real`;
                 `inv(s pow 2)`; `u:real`; `y:A`; `w:real^3`] P2AP_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AB_SVS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REPEAT STRIP_TAC THEN REWRITE_TAC[p3_vrm] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[P2AP_RMETRIC_VFAM] THEN
  SUBGOAL_THEN `exp(&4 * inv(s pow 2) * (t0 - u)) <= exp(&4)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `inv(s pow 2) * (t0 - u) <= inv(s pow 2) * s pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* nonnegativity of both quadratic forms *)
  SUBGOAL_THEN `&0 <= w dot (p2c_vfam (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W t0 u y ** w) /\
                &0 <= w dot (p2c_vfam V W t0 t0 y ** w)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `t0 - s pow 2`; `t0:real`]
                  P2AP_REGION_UPTO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace(subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W)`
    ASSUME_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:A) IN W` THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[P3N_VBALL; mfd_ball; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_manifold_atlas (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W)
                    (restrict_atlas (rfs_vatlas V t0) W) /\
                  riemannian_metric (restrict_atlas (rfs_vatlas V t0) W) (p2c_vfam V W t0 u)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W`;
                     `t0 - s pow 2`; `t0:real`; `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W t0`; `u:real`]
                    P2AP_UPTO_RIEM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_manifold_atlas (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W)
                    (restrict_atlas (rfs_vatlas V t0) W) /\
                  riemannian_metric (restrict_atlas (rfs_vatlas V t0) W) (p2c_vfam V W t0 t0)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W`;
                     `t0 - s pow 2`; `t0:real`; `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W t0`; `t0:real`]
                    P2AP_UPTO_RIEM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
    EXISTS_TAC `subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W` THEN
    EXISTS_TAC `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `exp(&4 * inv(s pow 2) * (t0 - u)) *
                (w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) W t0 t0 y ** w))`;
    EXISTS_TAC `exp(&4 * inv(s pow 2) * (t0 - u)) *
                (w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) W t0 u y ** w))`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: arithmetic helpers and the                       *)
(* cross-slice geometry of an admissible parabolic region (comparison       *)
(* factor e^4): distances shrink at most by e^2 backwards, balls grow at    *)
(* most by e^2, volumes change by at most e^6.                              *)
(* ========================================================================= *)

let P3N_EXP2_SQ = prove
 (`exp(&2) pow 2 = exp(&4) /\ sqrt(exp(&4)) = exp(&2)`,
  SUBGOAL_THEN `exp(&2) pow 2 = exp(&4)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_EXP_POS_LE]);;

let P3N_INVSQRT_LOWER = prove
 (`!R s. &0 < R /\ &0 < s /\ R <= &9 * inv(s pow 2) ==> s / &3 <= inv(sqrt R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&9 * inv(s pow 2)) = &3 / s` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN
    SUBGOAL_THEN `&9 * inv(s pow 2) = (&3 * inv s) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt R <= &3 / s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s / &3 = inv(&3 / s)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT]);;

let P3N_PARAB_XGEOM = prove
 (`!(hs:(A)rfs_history) x0 t0 s t.
     rfs_history_ok hs /\ x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\
     p3n_adm (rfs_view hs) t0 x0 s /\ t0 - s pow 2 < t /\ t < t0
     ==> (!z r y. z IN rfs_vball (rfs_view hs) t0 x0 s /\ &0 < r /\
                  mfd_ball (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                           (rfs_vmetric (rfs_view hs) t0) z r
                  SUBSET rfs_vball (rfs_view hs) t0 x0 s /\
                  y IN mfd_ball (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                                (rfs_vmetric (rfs_view hs) t0) z r
                  ==> mfd_joinable (rfs_vtop (rfs_view hs) t,rfs_vatlas (rfs_view hs) t) z y /\
                      mfd_dist (rfs_vtop (rfs_view hs) t,rfs_vatlas (rfs_view hs) t)
                               (rfs_vmetric (rfs_view hs) t) z y <= exp(&2) * r) /\
         (!z r. z IN rfs_vball (rfs_view hs) t0 x0 s /\ &0 < r /\
                mfd_ball (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                         (rfs_vmetric (rfs_view hs) t0) z r
                SUBSET rfs_vball (rfs_view hs) t0 x0 s
                ==> mfd_ball (rfs_vtop (rfs_view hs) t,rfs_vatlas (rfs_view hs) t)
                             (rfs_vmetric (rfs_view hs) t) z (r / exp(&2)) SUBSET
                    mfd_ball (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                             (rfs_vmetric (rfs_view hs) t0) z r) /\
         (!S v1 v2. S SUBSET rfs_vball (rfs_view hs) t0 x0 s /\ ~(S = {}) /\
                    mfd_has_volume (rfs_vtop (rfs_view hs) t,rfs_vatlas (rfs_view hs) t)
                                   (rfs_vmetric (rfs_view hs) t) S v1 /\
                    mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                                   (rfs_vmetric (rfs_view hs) t0) S v2
                    ==> v1 <= exp(&6) * v2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `t:real`]
                P3N_PARAB_COMPARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `!t. compact_space (rfs_top_at (hs:(A)rfs_history) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2CW_HIST_COMPACT]; ALL_TAC] THEN
  UNDISCH_TAC `p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 s` THEN
  REWRITE_TAC[p3n_adm; rfs_parabolic_exists] THEN STRIP_TAC THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_space (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0)` ASSUME_TAC
  THENL [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  ABBREV_TAC `W = rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) t0 x0 s` THEN
  SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P3N_EXP2_SQ] THEN
  CONJ_TAC THENL
   [(* distances back in time *)
    MAP_EVERY X_GEN_TAC [`z:A`; `r:real`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN topspace(rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) /\
                  z IN topspace(rfs_vtop V t0) /\ open_in (rfs_vtop V t0) W /\
                  open_in (rfs_vtop V t) W`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists V (W:A->bool) (t0 - s pow 2) t0` THEN
      REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `t:real`) THEN FIRST_ASSUM(MP_TAC o SPEC `t0:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `t:real`; `z:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `t0:real`; `z:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_HC2_START_DIST THEN MAP_EVERY EXISTS_TAC [`W:A->bool`; `t0:real`] THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `t0 - s pow 2` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `W:A->bool`; `t0 - s pow 2`; `t0:real`]
                    P2C_REGULAR_VFLOW) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[p2c_vflow] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W`;
                     `t0 - s pow 2`; `t0:real`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W t0`; `t:real`] P2AP_UPTO_RIEM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`z':A`; `v:real^3`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `exp(&4)`)) (concl th))) THEN
      ASM_SIMP_TAC[P3N_EXP2_SQ]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* balls grow at most by e^2 forwards in time *)
    MAP_EVERY X_GEN_TAC [`z:A`; `r:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P3N_XBALL_IN THEN MAP_EVERY EXISTS_TAC [`W:A->bool`; `t0 - s pow 2`] THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `w:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `exp(&4)`)) (concl th))) THEN
    ASM_SIMP_TAC[P3N_EXP2_SQ];
    ALL_TAC] THEN
  (* volumes *)
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `t0 - s pow 2`; `t0:real`; `t:real`;
                 `S:A->bool`; `v1:real`; `v2:real`; `exp(&4)`] P3N_XVOL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `w:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `exp(&4)`)) (concl th))) THEN
    ASM_SIMP_TAC[P3N_EXP2_SQ];
    ALL_TAC] THEN
  REWRITE_TAC[P3N_EXP2_SQ; REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_ADD_CONV) THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: the tight case of KL Sublemma                    *)
(* 79.23 (b): a point (y,t) of P(x0,t0,s) with R(y,t) >= 4 C Rthr gives     *)
(* Vol B(x0,t0,s) >= kT s^3 (P3N_TIGHT_VOL).                               *)
(* ========================================================================= *)

(* the small-scale canonical data of P3N_CANONV_SMALL in a history view *)

let P3N_CANONV_SMALL_VIEW = prove
 (`?eps0. &0 < eps0 /\ eps0 <= &1 / &40 /\
     !C. &1 < C
       ==> ?c1 kap. &0 < c1 /\ c1 <= &1 /\ &0 < kap /\
             !(hs:(A)rfs_history) eps x t.
               rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ &0 < eps /\ eps <= eps0 /\
               &0 <= t /\ rfs_components_sc (rfs_vtop (rfs_view hs) t) /\
               x IN topspace(rfs_vtop (rfs_view hs) t) /\
               p3_canonv_at (rfs_view hs) C eps x t /\
               &8 * exp(&4) * C <= rfs_vscalar (rfs_view hs) t x
               ==> (!y. y IN rfs_vball (rfs_view hs) t x
                               (c1 * inv(sqrt(rfs_vscalar (rfs_view hs) t x)))
                        ==> rfs_vscalar (rfs_view hs) t x <=
                            &4 * C * rfs_vscalar (rfs_view hs) t y) /\
                   (!rho. &0 < rho /\ rho <= c1 * inv(sqrt(rfs_vscalar (rfs_view hs) t x))
                          ==> ?v. mfd_has_volume (rfs_vtop (rfs_view hs) t,
                                                  rfs_vatlas (rfs_view hs) t)
                                    (rfs_vmetric (rfs_view hs) t)
                                    (rfs_vball (rfs_view hs) t x rho) v /\
                                  kap * rho pow 3 <= v)`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "cs"))) (INST_TYPE [`:A`,`:A`] P3N_CANONV_SMALL) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `C:real` THEN DISCH_TAC THEN
  USE_THEN "cs" (MP_TAC o C MP (ASSUME `&1 < C`) o SPEC `C:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `K2:real` (X_CHOOSE_THEN `kap:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dat")))))))) THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `kap:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `eps:real`; `x:A`; `t:real`] THEN STRIP_TAC THEN
  USE_THEN "dat" (MP_TAC o ISPECL [`rfs_top_at (hs:(A)rfs_history)`; `rfs_atlas_at (hs:(A)rfs_history)`;
                                   `rfs_metric_at (hs:(A)rfs_history)`; `eps:real`; `x:A`; `t:real`]) THEN
  REWRITE_TAC[GSYM rfs_view] THEN
  UNDISCH_TAC `rfs_components_sc (rfs_vtop (rfs_view (hs:(A)rfs_history)) t)` THEN
  UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (rfs_view (hs:(A)rfs_history)) t)` THEN
  UNDISCH_TAC `&8 * exp(&4) * C <= rfs_vscalar (rfs_view (hs:(A)rfs_history)) t x` THEN
  REWRITE_TAC[P2C_RFS_VIEW_PARTS; P2C_VIEW_EXPAND] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
      REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN
        MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
        REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN SIMP_TAC[]];
      MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN
        MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
        REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN SIMP_TAC[]];
      MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN
        MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
        REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN SIMP_TAC[]];
      ASM_SIMP_TAC[P2CW_HIST_COMPACT];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `y:A`] P3N_PINCHED_AT) THEN
      ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[P3N_VBALL; P2C_RFS_VIEW_PARTS] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K2:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[P3N_VBALL; P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[]]);;

let P3N_TIGHT_VOL = prove
 (`?eps0. &0 < eps0 /\ eps0 <= &1 / &40 /\
     !C. &1 < C
       ==> ?kT. &0 < kT /\
             !(hs:(A)rfs_history) eps Rthr x0 t0 s t y.
               rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
               (!t. &0 <= t /\ t < rfs_horizon hs
                    ==> rfs_components_sc (rfs_vtop (rfs_view hs) t)) /\
               &0 < eps /\ eps <= eps0 /\ &8 * exp(&4) * C <= Rthr /\
               (!t y. &0 <= t /\ y IN topspace(rfs_vtop (rfs_view hs) t) /\
                      Rthr <= rfs_vscalar (rfs_view hs) t y
                      ==> p3_canonv_at (rfs_view hs) C eps y t) /\
               s pow 2 <= t0 /\ t0 < rfs_horizon hs /\
               x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\
               p3n_adm (rfs_view hs) t0 x0 s /\
               t0 - s pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 s /\
               &4 * C * Rthr <= rfs_vscalar (rfs_view hs) t y
               ==> ?v. mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                                      (rfs_vmetric (rfs_view hs) t0)
                                      (rfs_vball (rfs_view hs) t0 x0 s) v /\
                       kT * s pow 3 <= v`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "cv"))) (INST_TYPE [`:A`,`:A`] P3N_CANONV_SMALL_VIEW) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `C:real` THEN DISCH_TAC THEN
  USE_THEN "cv" (MP_TAC o C MP (ASSUME `&1 < C`) o SPEC `C:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `kap:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "dat")))))) THEN
  SUBGOAL_THEN `&0 < exp(&2) /\ &1 <= exp(&2) /\ &0 < exp(&4) /\ &0 < exp(&6) /\
                exp(&2) * exp(&2) = exp(&4)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_ADD] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&2` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `kap * (c1 / (&6 * exp(&4))) pow 3 / exp(&6)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `eps:real`; `Rthr:real`; `x0:A`; `t0:real`;
                       `s:real`; `t:real`; `y:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sc") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    STRIP_ASSUME_TAC))))))) THEN
  (* basic facts *)
  UNDISCH_TAC `p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 s` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[p3n_adm; rfs_parabolic_exists] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm"))) THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  ABBREV_TAC `W = rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) t0 x0 s` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ &0 <= t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) W /\
                open_in (rfs_vtop V t0) W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) (t0 - s pow 2) t0` THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `t0:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) /\ y IN topspace(rfs_vtop V t0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `y:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t0:real`; `y:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(s pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the scalar curvature on W at time t is at most 9 s^-2 *)
  SUBGOAL_THEN `!w:A. w IN W ==> rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t w <= &9 * inv(s pow 2)`
  (LABEL_TAC "r9") THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_rm_norm (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (rfs_vmetric V t) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
      MATCH_MP_TAC P3N_SCALAR_LE_RM THEN EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      USE_THEN "rm" (MP_TAC o SPECL [`t:real`; `w:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* Rthr facts *)
  SUBGOAL_THEN `&0 < Rthr /\ Rthr <= &4 * C * Rthr /\ &0 < &4 * C` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < exp(&4) * C` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Rthr` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&1 * Rthr <= (&4 * C) * Rthr` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* canonical data at (y,t) *)
  USE_THEN "dat" (MP_TAC o SPECL [`hs:(A)rfs_history`; `eps:real`; `y:A`; `t:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "sc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ry") (K ALL_TAC)) THEN
  (* the inward point *)
  ABBREV_TAC `rho = (c1 * s) / (&12 * exp(&2))` THEN
  SUBGOAL_THEN `&0 < rho /\ &2 * rho <= s /\ exp(&2) * (&2 * rho) = c1 * s / &6`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&2 * rho = (c1 / (&6 * exp(&2))) * s` SUBST1_TAC THENL
       [EXPAND_TAC "rho" THEN UNDISCH_TAC `&0 < exp(&2)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < &6 * x`] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "rho" THEN UNDISCH_TAC `&0 < exp(&2)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `x0:A`; `y:A`; `s:real`; `rho:real`]
                P3N_INWARD_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:A) IN W` THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[P3N_VBALL];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P3N_VBALL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "ry" (LABEL_TAC "ry" o REWRITE_RULE[ASSUME `rfs_view (hs:(A)rfs_history) = (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`]) THEN
  (* bounds at y *)
  SUBGOAL_THEN `&0 < rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t y /\ s / &3 <= inv(sqrt(rfs_vscalar V t y))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t y` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3N_INVSQRT_LOWER THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "r9" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c1 * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* z is close to y at time t *)
  SUBGOAL_THEN `mfd_joinable (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t,rfs_vatlas V t) z y /\
                mfd_dist (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) z y <=
                exp(&2) * (&2 * rho)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `t:real = t0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `(y:A) IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z (&2 * rho)` THEN
      REWRITE_TAC[P3N_VBALL; mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 * (&2 * rho) <= exp(&2) * (&2 * rho)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `t:real`]
                  P3N_PARAB_XGEOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`z:A`; `&2 * rho`; `y:A`] o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM P3N_VBALL] THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t y (c1 * inv(sqrt(rfs_vscalar V t y)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P3N_VBALL; mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `y:A`; `z:A`]
                    MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `y:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `c1 * s / &3 <= c1 * inv(sqrt(rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t y))` MP_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[GSYM real_div] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the inward point is hot enough for its own canonical neighbourhood *)
  SUBGOAL_THEN `Rthr <= rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t z` ASSUME_TAC THENL
   [USE_THEN "ry" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(&4 * C) * Rthr <= (&4 * C) * rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t z` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  (* z lies in the slice at t and has small-scale data *)
  SUBGOAL_THEN `(z:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) /\ z IN topspace(rfs_vtop V t0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  USE_THEN "dat" (MP_TAC o SPECL [`hs:(A)rfs_history`; `eps:real`; `z:A`; `t:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "sc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the small radius *)
  ABBREV_TAC `rh = &2 * rho / exp(&2)` THEN
  SUBGOAL_THEN `&0 < rh /\ rh <= &2 * rho /\ exp(&2) * rh = &2 * rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rh" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&2 * r / e = (&2 * r) / e`] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&2 * r / e = (&2 * r) / e`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `(&2 * rho) * &1 <= (&2 * rho) * exp(&2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      UNDISCH_TAC `&0 < exp(&2)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `rh <= c1 * inv(sqrt(rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t z))` ASSUME_TAC THENL
   [SUBGOAL_THEN `s / &3 <= inv(sqrt(rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t z))` ASSUME_TAC THENL
     [MATCH_MP_TAC P3N_INVSQRT_LOWER THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; USE_THEN "r9" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1 * s / &3` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `rh = (c1 * s / &6) / exp(&2) pow 2` SUBST1_TAC THENL
       [EXPAND_TAC "rh" THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `exp(&2) * &2 * rho = c1 * s / &6`)) THEN
        UNDISCH_TAC `&0 < exp(&2)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= exp(&2) pow 2` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[GSYM(REAL_RAT_REDUCE_CONV `&1 pow 2`)] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < exp(&2) pow 2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `(c1 * s / &3) * &1 <= (c1 * s / &3) * exp(&2) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[GSYM real_div] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rh:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `kap:real`)) (concl th) &&
    not (can (find_term (fun t -> t = `hs:(A)rfs_history`)) (concl th)) = false ||
    (is_forall(concl th) && can (find_term (fun t -> t = `kap:real`)) (concl th) &&
     can (find_term (fun t -> t = `z:A`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Sb = rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t z rh` THEN
  (* the small ball lies in W *)
  SUBGOAL_THEN `(Sb:A->bool) SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z (&2 * rho)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Sb" THEN
    ASM_CASES_TAC `t:real = t0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[P3N_VBALL] THEN
      MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `t:real`]
                  P3N_PARAB_XGEOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`z:A`; `&2 * rho`] o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM P3N_VBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * rho) / exp(&2) = rh` SUBST1_TAC THENL
     [EXPAND_TAC "rh" THEN REAL_ARITH_TAC; EXPAND_TAC "Sb" THEN REWRITE_TAC[P3N_VBALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN Sb` ASSUME_TAC THENL
   [EXPAND_TAC "Sb" THEN REWRITE_TAC[P3N_VBALL; mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL];
    ALL_TAC] THEN
  (* the volume of the small ball at t0 *)
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) Sb` ASSUME_TAC THENL
   [SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) Sb` ASSUME_TAC THENL
     [EXPAND_TAC "Sb" THEN REWRITE_TAC[P3N_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real = t0` THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) W = subtopology (rfs_vtop V t0) W`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P3N_REGION_SUBTOP THEN EXISTS_TAC `t0 - s pow 2` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0) W) Sb` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
      ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `x0:A`; `s:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN ASM_SIMP_TAC[P2C_RFS_VIEW_PARTS; P2CW_HIST_COMPACT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P3N_VBALL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real`) THEN EXISTS_TAC `v0:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `Sb:A->bool`; `W:A->bool`; `v0:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v2 = mfd_volume (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0,rfs_vatlas V t0) (rfs_vmetric V t0) Sb` THEN
  STRIP_TAC THEN
  (* v1 <= e^6 v2 *)
  SUBGOAL_THEN `v1 <= exp(&6) * v2` ASSUME_TAC THENL
   [ASM_CASES_TAC `t:real = t0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `v1:real = v2` SUBST1_TAC THENL
       [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_UNIQUE) THEN
        MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                              `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `Sb:A->bool`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= v2 /\ &1 <= exp(&6)` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_POS_LE) THEN
          MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                                `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`; `Sb:A->bool`] THEN
          ASM_REWRITE_TAC[];
          MP_TAC(SPEC `&6` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 * v2 <= exp(&6) * v2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `t:real`]
                  P3N_PARAB_XGEOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`Sb:A->bool`; `v1:real`; `v2:real`] o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the arithmetic of the constant *)
  SUBGOAL_THEN `(kap * (c1 / (&6 * exp(&4))) pow 3 / exp(&6)) * s pow 3 =
                (kap * rh pow 3) / exp(&6)` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rh"; "rho"] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `exp(&2) * exp(&2) = exp(&4)`)) THEN
    UNDISCH_TAC `&0 < exp(&2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `exp(&6) * v2 <= exp(&6) * v0` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.1, small scales: the assembly.  KL Sublemma 79.23 in the form     *)
(* of the statement of pc_p3_s16sst: from the maximal admissible scale       *)
(* s in [r0,rr] (P3N_MAXSCALE): if s = rr the large-scale bound at rr steps *)
(* down to r0; otherwise P3N_TIGHT_EXISTS gives a hot point and             *)
(* P3N_TIGHT_VOL a volume bound at s, which steps down to r0.               *)
(* ========================================================================= *)

let P3N_ADM_STEPDOWN = prove
 (`!(hs:(A)rfs_history) x0 t0 s r0 k v.
     rfs_history_ok hs /\ x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\
     p3n_adm (rfs_view hs) t0 x0 s /\ &0 < r0 /\ r0 <= s /\
     mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                    (rfs_vmetric (rfs_view hs) t0) (rfs_vball (rfs_view hs) t0 x0 s) v /\
     k * s pow 3 <= v
     ==> ?v'. mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                             (rfs_vmetric (rfs_view hs) t0) (rfs_vball (rfs_view hs) t0 x0 r0) v' /\
              k / &2 * r0 pow 3 <= v'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = rfs_view (hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact_space (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0)` ASSUME_TAC
  THENL [EXPAND_TAC "V" THEN ASM_SIMP_TAC[P2C_RFS_VIEW_PARTS; P2CW_HIST_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t0`; `rfs_vatlas (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t0`; `x0:A`; `r0:real`]
                MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v':real`) THEN
  EXISTS_TAC `v':real` THEN ASM_REWRITE_TAC[P3N_VBALL] THEN
  MATCH_MP_TAC P3N_BG_STEPDOWN THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t0`;
                        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t0`;
                        `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t0`;
                        `x0:A`; `s:real`; `v:real`] THEN
  REWRITE_TAC[GSYM P3N_VBALL] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[P3N_VBALL] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ASSUME `p3n_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) t0 x0 s`) THEN
    REWRITE_TAC[p3n_adm; P3N_VBALL] THEN DISCH_THEN(MP_TAC o SPECL [`t0:real`; `y:A`] o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPECL [`s:real`; `2`] REAL_POW_LT) THEN ANTS_TAC THENL
     [MP_TAC(ASSUME `p3n_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) t0 x0 s`) THEN
      REWRITE_TAC[p3n_adm] THEN SIMP_TAC[];
      REAL_ARITH_TAC]]);;

(* KL Sublemma 79.23, unpackaged (P3N_SMALL_SCALE below packages it) *)

let P3N_SMALL_SCALE_RAW = prove
 (`?eps0. &0 < eps0 /\
     !C. &1 < C
       ==> ?Lam kS. &1 <= Lam /\ &0 < kS /\
             !(hs:(A)rfs_history) eps Rthr rr kL x0 t0 r0.
               rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
               (!t. &0 <= t /\ t < rfs_horizon hs
                    ==> rfs_components_sc (rfs_vtop (rfs_view hs) t)) /\
               &0 < eps /\ eps <= eps0 /\ &8 * exp(&4) * C <= Rthr /\
               Lam * Rthr <= inv(rr pow 2) /\
               (!t y. &0 <= t /\ y IN topspace(rfs_vtop (rfs_view hs) t) /\
                      Rthr <= rfs_vscalar (rfs_view hs) t y
                      ==> p3_canonv_at (rfs_view hs) C eps y t) /\
               (!k i c. 1 <= k /\ k <= hs_count hs /\
                        t0 - rr pow 2 <= hs_time hs k /\ hs_time hs k <= t0 /\
                        i IN ev_index(hs_event hs k) /\
                        c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
                        ==> Lam * Rthr <= rfs_vscalar (rfs_view hs) (hs_time hs k) c) /\
               &0 < kL /\ rr pow 2 <= t0 /\ t0 < rfs_horizon hs /\
               x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\ &0 < r0 /\ r0 <= rr /\
               rfs_parabolic_exists (rfs_view hs) t0 x0 r0 (r0 pow 2) /\
               (!t y. t0 - r0 pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 r0
                      ==> mfd_rm_norm (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t) y
                          <= inv(r0 pow 2)) /\
               (rfs_parabolic_exists (rfs_view hs) t0 x0 rr (rr pow 2) /\
                (!t y. t0 - rr pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 rr
                       ==> mfd_rm_norm (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t) y
                           <= inv(rr pow 2))
                ==> ?v. mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                                       (rfs_vmetric (rfs_view hs) t0)
                                       (rfs_vball (rfs_view hs) t0 x0 rr) v /\
                        kL * rr pow 3 <= v)
               ==> ?v. mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                                      (rfs_vmetric (rfs_view hs) t0)
                                      (rfs_vball (rfs_view hs) t0 x0 r0) v /\
                       min (kL / &2) kS * r0 pow 3 <= v`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "tv"))) (INST_TYPE [`:A`,`:A`] P3N_TIGHT_VOL) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `C:real` THEN DISCH_TAC THEN
  USE_THEN "tv" (MP_TAC o C MP (ASSUME `&1 < C`) o SPEC `C:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `kT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tvC"))) THEN
  MAP_EVERY EXISTS_TAC [`&64 * C`; `kT / &2`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `eps:real`; `Rthr:real`; `rr:real`; `kL:real`;
                       `x0:A`; `t0:real`; `r0:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sc") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (CONJUNCTS_THEN2 (LABEL_TAC "hot") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "large")))))))))))))))))) THEN
  SUBGOAL_THEN `&0 < Rthr /\ &0 < C * Rthr` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < exp(&4) * C` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Rthr` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 r0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p3n_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`; `x0:A`; `r0:real`; `rr:real`] P3N_MAXSCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r0 pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "disj"))))) THEN
  ASM_CASES_TAC `s:real = rr` THENL
   [(* case (c): s = rr, the large-scale bound steps down *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "large" MP_TAC THEN ANTS_TAC THENL
     [UNDISCH_TAC `p3n_adm (rfs_view (hs:(A)rfs_history)) t0 x0 rr` THEN
      REWRITE_TAC[p3n_adm] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `rr:real`; `r0:real`; `kL:real`;
                   `v:real`] P3N_ADM_STEPDOWN) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v':real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `kL / &2 * r0 pow 3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* cases (a) and (b): a hot point, then the tight volume bound *)
  REMOVE_THEN "disj" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max") THEN
  SUBGOAL_THEN `s < rr` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Rthr <= C * Rthr` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 * Rthr <= C * Rthr` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * exp(&4) <= inv(rr pow 2) /\ &0 < &64 * C * Rthr` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 < exp(&4) * C /\ exp(&4) * &1 <= exp(&4) * C` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `rr:real`;
                 `&64 * C * Rthr`] P3N_TIGHT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "hot" (ACCEPT_TAC o REWRITE_RULE[GSYM REAL_MUL_ASSOC])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
  USE_THEN "tvC" (MP_TAC o SPECL [`hs:(A)rfs_history`; `eps:real`; `Rthr:real`; `x0:A`;
                                  `t0:real`; `s:real`; `t:real`; `y:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `s pow 2 <= rr pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `x0:A`; `t0:real`; `s:real`; `r0:real`; `kT:real`;
                 `v:real`] P3N_ADM_STEPDOWN) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v':real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `kT / &2 * r0 pow 3` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.1, small scales: the main theorem P3N_SMALL_SCALE in the          *)
(* statement form of unit pc_p3_s16sst.                                      *)
(* ========================================================================= *)

let P3N_SMALL_SCALE = prove
 (`!u:A->bool. P3N_SMALL_SCALE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3N_SMALL_SCALE_STATEMENT] THEN
  ACCEPT_TAC(INST_TYPE [`:A`,`:A`] P3N_SMALL_SCALE_RAW));;

