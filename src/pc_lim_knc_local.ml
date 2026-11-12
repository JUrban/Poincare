(* ========================================================================= *)
(* The local form of L4 of the limit-geometry layer (kappa-noncollapsing     *)
(* passes to the limit).  LIM_KNC (pc_lim_vol) asks every approximant to be  *)
(* kappa-noncollapsed everywhere on scales r0 / sqrt(Q k); blow-up sequences *)
(* give p3_noncoll_at only near the base points.  P2BU_KNC_LOCAL asks, for   *)
(* each limit point (tt,xx), noncollapsing of V k at                         *)
(* (phi k xx, t k + tt / Q k) for all large k.  The blow-ups of MT 17.1 use  *)
(* the same form.                                                            *)
(* ========================================================================= *)

needs "src/pc_lim_vol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* P2BU_NONCOLL_AT_VIEW (p3_noncoll_at in the form of LIM_KNC_VIEW at one    *)
(* point), P2BU_NONCOLL_AT_MONO, and the adapted P2BU_KNC_APPROX_LOCAL and   *)
(* P2BU_KNC_LOCAL.                                                           *)
(* ========================================================================= *)

(* p3_noncoll_at at one point (x,t), in the form of LIM_KNC_VIEW.           *)

let P2BU_NONCOLL_AT_VIEW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    kappa r0 x t.
     p3_noncoll_at V kappa r0 x t <=>
     !r. &0 < r /\ r <= r0 /\
         (!s. t - r pow 2 < s /\ s <= t
              ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                  open_in (rfs_vtop V s)
                    (mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r)) /\
         (!s y. t - r pow 2 < s /\ s <= t /\
                y IN mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r
                ==> mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) y <= inv(r pow 2))
         ==> ?v. mfd_has_volume (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t)
                   (mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r) v /\
                 kappa * r pow 3 <= v`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[P2BL_VIEW_TRIPLE] THEN
  REWRITE_TAC[p3_noncoll_at; rfs_parabolic_exists; rfs_persists; rfs_vball;
              rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* Noncollapsing on scales <= r0 gives it on scales <= r1 for r1 <= r0.    *)

let P2BU_NONCOLL_AT_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    kappa r0 r1 x t.
     p3_noncoll_at V kappa r0 x t /\ r1 <= r0 ==> p3_noncoll_at V kappa r1 x t`,
  REWRITE_TAC[p3_noncoll_at] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Adapted from LIM_KNC_APPROX (pc_lim_vol): the global noncollapsing of     *)
(* every V k is replaced by noncollapsing of V k at (phi k xx, t k + tt / Q  *)
(* k) for k >= k1, the only point the proof uses; the index k gets the extra *)
(* summand k1.  Otherwise the proof is that of LIM_KNC_APPROX.               *)

let P2BU_KNC_APPROX_LOCAL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi kappa r0 tt xx r r' d.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k tau. hausdorff_space (rfs_vtop (V k) tau)) /\
     (!s. s IN J ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)) /\
     (?k1. !k. k1 <= k
               ==> p3_noncoll_at (V k) kappa (r0 * inv(sqrt(Q k))) (phi k xx)
                     (t k + tt / Q k)) /\
     tt IN J /\ xx IN topspace top /\ &0 <= kappa /\ &0 < r' /\ r' < r /\ r <= r0 /\
     &0 < d /\ d <= &1 / &2 /\
     (!s. tt - r pow 2 < s /\ s <= tt ==> s IN J) /\
     (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN mfd_ball (top,atlas) (g tt) xx r
            ==> mfd_rm_norm atlas (g s) y <= inv(r pow 2))
     ==> kappa * r' pow 3 <=
         (&1 + &3 * d) * mfd_volume (top,atlas) (g tt) (mfd_ball (top,atlas) (g tt) xx r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) tt) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r'' = (r' + r) / &2` THEN
  SUBGOAL_THEN `r' < r'' /\ r'' < r /\ &0 < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r''" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r' pow 2 < r pow 2 /\ &0 < r' pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  ABBREV_TAC `alpha = inv(r' pow 2) - inv(r pow 2)` THEN
  SUBGOAL_THEN `&0 < alpha` ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[tt - r' pow 2,tt] SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Kb = mfd_cball (top,atlas) ((g:real->B->real^3^3) tt) xx r''` THEN
  ABBREV_TAC `Kq = mfd_cball (top,atlas) ((g:real->B->real^3^3) tt) xx (r + &1)` THEN
  SUBGOAL_THEN `compact_in top (Kb:B->bool) /\ compact_in top (Kq:B->bool) /\ Kb SUBSET Kq /\
                Kb SUBSET mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r /\
                mfd_ball (top,atlas) (g tt) xx r SUBSET Kq`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kb"; "Kq"] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_cball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the view curvature bound on [tt - r'^2, tt] over Kb *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `tt - r' pow 2`; `tt:real`; `Kb:B->bool`;
                 `inv(r pow 2)`; `alpha:real`] LIM_VIEW_RM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(s:real) IN J` (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tt - r pow 2`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm"))
                            (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `z:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm atlas ((g:real->B->real^3^3) s) z` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(s:real) IN J` (fun th -> ASM_SIMP_TAC[th]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th) &&
        can (find_term ((=) `inv(r pow 2)`)) (concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `kb:num` (LABEL_TAC "rmb"))] THEN
  (* the view ball inside the image of B(xx,r'') *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `tt:real`; `xx:B`; `r':real`; `r'':real`]
                LIM_BALL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:num` (LABEL_TAC "bin")) THEN
  (* closeness on Kq at time tt *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `tt:real`; `tt:real`; `Kq:B->bool`;
                 `d:real`] LIM_QF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s' = tt:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:num` (LABEL_TAC "qf0")) THEN
  (* the diffeomorphisms at all times of [tt - r'^2, tt] *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt - r' pow 2`; `tt:real`; `Kq:B->bool`; `0`; `&1`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kd:num` (LABEL_TAC "dif")) THEN
  ABBREV_TAC `k = ka + kb + kc + kd + k1:num` THEN
  USE_THEN "qf0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `tt:real`)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi0:A->B`) (LABEL_TAC "qfk")))) THEN
  USE_THEN "dif" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "difk") (K ALL_TAC))) THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`(Q:num->real) k`; `r':real`] LIM_RHO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `rho = r' * inv(sqrt((Q:num->real) k))` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= r0 * inv(sqrt((Q:num->real) k))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN
    SUBGOAL_THEN `&0 < inv(sqrt((Q:num->real) k))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `VT0 = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + tt / Q k)` THEN
  ABBREV_TAC `VA0 = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + tt / Q k)` THEN
  ABBREV_TAC `VG0 = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + tt / Q k)` THEN
  ABBREV_TAC `Bk = mfd_ball (VT0:A topology,VA0:((A->bool)#(A->real^3))->bool)
                            (VG0:A->real^3^3) ((phi:num->B->A) k xx) rho` THEN
  SUBGOAL_THEN `!z:A. z IN Bk
                      ==> z IN IMAGE ((phi:num->B->A) k)
                                (mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r'' INTER
                                 W k)` (LABEL_TAC "bink") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "bin" MATCH_MP_TAC THEN
    CONJ_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["VT0"; "VA0"; "VG0"; "Bk"; "rho"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Bk:A->bool) SUBSET IMAGE ((phi:num->B->A) k) (W k) /\
                (phi:num->B->A) k xx IN topspace (VT0:A topology) /\
                hausdorff_space (VT0:A topology)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      USE_THEN "bink" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN Bk`)) THEN SET_TAC[];
      UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                     ((W:num->B->bool) k) (VT0:A topology) (VA0:((A->bool)#(A->real^3))->bool)
                     (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psi0:A->B)` THEN
      REWRITE_TAC[mfd_diffeo] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
      SUBGOAL_THEN `(xx:B) IN W(k:num)` MP_TAC THENL
       [SUBGOAL_THEN `(xx:B) IN Kq` MP_TAC THENL
         [EXPAND_TAC "Kq" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
          ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]];
        SET_TAC[]];
      EXPAND_TAC "VT0" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (VT0:A topology) Bk` ASSUME_TAC THENL
   [EXPAND_TAC "Bk" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* times in (t' - rho^2, t'] are t k + s / Q k with s in (tt - r'^2, tt] *)
  SUBGOAL_THEN
   `!sg. (t k + tt / Q k) - rho pow 2 < sg /\ sg <= t k + tt / Q k
         ==> ?s. tt - r' pow 2 < s /\ s <= tt /\ sg = t k + s / (Q:num->real) k`
  (LABEL_TAC "tch") THENL
   [X_GEN_TAC `sg:real` THEN STRIP_TAC THEN MATCH_MP_TAC LIM_TIME_CHANGE THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t k + (tt - r' pow 2) / (Q:num->real) k = (t k + tt / Q k) - rho pow 2`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < (Q:num->real) k` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* noncollapsing of V k at (t k + tt / Q k, phi k xx, rho) *)
  (* (adapted) the local noncollapsing hypothesis at k1 <= k *)
  SUBGOAL_THEN `k1 <= k:num` ASSUME_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `k1 <= k:num`) o SPEC `k:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_noncoll_at"))
        (concl th))) THEN
  REWRITE_TAC[P2BU_NONCOLL_AT_VIEW] THEN
  DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `sg:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "tch" (MP_TAC o C MATCH_MP (ASSUME
        `(t k + tt / (Q:num->real) k) - rho pow 2 < sg /\ sg <= t k + tt / Q k`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "difk" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `psis:A->B`) THEN
      SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                      (t k + s / Q k)) (rfs_vatlas (V k) (t k + s / Q k))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `t k + s / (Q:num->real) k`] o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric"))
              (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_vtop")) (concl th))) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) k xx` THEN
        UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                       ((W:num->B->bool) k)
                       (rfs_vtop ((V:num->(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                         (t k + s / Q k))
                       (rfs_vatlas (V k) (t k + s / Q k))
                       (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psis:A->B)` THEN
        REWRITE_TAC[mfd_diffeo] THEN
        DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
        SUBGOAL_THEN `(phi:num->B->A) k xx IN IMAGE (phi k) (W k)` MP_TAC THENL
         [UNDISCH_TAC `(phi:num->B->A) k xx IN topspace (VT0:A topology)` THEN
          UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                         ((W:num->B->bool) k) (VT0:A topology)
                         (VA0:((A->bool)#(A->real^3))->bool)
                         (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psi0:A->B)` THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN
          SUBGOAL_THEN `(xx:B) IN Kq` MP_TAC THENL
           [EXPAND_TAC "Kq" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
            ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
            ASM SET_TAC[]];
          SET_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(W:num->B->bool) k`; `VT0:A topology`;
                     `VA0:((A->bool)#(A->real^3))->bool`;
                     `IMAGE ((phi:num->B->A) k) (W k)`;
                     `rfs_vtop ((V:num->(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                       (t k + s / Q k)`;
                     `rfs_vatlas ((V:num->(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                       (t k + s / Q k)`;
                     `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`;
                     `psi0:A->B`; `psis:A->B`; `Bk:A->bool`] LIM_DIFFEO_OPEN_TRANSFER) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`sg:real`; `y':A`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y':A) IN Bk` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["Bk"; "VT0"; "VA0"; "VG0"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "tch" (MP_TAC o C MATCH_MP (CONJ (ASSUME
      `(t k + tt / (Q:num->real) k) - rho pow 2 < sg`) (ASSUME `sg <= t k + tt / (Q:num->real) k`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "bink" (MP_TAC o C MATCH_MP (ASSUME `(y':A) IN Bk`)) THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Q:num->real) k * (inv(r pow 2) + alpha)` THEN CONJ_TAC THENL
     [USE_THEN "rmb" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "k" THEN ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Kb" THEN
        UNDISCH_TAC `(z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r''` THEN
        REWRITE_TAC[mfd_ball; mfd_cball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "alpha" THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vk:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `P = mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r INTER
                  {z | z IN W(k:num) /\ (phi:num->B->A) k z IN Bk}` THEN
  SUBGOAL_THEN `open_in top (P:B->bool) /\ P SUBSET W(k:num) /\ P SUBSET Kq /\
                P SUBSET mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r /\
                IMAGE ((phi:num->B->A) k) P = Bk`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `VT0:A topology`; `VA0:((A->bool)#(A->real^3))->bool`;
                     `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                     `(phi:num->B->A) k`; `psi0:A->B`; `Bk:A->bool`]
                    LIM_DIFFEO_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "P" THEN SET_TAC[];
      EXPAND_TAC "P" THEN ASM SET_TAC[];
      EXPAND_TAC "P" THEN SET_TAC[];
      EXPAND_TAC "P" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `w:A` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      USE_THEN "bink" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN Bk`)) THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN EXISTS_TAC `z:B` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r''` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(w:A) IN Bk` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`; `P:B->bool`; `Kq:B->bool`] LIM_OPEN_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`;
                 `mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r`; `Kq:B->bool`]
                LIM_OPEN_VOLUME) THEN
  ASM_SIMP_TAC[MFD_BALL_OPEN] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`; `VT0:A topology`;
                 `VA0:((A->bool)#(A->real^3))->bool`; `VG0:A->real^3^3`; `(W:num->B->bool) k`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi0:A->B`;
                 `P:B->bool`; `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) P`;
                 `vk:real`; `(Q:num->real) k`; `d:real`] LIM_VOL_IMAGE_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MAP_EVERY X_GEN_TAC [`z:B`; `w:real^3`] THEN DISCH_TAC THEN
    USE_THEN "qfk" (MP_TAC o SPECL [`z:B`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`; `P:B->bool`;
                 `mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r`;
                 `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) P`;
                 `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt)
                    (mfd_ball (top,atlas) (g tt) xx r)`] MFD_HAS_VOLUME_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k * sqrt(Q k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `kappa * r' pow 3 <= (Q:num->real) k * sqrt(Q k) * vk` ASSUME_TAC THENL
   [UNDISCH_TAC `(Q:num->real) k * sqrt(Q k) * rho pow 3 = r' pow 3` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(kappa * ((Q:num->real) k * sqrt(Q k) * rho pow 3) =
                   (Q k * sqrt(Q k)) * (kappa * rho pow 3)) /\
                  ((Q:num->real) k * sqrt(Q k) * vk = (Q k * sqrt(Q k)) * vk)`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + &3 * d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + &3 * d) * mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) P` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Adapted from LIM_KNC (pc_lim_vol): kappa-noncollapsing on scales <= r0   *)
(* passes to the limit from noncollapsing of the approximants near the      *)
(* images of the limit points (P2BU_KNC_APPROX_LOCAL).  Otherwise the proof *)
(* is that of LIM_KNC.                                                      *)

let P2BU_KNC_LOCAL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (x:num->A) t Q J (top:B topology) atlas g (xl:B)
     W phi kappa r0.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k tau. hausdorff_space (rfs_vtop (V k) tau)) /\
     (!s. s IN J ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)) /\
     (!tt xx. tt IN J /\ xx IN topspace top
              ==> ?k1. !k. k1 <= k
                           ==> p3_noncoll_at (V k) kappa (r0 * inv(sqrt(Q k))) (phi k xx)
                                 (t k + tt / Q k))
     ==> rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) J g) kappa r0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  REWRITE_TAC[rfs_flow_view; rfs_kappa_noncollapsed; rfs_parabolic_exists; rfs_persists;
              rfs_vball] THEN
  MAP_EVERY X_GEN_TAC [`tt:real`; `xx:B`; `r:real`] THEN
  ASM_CASES_TAC `(tt:real) IN J` THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) tt) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(xx:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. tt - r pow 2 < s /\ s <= tt ==> s IN J` (LABEL_TAC "inJ") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bl = mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r` THEN
  SUBGOAL_THEN `mfd_has_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl
                  (mfd_volume (top,atlas) (g tt) Bl)` ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN
    EXISTS_TAC `mfd_cball (top,atlas) ((g:real->B->real^3^3) tt) xx (r + &1)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Bl" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Bl" THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `x < r ==> x <= r + &1`]];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) tt`; `Bl:B->bool`;
                   `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl`]
                  MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `kappa <= &0` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `k * p <= &0 <=> &0 <= --k * p`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_LE_LIMIT THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl / &2 + kappa * r pow 3` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  (* (adapted) the local noncollapsing hypothesis at (tt,xx) *)
  SUBGOAL_THEN `?k1. !k. k1 <= k
                         ==> p3_noncoll_at ((V:num->(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                               kappa (r0 * inv(sqrt((Q:num->real) k)))
                               ((phi:num->B->A) k xx) ((t:num->real) k + tt / Q k)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_noncoll_at"))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `kappa:real`; `r0:real`; `tt:real`; `xx:B`;
                 `r:real`; `r * (&1 - h / &4)`; `h / &6`] P2BU_KNC_APPROX_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < r /\ &0 < r * h / &4 ==> r * (&1 - h / &4) < r`) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `h:real` LIM_CUBE_LOWER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `kappa * r pow 3 * (&1 - &3 * h / &4) <=
                kappa * (r * (&1 - h / &4)) pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `k * p * c = (k * p) * c:real`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kappa * r pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &3 * h / &6) * mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl =
                mfd_volume (top,atlas) (g tt) Bl +
                (mfd_volume (top,atlas) (g tt) Bl / &2) * h` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `kappa * r pow 3 * (&1 - &3 * h / &4) =
                kappa * r pow 3 - (&3 / &4) * (kappa * r pow 3) * h` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &4) * (kappa * r pow 3) * h <= (kappa * r pow 3) * h` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `(&3 / &4) * a * h = (&3 / &4) * (a * h)`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> (&3 / &4) * x <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

