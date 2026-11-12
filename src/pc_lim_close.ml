(* ========================================================================= *)
(* Metric closeness, the exit argument and ball inclusions for flow limits   *)
(* p2c_flow_limit_with (pc_p3_iface).  The rescaled pullback metrics of the  *)
(* views by phi k are uniformly close to the limit metric on compact sets as *)
(* quadratic forms (LIM_QF_CLOSE); short curves stay in images of balls      *)
(* (LIM_CURVES_STAY); view balls about phi k y lie in images of slightly     *)
(* larger limit balls (LIM_BALL_IN) and images of limit balls lie in         *)
(* slightly larger view balls (LIM_BALL_OUT).  Built on pc_p2b_cap           *)
(* (P2BC_BALL_IMAGE_IN, P2BC_BALL_PREIMAGE_IN), pc_p2b_ltr, pc_p2b_979s and  *)
(* the distance unit pc_grg_dist_in.                                         *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_p2b_cap.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_p2b_979.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_grg_dist_in.ml";;

prioritize_real();;
type_invention_error := true;;
(* Closeness of the rescaled pullback metrics to the limit metric on a      *)
(* compact set, uniformly on a time interval, as quadratic forms.           *)

let LIM_QF_CLOSE = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi a b K d.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     real_interval[a,b] SUBSET J /\
     (!s. a <= s /\ s <= b ==> riemannian_metric atlas (g s)) /\
     compact_in top K /\ &0 < d
     ==> ?k0. !k. k0 <= k
            ==> K SUBSET W k /\
                !s. a <= s /\ s <= b
                    ==> smooth_manifold_atlas (rfs_vtop (V k) (t k + s / Q k))
                                              (rfs_vatlas (V k) (t k + s / Q k)) /\
                        riemannian_metric (rfs_vatlas (V k) (t k + s / Q k))
                                          (rfs_vmetric (V k) (t k + s / Q k)) /\
                        (?psi. mfd_diffeo top atlas (W k)
                                 (rfs_vtop (V k) (t k + s / Q k))
                                 (rfs_vatlas (V k) (t k + s / Q k))
                                 (IMAGE (phi k) (W k)) (phi k) psi) /\
                        !y v. y IN K
                              ==> abs(Q k * (v dot (mfd_pullback_metric atlas
                                                      (rfs_vatlas (V k) (t k + s / Q k))
                                                      (phi k)
                                                      (rfs_vmetric (V k) (t k + s / Q k)) y ** v)) -
                                      v dot (g s y ** v))
                                  <= d * (v dot (g s y ** v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `0`; `d pow 2 / &2`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "pt"))) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "dif" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  SUBGOAL_THEN `smooth_manifold_atlas (VT:A topology) VA /\ riemannian_metric VA (VG:A->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["VT"; "VA"; "VG"] THEN USE_THEN "reg" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) k xl` THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (VT:A topology) (VA:((A->bool)#(A->real^3))->bool)
                   (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psi:A->B)` THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [EXISTS_TAC `psi:A->B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `v:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN W(k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 0 (metric_local atlas (chart_at atlas (y:B)) (\z. &1 %% (g:real->B->real^3^3) s z))
      (metric_local atlas (chart_at atlas y)
         (\z. &1 %% mfd_pullback_metric atlas (VA:((A->bool)#(A->real^3))->bool)
                      ((phi:num->B->A) k) (\z. (Q:num->real) k %% (VG:A->real^3^3) z) z))
      (SND(chart_at atlas y) y) <= d pow 2 / &2`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2B9_PULLBACK_METRIC_CMUL; MATRIX_CMUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv(&1)) pow 0 *
                lck_dist2 0 (metric_local atlas (chart_at atlas (y:B)) ((g:real->B->real^3^3) s))
                  (\z. (Q:num->real) k %%
                       rfs_pullback (VA:((A->bool)#(A->real^3))->bool)
                         ((phi:num->B->A) k o chart_inv (chart_at atlas y)) (VG:A->real^3^3) z)
                  (SND(chart_at atlas y) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BL_LCK_CHART_CONVERT THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `VT:A topology`; `(W:num->B->bool) k`;
                            `IMAGE ((phi:num->B->A) k) (W k)`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      ALL_TAC] THEN
    REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "pt" (MP_TAC o SPECL [`s:real`; `y:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `VT:A topology`;
                 `VA:((A->bool)#(A->real^3))->bool`; `\z:A. (Q:num->real) k %% (VG:A->real^3^3) z`;
                 `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                 `(phi:num->B->A) k`; `psi:A->B`; `&1`; `0`; `d pow 2 / &2`; `y:B`]
                P2B9S_PB_QF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
  REWRITE_TAC[P2B9_PULLBACK_METRIC_CMUL; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `sqrt(d pow 2 / &2) <= d /\ &0 < sqrt(d pow 2 / &2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(d pow 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN
        MP_TAC(SPEC `d:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
      MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `qb = v dot ((g:real->B->real^3^3) s y ** v)` THEN
  ABBREV_TAC `qa = v dot (mfd_pullback_metric atlas (VA:((A->bool)#(A->real^3))->bool)
                            ((phi:num->B->A) k) (VG:A->real^3^3) y ** v)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= qb` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt(d pow 2 / &2) * qb` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Q:num->real) k * qa - qb)` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_SIMP_TAC[REAL_LE_MUL_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(d pow 2 / &2) * qb` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The exit argument (general manifolds).                                    *)
(* ========================================================================= *)
(* Images of compact and of open subsets under a diffeomorphism of open     *)
(* sets, into a Hausdorff space.                                             *)

let LIM_DIFFEO_IMAGE_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (top':B topology)
    (atlas':((B->bool)#(B->real^M))->bool) U U' psi psi' C S.
     hausdorff_space top' /\ mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top C /\ C SUBSET U /\ open_in top S /\ S SUBSET U
     ==> closed_in top' (IMAGE psi C) /\ open_in top' (IMAGE psi S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`; `U':B->bool`;
                   `psi:A->B`; `psi':B->A`; `S:A->bool`] MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[mfd_diffeo]]);;
(* The exit argument: a short curve from psi y0 stays in the image of the   *)
(* ball B(y1,R), when the pullback of g' by psi is >= mu g on U and the     *)
(* closure of the ball is a                                                  *)
(* compact subset of U.                                                      *)

let LIM_CURVES_STAY = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' y1 y0 R R0 mu
    (gamma:real->B).
     hausdorff_space top' /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top (top closure_of mfd_ball (top,atlas) g y1 R) /\
     top closure_of mfd_ball (top,atlas) g y1 R SUBSET U /\ &0 < mu /\
     (!z v. z IN U
            ==> mu * (v dot (g z ** v)) <=
                v dot (mfd_pullback_metric atlas atlas' psi g' z ** v)) /\
     y0 IN mfd_ball (top,atlas) g y1 R0 /\
     mfd_c1_curve (top',atlas') gamma (&0) (&1) /\ gamma(&0) = psi y0 /\
     mfd_length atlas' g' gamma (&0) (&1) < sqrt mu * (R - R0)
     ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN IMAGE psi (mfd_ball (top,atlas) g y1 R)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = mfd_ball (top,atlas) (g:A->real^N^N) y1 R` THEN
  ABBREV_TAC `C = top closure_of (B:A->bool)` THEN
  SUBGOAL_THEN `&0 <= mfd_length atlas' (g':B->real^N^N) gamma (&0) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt mu` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `R0 < R` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(R <= R0) ==> R0 < R`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `sqrt mu * (R - R0) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (B:A->bool) /\ B SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:A->bool) SUBSET C /\ B SUBSET U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_SIMP_TAC[CLOSURE_OF_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (B:A->bool)` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN B` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:A) IN mfd_ball (top,atlas) (g:A->real^N^N) y1 R0` THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `U:A->bool`; `U':B->bool`;
                 `psi:A->B`; `psi':B->A`; `C:A->bool`; `B:A->bool`] LIM_DIFFEO_IMAGE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `gamma:real->B`; `IMAGE (psi:A->B) B`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool) gamma (&0) (&1)` THEN
      SIMP_TAC[mfd_c1_curve];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma:real->B) t1 IN IMAGE (psi:A->B) C` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_CLOSED_LEFT_CURVE THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool) gamma (&0) (&1)` THEN
      SIMP_TAC[mfd_c1_curve];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:A->bool) SUBSET U` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `p = (psi':B->A) (gamma(t1:real))` THEN
  SUBGOAL_THEN `(p:A) IN C /\ (psi:A->B) p = gamma(t1:real)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,t1] ==> (gamma:real->B) t IN IMAGE (psi:A->B) C`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t = t1:real` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gamma:real->B) t IN IMAGE (psi:A->B) B` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool) gamma (&0) t1 /\
                mfd_length atlas' (g':B->real^N^N) gamma (&0) t1 <=
                mfd_length atlas' g' gamma (&0) (&1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `g':B->real^N^N`; `gamma:real->B`; `&0`; `t1:real`; `&1`]
                  MFD_LENGTH_COMBINE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `g':B->real^N^N`; `gamma:real->B`; `t1:real`; `&1`] MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist_in (top',atlas') (g':B->real^N^N) (IMAGE (psi:A->B) C) (gamma(&0)) (gamma t1) <=
    mfd_length atlas' g' gamma (&0) t1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_joinable_in (top',atlas':((B->bool)#(B->real^N))->bool) (IMAGE (psi:A->B) C)
      (gamma(&0)) (gamma(t1:real))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_joinable_in] THEN
    EXISTS_TAC `(gamma:real->B) o (\x. &0 + (t1 - &0) * x)` THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `gamma:real->B`; `&0`; `t1:real`] GRGD_AFFINE_CURVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `real_interval[&0,t1]`)) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= t * x ==> &0 <= &0 + (t - &0) * x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `t * x <= t * &1 ==> &0 + (t - &0) * x <= t`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `C:A->bool`; `inv mu`;
                 `y0:A`; `p:A`] P2B9S_DIST_IN_PB_GE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:A`; `v:real^N`] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `mu:real` THEN
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y0 p < R - R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^N^N) C y0 p` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sqrt(inv mu) * mfd_length atlas' (g':B->real^N^N) gamma (&0) (&1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(inv mu) * mfd_dist_in (top',atlas') (g':B->real^N^N)
                    (IMAGE (psi:A->B) C) (psi(y0:A)) (psi(p:A))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      UNDISCH_THEN `(gamma:real->B)(&0) = psi(y0:A)` (SUBST1_TAC o SYM) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(inv mu) * sqrt mu = &1` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SQRT_MUL] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; SQRT_1];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(inv mu)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sqrt(inv mu) * (sqrt mu * (R - R0))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    UNDISCH_TAC `(y0:A) IN mfd_ball (top,atlas) (g:A->real^N^N) y1 R0` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y0 p` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN EXISTS_TAC `C:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `y1:A`; `y0:A`; `p:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~((gamma:real->B) t1 IN IMAGE (psi:A->B) B)` THEN
  UNDISCH_THEN `(psi:A->B) p = gamma(t1:real)` (SUBST1_TAC o SYM) THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* Balls under a diffeomorphism close to an isometry after the scaling by c  *)
(* (general manifolds, dimension 3).                                         *)
(* ========================================================================= *)
(* A curve from y0 of length < r stays in the ball B(y0,r).                 *)

let LIM_CURVE_IN_BALL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) y0 r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y0 /\
     mfd_length atlas g gamma (&0) (&1) < r
     ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN mfd_ball (top,atlas) g y0 r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `&0`; `s:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `s:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `&0`; `s:real`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `&0`; `s:real`] MFD_C1_CURVE_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `(gamma:real->A)(&0) = y0` (SUBST_ALL_TAC o SYM) THEN ASM_REAL_ARITH_TAC);;

(* Images of balls under a diffeomorphism psi with c (pullback of g' by psi) *)
(* <= (1+d) g.                                                               *)

let LIM_PB_BALL_IMAGE = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' y0 rho c d q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     mfd_ball (top,atlas) g y0 rho SUBSET U /\ &0 < c /\ &0 <= d /\
     (!y v. y IN U
            ==> c * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v)) <=
                (&1 + d) * (v dot (g y ** v))) /\
     y0 IN U /\ q IN mfd_ball (top,atlas) g y0 rho
     ==> psi q IN mfd_ball (top',atlas') g' (psi y0) (sqrt((&1 + d) / c) * rho)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BC_BALL_IMAGE_IN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `U:A->bool`; `U':B->bool`; `psi':B->A`;
                        `rho:real`; `(&1 + d) / c`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `rho:real`)) (concl th) && not (is_forall(concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `y0:A`; `rho:real`] LIM_CURVE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ];
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC]);;

(* Preimages of view balls: a ball of radius rho about psi y0 lies in the   *)
(* image of B(y1,R) and pulls back into B(y0, sqrt(c/(1-d)) rho), when      *)
(* (1-d) g <= c (pullback of g' by psi) on U and the closure of B(y1,R) is  *)
(* compact in U.                                                             *)

let LIM_PB_BALL_PREIMAGE = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    y1 y0 R R0 c d rho q.
     hausdorff_space top' /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top (top closure_of mfd_ball (top,atlas) g y1 R) /\
     top closure_of mfd_ball (top,atlas) g y1 R SUBSET U /\
     &0 < c /\ &0 <= d /\ d < &1 /\
     (!y v. y IN U
            ==> (&1 - d) * (v dot (g y ** v)) <=
                c * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
     y0 IN mfd_ball (top,atlas) g y1 R0 /\ sqrt c * rho <= sqrt(&1 - d) * (R - R0) /\
     q IN mfd_ball (top',atlas') g' (psi y0) rho
     ==> q IN IMAGE psi (mfd_ball (top,atlas) g y1 R) /\
         psi' q IN mfd_ball (top,atlas) g y0 (sqrt(c / (&1 - d)) * rho) /\
         psi (psi' q) = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:B) IN mfd_ball (top',atlas') (g':B->real^3^3) ((psi:A->B) y0) rho` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':B->real^3^3`; `(psi:A->B) y0`; `q:B`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c /\ &0 < sqrt(&1 - d) /\ &0 < &1 - d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `R0 < R` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(R <= R0) ==> R0 < R`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(&1 - d) * (R - R0) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt c * rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `B = mfd_ball (top,atlas) (g:A->real^3^3) y1 R` THEN
  SUBGOAL_THEN `open_in top (B:A->bool) /\ B SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:A->bool) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (B:A->bool)` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN B` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:A) IN mfd_ball (top,atlas) (g:A->real^3^3) y1 R0` THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `U':B->bool`;
                 `psi:A->B`; `psi':B->A`; `B:A->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `B:A->bool`; `IMAGE (psi:A->B) B`; `psi:A->B`; `psi':B->A`; `y0:A`;
                 `rho:real`; `c / (&1 - d)`; `q:B`] P2BC_BALL_PREIMAGE_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `g':B->real^3^3`; `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                     `y1:A`; `y0:A`; `R:real`; `R0:real`; `(&1 - d) / c`; `gamma:real->B`]
                    LIM_CURVES_STAY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`z:A`; `v:real^3`] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `c:real` THEN
        ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SQRT_DIV] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `a / b * x = (a * x) / b`] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&1 - d` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Ball inclusions for flow limits.                                          *)
(* ========================================================================= *)
(* Rescaled view balls about phi k y lie in the images of slightly larger  *)
(* limit balls about y, eventually.                                         *)

let LIM_BALL_IN = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s y r r'.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
     y IN topspace top /\ &0 < r /\ r < r'
     ==> ?k0. !k z. k0 <= k /\
                    z IN mfd_ball (rfs_vtop (V k) (t k + s / Q k),
                                   rfs_vatlas (V k) (t k + s / Q k))
                                  (rfs_vmetric (V k) (t k + s / Q k))
                                  (phi k y) (r * inv(sqrt(Q k)))
                    ==> z IN IMAGE (phi k) (mfd_ball (top,atlas) (g s) y r' INTER W k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  ABBREV_TAC `rho0 = (r + r') / &2` THEN
  SUBGOAL_THEN `&0 < rho0 /\ r < rho0 /\ rho0 < r'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / rho0 /\ r / rho0 < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `dd = &1 - (r / rho0) pow 2` THEN
  SUBGOAL_THEN `&0 < dd /\ dd < &1 /\ sqrt(&1 - dd) = r / rho0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 < (r / rho0) pow 2 /\ (r / rho0) pow 2 < &1` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_1_LT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y (r' + &1)` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `s:real`; `Kc:B->bool`;
                 `dd:real`] LIM_QF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s' = s:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `z:A`] THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real`)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) (LABEL_TAC "qf")))) THEN
  SUBGOAL_THEN `hausdorff_space (VT:A topology)` ASSUME_TAC THENL
   [EXPAND_TAC "VT" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `U = mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y (r' + &1)` THEN
  SUBGOAL_THEN `open_in top (U:B->bool) /\ U SUBSET Kc` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "Kc"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) SUBSET W(k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) k`;
                 `VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                 `U:B->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Bl = mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y r'` THEN
  SUBGOAL_THEN `compact_in top (top closure_of (Bl:B->bool)) /\ top closure_of Bl SUBSET U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `y:B`; `Bl:B->bool`; `r':real`]
                    P2BL_BOUNDED_CLOSURE_COMPACT) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Bl" THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y r'` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
        ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN EXPAND_TAC "Bl" THEN
        REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
        EXPAND_TAC "U" THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[REAL_ARITH `x <= r' ==> x < r' + &1`]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `VT:A topology`;
                 `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `U:B->bool`;
                 `IMAGE ((phi:num->B->A) k) U`; `(phi:num->B->A) k`; `psi:A->B`;
                 `y:B`; `y:B`; `r':real`; `r' - rho0`; `(Q:num->real) k`; `dd:real`;
                 `r * inv(sqrt((Q:num->real) k))`; `z:A`] LIM_PB_BALL_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`w:B`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "qf" (MP_TAC o SPECL [`w:B`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_ARITH `r' - (r' - rho0) = rho0`] THEN
      SUBGOAL_THEN `&0 < sqrt((Q:num->real) k)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < q ==> q * r * inv q = r`;
                   REAL_FIELD `&0 < rho0 ==> r / rho0 * rho0 = r`; REAL_LE_REFL]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(z:A) IN IMAGE ((phi:num->B->A) k)
                 (mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y r')` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Bl:B->bool) SUBSET W(k:num)` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:B->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (Bl:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN EXPAND_TAC "Bl" THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    SET_TAC[]]);;
(* Images of limit balls about y lie in slightly larger rescaled view balls *)
(* about phi k y, eventually.                                                *)

let LIM_BALL_OUT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s y r r'.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
     y IN topspace top /\ &0 < r /\ r < r'
     ==> ?k0. !k z. k0 <= k /\ z IN mfd_ball (top,atlas) (g s) y r
                    ==> z IN W k /\
                        phi k z IN mfd_ball (rfs_vtop (V k) (t k + s / Q k),
                                             rfs_vatlas (V k) (t k + s / Q k))
                                            (rfs_vmetric (V k) (t k + s / Q k))
                                            (phi k y) (r' * inv(sqrt(Q k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  ABBREV_TAC `dd = (r' / r) pow 2 - &1` THEN
  SUBGOAL_THEN `&0 < dd /\ sqrt(&1 + dd) = r' / r /\ &0 < r' / r` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 < r' / r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 < x ==> &0 < x - &1`) THEN
      MATCH_MP_TAC REAL_POW_LT_1 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y (r + &1)` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `s:real`; `Kc:B->bool`;
                 `dd:real`] LIM_QF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s' = s:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `z:B`] THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real`)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) (LABEL_TAC "qf")))) THEN
  ABBREV_TAC `U = mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y (r + &1)` THEN
  SUBGOAL_THEN `open_in top (U:B->bool) /\ U SUBSET Kc` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "Kc"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) SUBSET W(k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y r SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_ARITH `x < r ==> x < r + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) k`;
                 `VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                 `U:B->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `VT:A topology`;
                 `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `U:B->bool`;
                 `IMAGE ((phi:num->B->A) k) U`; `(phi:num->B->A) k`; `psi:A->B`;
                 `y:B`; `r:real`; `(Q:num->real) k`; `dd:real`; `z:B`] LIM_PB_BALL_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`w:B`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "qf" (MP_TAC o SPECL [`w:B`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> a IN s ==> a IN t`) THEN
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt((&1 + dd) / (Q:num->real) k) * r = r' * inv(sqrt(Q k))` (fun th ->
    ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[SQRT_DIV] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt((Q:num->real) k)` MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

