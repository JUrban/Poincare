(* ========================================================================= *)
(* Unit pc_p3_c171b: MT Prop 17.1 (pp. 395, 401-408), the                   *)
(* per-history and sequence foundation.  The worst bad point (avoids MT's  *)
(* Claim 17.6), Thm 10.2 applied (ball bounds), Lemma 11.2 applied (MT     *)
(* Claim 17.9), the standard solution near the tip and its caps (Thm 12.32 *)
(* at small t > 0 with the Prop 9.79 cap transfer: route (B), a deviation  *)
(* from MT's time-0 cap), fresh caps at the                                *)
(* bad time (cap of the stage or strong neck at x), closedness of          *)
(* noncollapsing at the bad time, Claim 17.9 for one ball and for the      *)
(* counterexample sequence (A-ball persistence over dl/Q with R <= K Q,    *)
(* flow lines of length mu / max(Q, R)), and p3_blowup_seq of the           *)
(* counterexamples (the hypothesis of Thm 11.8).                            *)
(* ========================================================================= *)

needs "src/pc_p3_c171a.ml";;
needs "src/pc_p3_c172f.ml";;
needs "src/pc_p3_c177e.ml";;
needs "src/pc_lck_swap.ml";;
needs "src/pc_rf_unique_a14.ml";;
needs "src/pc_apx_a22.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_p2c_blowup.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_p2b_a4s.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Prop 17.1, step S1: the worst bad point at the first bad time.  Among    *)
(* the points of the slice at ts with R >= r^-2 and no canonical            *)
(* neighbourhood, one with R(x) > sup/2: every point of the slice with      *)
(* R >= 2 R(x) then has one (this replaces MT's Claim 17.6 at time ts in    *)
(* the hypotheses of Thm 10.2).                                             *)
(* ========================================================================= *)

let P3H_WORST_POINT = prove
 (`!(P:A->bool) (f:A->real) x0.
     P x0 /\ &0 < f x0 /\ (?b. !y. P y ==> f y <= b)
     ==> ?x. P x /\ &0 < f x /\ !y. P y ==> f y < &2 * f x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `b:real`))) THEN
  ABBREV_TAC `s = {(f:A->real) y | P y}` THEN
  SUBGOAL_THEN `!z. z IN s <=> ?y. (P:A->bool) y /\ z = (f:A->real) y` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real->bool = {}) /\ (?c. !z. z IN s ==> z <= c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
      EXISTS_TAC `b:real` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `!y. (P:A->bool) y ==> (f:A->real) y <= sup s` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real) x0 <= sup s` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real->bool`; `sup s / &2`] SUP_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?x:A. P x /\ z = (f:A->real) x` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:A->real) y <= sup s` MP_TAC THENL
   [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]);;

let P3H_SLICE_SCALAR_BOUNDED = prove
 (`!(hs:(A)rfs_history) t.
     rfs_history_ok hs
     ==> ?b. !y. y IN topspace(rfs_top_at hs t) ==> rfs_vscalar (rfs_view hs) t y <= b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `t:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_vtop (rfs_view (hs:(A)rfs_history)) t = rfs_top_at hs t /\
                (!y. rfs_vscalar (rfs_view hs) t y =
                     mfd_scalar (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t) y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfs_view; rfs_vtop; rfs_vscalar; rfs_vatlas; rfs_vmetric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `euclideanreal`;
                 `mfd_scalar (rfs_vatlas (rfs_view (hs:(A)rfs_history)) t)
                             (rfs_vmetric (rfs_view hs) t)`;
                 `topspace(rfs_top_at (hs:(A)rfs_history) t)`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM compact_space] THEN MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`]);;

let P3H_171_WORST_BAD = prove
 (`!(hs:(A)rfs_history) ts r (good:A->bool) x0.
     rfs_history_ok hs /\ &0 < r /\ x0 IN topspace(rfs_top_at hs ts) /\
     inv(r pow 2) <= rfs_vscalar (rfs_view hs) ts x0 /\ ~good x0
     ==> ?x. x IN topspace(rfs_top_at hs ts) /\
             inv(r pow 2) <= rfs_vscalar (rfs_view hs) ts x /\ ~good x /\
             !y. y IN topspace(rfs_top_at hs ts) /\
                 &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                 ==> good y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(r pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_SLICE_SCALAR_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN
  MP_TAC(ISPECL [`\y:A. y IN topspace(rfs_top_at (hs:(A)rfs_history) ts) /\
                        inv(r pow 2) <= rfs_vscalar (rfs_view hs) ts y /\ ~good y`;
                 `rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts`; `x0:A`] P3H_WORST_POINT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `b:real` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `&2`)) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_NOT_LT] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 17.1, step S4a: at the worst bad point x at the first bad time ts,  *)
(* every point at a time s <= ts with R >= c R(x), c >= 2, has a canonical *)
(* neighbourhood (before ts by the truncation, at ts by the choice of x),   *)
(* so Thm 10.2 bounds R by D R(x) on B(x, ts, A R(x)^-1/2).                 *)
(* ========================================================================= *)

(* In the unit pc_p3_c171a: P3H_STEPF_AT_BAD, P3H_TOPSPACE_TIME_POS,
   P3H_171_CANON_ABOVE. *)

let P3H_171_BALL_BOUND = prove
 (`!u:A->bool.
     P2_THM_10_2_STATEMENT u /\ APX_SC_SPHERE_SEP_STATEMENT (:A) /\
     RFS_CUTCAP_SC_STATEMENT (:A) (:A)
     ==> ?eps0. &0 < eps0 /\
           !eps C A. &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A
             ==> ?D0 D. &0 < D0 /\ &0 < D /\
                   !hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x.
                      rs' (SUC i) = r' /\ &0 < r' /\ D0 <= inv(r' pow 2) /\
                      p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                      p3_T i <= ts /\ ts < rfs_horizon hs /\
                      rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps
                        (p3_stepf rs') /\
                      x IN topspace(rfs_top_at hs ts) /\
                      inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                      (!y. y IN topspace(rfs_top_at hs ts) /\
                           &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                           ==> p3_canon_at (rfs_view hs) C eps y ts)
                      ==> !y. y IN rfs_vball (rfs_view hs) ts x
                                     (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                              ==> rfs_vscalar (rfs_view hs) ts y <=
                                  D * rfs_vscalar (rfs_view hs) ts x`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[P2_THM_10_2_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "102"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `A:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "102" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`D0:real`; `D:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ASSUME `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                   (hs:(A)rfs_history)`) THEN
  REWRITE_TAC[p3_step_hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd)
                   (hs:(A)rfs_history)` THEN SIMP_TAC[p3_struct];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3_STRUCT_SPHERE_SEP THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                          `g0:real^3->real^3^3`; `A0:real`; `p3_stepf rs'`; `p3_stepf dd`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p3_T i` THEN ASM_REWRITE_TAC[p3_T] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
    MATCH_MP_TAC P3H_171_CANON_ABOVE THEN
    MAP_EVERY EXISTS_TAC [`hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
                          `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
                          `dlt:real`; `rs':num->real`; `ks':num->real`; `dd:num->real`;
                          `r':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[p3_step_hyp] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 17.1, step L (MT Claim 17.9 with Lemma 11.2): from a point z of the *)
(* slice at the first bad time ts with R(z) <= D R(x), on a small ball      *)
(* B(z, ts, rr) persisting back to t' >= ts - 1/(16 C (D+2) R(x)), R stays  *)
(* below 2 (D+2) R(x) (Lemma 11.2 with threshold r0^-2 = 2 R(x): canonical  *)
(* before ts above r'^-2 <= R(x), at ts above 2 R(x) by the worst point).   *)
(* ========================================================================= *)

let P3H_171_BACK_BOUND = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x z t' rr D.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              z IN topspace(rfs_top_at hs ts) /\ &0 <= D /\
              rfs_vscalar (rfs_view hs) ts z <= D * rfs_vscalar (rfs_view hs) ts x /\
              &0 < rr /\ rr <= inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x)) /\
              t' <= ts /\
              ts - t' <= inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) /\
              rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) ts z rr) t' ts
              ==> !s y. t' < s /\ s <= ts /\ y IN rfs_vball (rfs_view hs) ts z rr
                        ==> rfs_vscalar (rfs_view hs) s y <=
                            &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x`,
  GEN_TAC THEN REWRITE_TAC[P2_LEMMA_11_2_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "112"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                   (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(inv(sqrt(&2 * Q)) pow 2) = &2 * Q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; REAL_INV_INV] THEN MATCH_MP_TAC SQRT_POW_2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "112" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`;
    `inv(sqrt(&2 * Q))`; `z:A`; `ts:real`; `t':real`; `rr:real`]) THEN
  ASM_SIMP_TAC[REAL_ARITH `t' <= ts ==> min ts t' = t' /\ max ts t' = ts`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                     `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`;
                     `ks:num->real`; `ds:num->real`; `dlt:real`; `rs':num->real`;
                     `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
                     `ts:real`; `x:A`; `&2`] P3H_171_CANON_ABOVE) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&2 * C * sqrt((D + &2) * Q))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN
        SUBGOAL_THEN `&0 <= D * Q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_ARITH `t' <= ts ==> abs(t' - ts) = ts - t'`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&16 * C * (D + &2) * Q)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= D * Q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (max (&0) (rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts z) + &2 * Q)` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D * Q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Fresh caps at the bad time, F2: at a small time t > 0 a point q of the   *)
(* standard solution near the tip has only the cap alternative of Thm 12.32 *)
(* (a neck of length 1 + eps would reach before time 0; a neck from time 0  *)
(* inside dist0 >= A0 + 5 would have to contain the tip, which is closer    *)
(* than its exit length).  DEVIATION FROM MT: MT uses Thm 12.32 at          *)
(* normalized time 0 (Lemma 17.7 with t_a = 0, p. 401); the formal 12.32 is *)
(* for 0 < t < 1, so we use it at a small t > 0 and pass to t = 0 by the    *)
(* C^k closeness of the standard flow to g0 (P3H_SLICES_TUBE_FROM).        *)
(* ========================================================================= *)

let P3H_NECK_TIP_BOUND = prove
 (`!g0 A0 eps (G:real->real^3->real^3^3) q t (e:real^3->real^3).
     p3_std_initial g0 A0 /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\ G (&0) = g0 /\
     (!s y u v. &0 < s /\ s < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (G s) y u v) /\
     &0 < eps /\ eps < &1 /\ &0 <= t /\ t < &1 /\
     rfs_neck (euclidean,open_set_atlas (:real^3)) (G t) eps q e /\
     ~((vec 0:real^3) IN IMAGE e (rfs_neck_dom eps))
     ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) (G t) q)) * inv eps
         <= p3_std_dist g0 q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) q` THEN
  MP_TAC(ASSUME `rfs_neck (euclidean,open_set_atlas (:real^3))
                   ((G:real->real^3->real^3^3) t) eps q e`) THEN
  REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN sphere(vec 0,&1) /\ (e:real^3->real^3) y0 = q`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&1 - eps) * inv(sqrt R) * (inv eps - abs(apx_sval (y0:real^3))) <=
    mfd_dist (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) q (vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_DIST_GE_CURVES THEN REWRITE_TAC[P2C_RAD_JOINABLE] THEN
    X_GEN_TAC `gamma:real->real^3` THEN STRIP_TAC THEN
    EXPAND_TAC "R" THEN MATCH_MP_TAC APX_NECK_EXIT THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `e:real^3->real^3`] THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `(G:real->real^3->real^3^3) t`; `&1`;
                 `q:real^3`; `vec 0:real^3`] P3N_DIST_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; P2C_RAD_JOINABLE; REAL_MUL_LID] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(G:real->real^3->real^3^3) (&0) = g0`)) THEN
    MATCH_MP_TAC P3H_RF_QF_NONINCR THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_dist (euclidean,open_set_atlas (:real^3)) g0 q (vec 0) =
                p3_std_dist g0 q` ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `sqrt(&1 - eps) * inv(sqrt R) * (inv eps - abs(apx_sval (y0:real^3))) <=
    mfd_dist (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) q (vec 0)` THEN
  ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN ASM_REAL_ARITH_TAC);;

let P3H_STD_EARLY_CAP = prove
 (`!g0 A0 eps C' (G:real->real^3->real^3^3) q t.
     p3_std_initial g0 A0 /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\ G (&0) = g0 /\
     (!s y u v. &0 < s /\ s < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (G s) y u v) /\
     &0 < eps /\ eps < &1 /\ &0 < t /\ t < &1 /\
     t * mfd_scalar (open_set_atlas (:real^3)) (G t) q < &1 /\
     p3_std_dist g0 q <
     sqrt(&1 - eps) * inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) (G t) q)) * inv eps /\
     ((?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t) C' eps U Y /\ q IN Y) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps q t (t * mfd_scalar (open_set_atlas (:real^3)) (G t) q) e /\
           !z. z IN IMAGE e (rfs_neck_dom eps) ==> A0 + &5 <= p3_std_dist g0 z) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps q t (&1 + eps) e))
     ==> ?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t) C' eps U Y /\ q IN Y`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (vec 0) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                   (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ACCEPT_TAC (DISJ_CASES_THEN2 MP_TAC MP_TAC) o check (fun th ->
    is_disj(concl th))) THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:real^3->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `rfs_neck (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)
                    eps q e` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_evolving_neck
        (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                       (G:real->real^3->real^3^3))
        eps q t (t * mfd_scalar (open_set_atlas (:real^3)) (G t) q) e` THEN
      REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
      REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((vec 0:real^3) IN IMAGE e (rfs_neck_dom eps))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th ->
        can (find_term (fun t -> t = `A0 + &5`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `eps:real`;
                   `G:real->real^3->real^3^3`; `q:real^3`; `t:real`; `e:real^3->real^3`]
                  P3H_NECK_TIP_BOUND) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->real^3` MP_TAC) THEN
    REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
    REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar;
                IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    MP_TAC(ASSUME `rfs_neck (euclidean,open_set_atlas (:real^3))
                     ((G:real->real^3->real^3^3) t) eps q e`) THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) q` THEN
    SUBGOAL_THEN `t - (&1 + eps) / R < &0` ASSUME_TAC THENL
     [SUBGOAL_THEN `t < (&1 + eps) / R` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(t - (&1 + eps) / R) / &2` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&0 <= (t - (&1 + eps) / R) / &2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Fresh caps, F3a support: bounds for ONE fixed standard flow G0 on a      *)
(* short time interval [0,b1]: R between c > 0 (Prop 12.31) and Rm, and    *)
(* g0 <= 4 G0(t) (Ricci flow metric equivalence, RFU_FLOW_EQUIV).          *)
(* ========================================================================= *)

let P3H_STD_FLOW0_BOUNDS = prove
 (`!g0 A0 (G:real->real^3->real^3^3).
     P2_PROP_12_31_STATEMENT /\ p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G
     ==> ?c Rm b1. &0 < c /\ &0 < Rm /\ &0 < b1 /\ b1 <= &1 / &4 /\
                   (!t x. &0 <= t /\ t <= b1
                          ==> c <= mfd_scalar (open_set_atlas (:real^3)) (G t) x /\
                              mfd_scalar (open_set_atlas (:real^3)) (G t) x <= Rm) /\
                   (!t x v. &0 <= t /\ t <= b1
                            ==> v dot (g0 x ** v) <= &4 * (v dot (G t x ** v)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)`) THEN
  REWRITE_TAC[p3_std_flow; p3_partial_std] THEN STRIP_TAC THEN
  UNDISCH_TAC `P2_PROP_12_31_STATEMENT` THEN REWRITE_TAC[P2_PROP_12_31_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &2` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
  CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^3))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < &1
                    ==> riemannian_metric (open_set_atlas (:real^3))
                          ((G:real->real^3->real^3^3) t)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_CHOOSE_THEN `Cs:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RS"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_SCALAR_FROM_RMNORM) THEN
  X_CHOOSE_THEN `Ce:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FE"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_FLOW_EQUIV) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `Cs * abs K + &1`;
                        `min (&1 / &4) (inv(&16 * Ce * abs K + &1))`] THEN
  SUBGOAL_THEN `&0 <= Ce * abs K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&16 * Ce * abs K + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Cs * abs K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC;
    (* the scalar bounds *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / (&1 - t)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `t <= &1 / &4 ==> &0 < &1 - t`] THEN
        MATCH_MP_TAC(REAL_ARITH `!c t. &0 <= c * t ==> c * (&1 - t) <= c`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `!x b. abs x <= b ==> x <= b + &1`) THEN
      REMOVE_THEN "RS" MATCH_MP_TAC THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; REAL_ABS_POS] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `!x K. x <= K ==> x <= abs K`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    (* the metric comparison *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `v:real^3`] THEN REWRITE_TAC[REAL_LE_MIN] THEN
    STRIP_TAC THEN
    REMOVE_THEN "FE" (MP_TAC o SPECL
      [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `&1`;
       `G:real->real^3->real^3^3`; `&2 * min (&1 / &4) (inv(&16 * Ce * abs K + &1))`;
       `abs K`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_ABS_POS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `!x K. x <= K ==> x <= abs K`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:real^3`; `v:real^3`]) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    ABBREV_TAC `z = &2 * (Ce * abs K) * (&2 * min (&1 / &4) (inv(&16 * Ce * abs K + &1)))` THEN
    SUBGOAL_THEN `&0 <= z /\ z <= inv(&2)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&4 * (Ce * abs K) * inv(&16 * Ce * abs K + &1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&2 * a * &2 * m = &4 * a * m`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &16 * Ce * abs K + &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&4 * (Ce * abs K) * inv(&16 * Ce * abs K + &1) =
                    (&4 * (Ce * abs K)) / (&16 * Ce * abs K + &1)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp z <= &4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * z` THEN
      ASM_SIMP_TAC[REAL_EXP_BOUND_LEMMA] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= v dot ((g0:real^3->real^3^3) x ** v)` ASSUME_TAC THENL
     [ASM_CASES_TAC `v:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                       `g0:real^3->real^3^3`; `x:real^3`] RIEMANNIAN_METRIC_POS) THEN
        ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &4 <= exp(--z)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_NEG] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&4)` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &4 * (v dot ((g0:real^3->real^3^3) x ** v)) <=
                  exp(--z) * (v dot (g0 x ** v))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Fresh caps, F3a: caps of the standard initial metric g0 near the tip     *)
(* (MT uses Thm 12.32 at t = 0; we take the cap of Thm 12.32 at a small     *)
(* t > 0 for ONE fixed standard flow G0 and transfer it to g0 by Prop 9.79  *)
(* (cap form) along the identity: G0(t) is C^k close to g0 on compacta).    *)
(* ========================================================================= *)

let P3H_CAP_IN_BALL = prove
 (`!g0 (G:real^3->real^3^3) C' eps U Y q c.
     riemannian_metric (open_set_atlas (:real^3)) g0 /\
     riemannian_metric (open_set_atlas (:real^3)) G /\ &0 < c /\ &0 < C' /\
     rfs_cap (euclidean,open_set_atlas (:real^3)) G C' eps U Y /\ q IN U /\
     c <= mfd_scalar (open_set_atlas (:real^3)) G q /\
     (!z v. v dot (g0 z ** v) <= &4 * (v dot (G z ** v)))
     ==> !y. y IN U ==> p3_std_dist g0 y <= p3_std_dist g0 q + &2 * C' * inv(sqrt c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^3))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `G:real^3->real^3^3`;
                 `C':real`; `eps:real`; `U:real^3->bool`; `Y:real^3->bool`; `q:real^3`;
                 `y:real^3`] APX22_CAP_DIAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `G:real^3->real^3^3`; `g0:real^3->real^3^3`; `&4`; `q:real^3`; `y:real^3`]
                P3N_DIST_COMPARE) THEN
  ASM_REWRITE_TAC[P2C_RAD_JOINABLE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `sqrt(&4) = &2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&4 = &2 pow 2`] THEN MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `g0:real^3->real^3^3`;
                 `vec 0:real^3`; `q:real^3`; `y:real^3`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[P2C_RAD_JOINABLE] THEN REWRITE_TAC[GSYM p3_std_dist] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) G q)) <= inv(sqrt c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `C' * inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) G q)) <= C' * inv(sqrt c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_G0_CAPS = prove
 (`P2_THM_12_32_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_PROP_12_31_STATEMENT /\
   P3_STD_C2_BOUND_STATEMENT
   ==> ?eps0. &0 < eps0 /\
         !g0 A0 eps L.
           p3_std_initial g0 A0 /\ &0 < eps /\ eps <= eps0 /\ &0 <= L
           ==> ?C0. &1 < C0 /\
                 !q. p3_std_dist g0 q <= L
                     ==> ?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) g0 C0 eps U Y /\
                               q IN Y`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`] P2B_PROP_9_79_CAP_FIX) THEN
  REWRITE_TAC[P2B_PROP_9_79_CAP_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `ecf:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))))) THEN
  UNDISCH_TAC `P2_THM_12_32_STATEMENT` THEN REWRITE_TAC[P2_THM_12_32_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e32:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1232"))) THEN
  UNDISCH_TAC `P3_STD_C2_BOUND_STATEMENT` THEN REWRITE_TAC[P3_STD_C2_BOUND_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C2"))) THEN
  EXISTS_TAC `ecf:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `eps:real`; `L:real`] THEN
  STRIP_TAC THEN
  (* the fixed standard flow G and its facts *)
  MP_TAC(ASSUME `P2_THM_12_5_STATEMENT`) THEN REWRITE_TAC[P2_THM_12_5_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `G:real->real^3->real^3^3`) (LABEL_TAC "125")) THEN
  REMOVE_THEN "125" (LABEL_TAC "G125" o C MP (ASSUME `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)`) o
                  SPECL [`&1`; `G:real->real^3->real^3^3`]) THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3) /\ G (&0) = g0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s y u v. &0 < s /\ s < &1 /\ ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional (open_set_atlas (:real^3))
                                      ((G:real->real^3->real^3^3) s) y u v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "G125" (MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "G125" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`]
                P3H_STD_FLOW0_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `Rm:real` (X_CHOOSE_THEN `b1:real`
    STRIP_ASSUME_TAC))) THEN
  (* the source parameter es *)
  SUBGOAL_THEN `&0 < sqrt Rm` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * (L + &1) * sqrt Rm)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?es. &0 < es /\ K * es <= eps /\ es <= e32 /\ es <= ec2 /\ es <= &1 / &2 /\
                     es <= inv(&4 * (L + &1) * sqrt Rm)`
  (X_CHOOSE_THEN `es:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min (eps / K) (min e32 (min ec2 (min (&1 / &2)
                  (inv(&4 * (L + &1) * sqrt Rm)))))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN
    SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      SUBGOAL_THEN `K * min (eps / K) (min e32 (min ec2 (min (&1 / &2)
                       (inv(&4 * (L + &1) * sqrt Rm))))) <= K * (eps / K)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]];
      REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Thm 12.32 at es, the C^2 bound, Prop 9.79 (cap form) *)
  REMOVE_THEN "1232" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `es:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAP32"))) THEN
  REMOVE_THEN "C2" (MP_TAC o SPECL [`C1:real`; `es:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KR"))) THEN
  REMOVE_THEN "CF" (MP_TAC o SPECL [`C1:real`; `es:real`; `&2 * C1`; `eps:real`; `Kr:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))) THEN
  EXISTS_TAC `&2 * C1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the base swap constant, the compact region, the time t *)
  X_CHOOSE_THEN `Msw:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SW"))
    (SPEC `rfs_kreg delta` (INST_TYPE [`:3`,`:N`] LCK_CK_BASE_REV)) THEN
  SUBGOAL_THEN `&0 < (&1 + inv c) pow (rfs_kreg delta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    SUBGOAL_THEN `&0 < inv c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?th. &0 < th /\ th <= &1 / &4 /\
                     (&1 + inv c) pow (rfs_kreg delta) * Msw * th < delta pow 2`
  (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC) THENL
   [ABBREV_TAC `P = (&1 + inv c) pow (rfs_kreg delta)` THEN
    SUBGOAL_THEN `&0 < delta pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * P * (Msw + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < delta pow 2 / (&2 * P * (Msw + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `min (&1 / &4) (delta pow 2 / (&2 * P * (Msw + &1)))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `P * Msw * (delta pow 2 / (&2 * P * (Msw + &1)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `P * Msw * (delta pow 2 / (&2 * P * (Msw + &1))) =
                  (Msw * delta pow 2) / (&2 * (Msw + &1))` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(P = &0) /\ ~(Msw + &1 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * (Msw + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= Msw * delta pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `G:real->real^3->real^3^3`; `&0`; `&1`; `&1`; `&0`; `rfs_kreg delta`;
                 `{x:real^3 | p3_std_dist g0 x <= L + &2 * C1 * inv(sqrt c)}`; `th:real`]
                P3H_SLICES_TUBE_FROM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC P3H_STD_REGION_COMPACT THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TUBE"))) THEN
  SUBGOAL_THEN `?t. &0 < t /\ t <= b1 /\ t < eta /\ t * Rm < &1 /\ t < &1`
  (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `&0 < inv(&2 * Rm)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `min b1 (min (eta / &2) (inv(&2 * Rm)))` THEN
    ABBREV_TAC `t = min b1 (min (eta / &2) (inv(&2 * Rm)))` THEN
    SUBGOAL_THEN `t <= inv(&2 * Rm) /\ &0 < t /\ t <= b1 /\ t < eta` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2 * Rm) * Rm` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `inv(&2 * Rm) * Rm = &1 / &2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Rm` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^3))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) /\
                metric_field (:real^3) (G t) /\ metric_field (:real^3) g0 /\
                riemannian_metric (open_set_atlas (:real^3)) g0 /\
                mfd_complete (euclidean,open_set_atlas (:real^3)) g0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) t) /\
                  metric_field (:real^3) (G (&0))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `metric_field (:real^3) ((G:real->real^3->real^3^3) (&0))` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) q <= Rm /\
                c <= mfd_scalar (open_set_atlas (:real^3)) (G t) q` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`t:real`; `q:real^3`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Rm:real`)) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the cap of G t at q *)
  SUBGOAL_THEN `t * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) q < &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t * Rm` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 q <
                sqrt(&1 - es) * inv(sqrt(mfd_scalar (open_set_atlas (:real^3))
                                           ((G:real->real^3->real^3^3) t) q)) * inv es`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - es)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt Rm) <= inv(sqrt(mfd_scalar (open_set_atlas (:real^3))
                                   ((G:real->real^3->real^3^3) t) q))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * (L + &1) * sqrt Rm <= inv es` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(sqrt Rm)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&1 / &2 * inv(sqrt Rm) * (&4 * (L + &1) * sqrt Rm)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&1 / &2 * inv(sqrt Rm) * (&4 * (L + &1) * sqrt Rm) = &2 * (L + &1)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt Rm` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= &4 * (L + &1) * sqrt Rm` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  REMOVE_THEN "CAP32" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `q:real^3`; `t:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `es:real`; `C1:real`;
                 `G:real->real^3->real^3^3`; `q:real^3`; `t:real`] P3H_STD_EARLY_CAP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `Y:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q:real^3) IN U` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `(G:real->real^3->real^3^3) t`; `C1:real`; `es:real`; `U:real^3->bool`;
                   `Y:real^3->bool`] P2B_CAP_CORE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in euclidean (U:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_cap (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)
                   C1 es U Y` THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[rfs_cap]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> p3_std_dist g0 y <= L + &2 * C1 * inv(sqrt c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(G:real->real^3->real^3^3) t`; `C1:real`; `es:real`;
                   `U:real^3->bool`; `Y:real^3->bool`; `q:real^3`; `c:real`] P3H_CAP_IN_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Prop 9.79 (cap form) along the identity *)
  REMOVE_THEN "CF" (MP_TAC o SPECL
    [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `(G:real->real^3->real^3^3) t`;
     `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `g0:real^3->real^3^3`;
     `q:real^3`; `U:real^3->bool`; `Y:real^3->bool`; `\x:real^3. x`; `\x:real^3. x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; IMAGE_ID] THEN REPEAT CONJ_TAC THENL
     [REMOVE_THEN "KR" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `t:real`; `q:real^3`;
                                        `U:real^3->bool`]) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[rfs_canonical_nbhd] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[rfs_mclose] THEN
      EXISTS_TAC `(&1 + inv c) pow (rfs_kreg delta) * Msw * th` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
      SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV];
                        ALL_TAC] THEN
      SUBGOAL_THEN `!Fm:real^3->real^3^3.
                      metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
        MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
        ALL_TAC] THEN
      REWRITE_TAC[SND; P3H_PULLBACK_OPEN_UNIV; P3H_ID_PULLBACK] THEN
      ABBREV_TAC `Rq = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) q` THEN
      MP_TAC(ISPECL [`rfs_kreg delta`; `(:real^3)`; `(G:real->real^3->real^3^3) t`;
                     `g0:real^3->real^3^3`; `Rq:real`; `y:real^3`] P2B9S_LCK_SCALE_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
      SUBGOAL_THEN `&0 <= lck_dist2 (rfs_kreg delta) ((G:real->real^3->real^3^3) t) g0 y`
      ASSUME_TAC THENL
       [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[IN_UNIV];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 + inv c) pow (rfs_kreg delta) *
                  lck_dist2 (rfs_kreg delta) ((G:real->real^3->real^3^3) t) g0 y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN
        SUBGOAL_THEN `&0 < inv Rq /\ inv Rq <= inv c` MP_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `lck_dist2 (rfs_kreg delta) g0 ((G:real->real^3->real^3^3) t) y < th`
      ASSUME_TAC THENL
       [USE_THEN "TUBE" (MP_TAC o SPECL [`t:real`; `y:real^3`]) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
            FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
        SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV];
                          ALL_TAC] THEN
        SUBGOAL_THEN `!Fm:real^3->real^3^3.
                        metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
        (fun th -> REWRITE_TAC[th]) THENL
         [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
          MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[SND; MATRIX_CMUL_LID; ETA_AX];
        ALL_TAC] THEN
      USE_THEN "SW" (MP_TAC o SPECL [`(:real^3)`; `g0:real^3->real^3^3`;
                                     `(G:real->real^3->real^3^3) t`; `g0:real^3->real^3^3`;
                                     `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`rfs_kreg delta`; `(:real^3)`; `g0:real^3->real^3^3`;
                     `(G:real->real^3->real^3^3) t`; `y:real^3`] LCK_DIST2_REFLECT) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Msw * lck_dist2 (rfs_kreg delta) g0 ((G:real->real^3->real^3^3) t) y` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':real^3->bool` (X_CHOOSE_THEN `Y':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`U':real^3->bool`; `Y':real^3->bool`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Fresh caps, F3b: P3H_CAP_TO_HIST (pc_p3_c172e) with an arbitrary positive *)
(* lower bound c for R at q instead of 1/2 (the g0-caps near the tip have   *)
(* R >= c of Prop 12.31 only).                                              *)
(* ========================================================================= *)

let P3H_CAP_TO_HIST_C = prove
 (`?K eps0. &1 <= K /\ &0 < eps0 /\
     !C eps C' eps' Kr.
       &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\ eps' <= eps0
       ==> ?delta. &0 < delta /\
             !(G0:real^3->real^3^3) q U Y (top:A topology) atlas g h W (Phi:real^3->A) d c.
               metric_field (:real^3) G0 /\
               rfs_cap (euclidean,open_set_atlas (:real^3)) G0 C eps U Y /\ q IN Y /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local (open_set_atlas (:real^3))
                               (chart_at (open_set_atlas (:real^3)) y)
                               (\z. mfd_scalar (open_set_atlas (:real^3)) G0 q %% G0 z))
                            (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
               hausdorff_space top /\ smooth_manifold_atlas top atlas /\
               riemannian_metric atlas g /\ compact_space top /\ &0 < h /\
               mfd_param top atlas W Phi /\ U SUBSET W /\
               &0 < c /\ c <= mfd_scalar (open_set_atlas (:real^3)) G0 q /\
               (&1 + inv c) pow (rfs_kreg delta) * d < delta pow 2 /\
               (!y. y IN W
                    ==> lck_dist2 (rfs_kreg delta) G0
                          (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d)
               ==> ?U' Y'. U' SUBSET IMAGE Phi U /\ rfs_cap (top,atlas) g C' eps' U' Y' /\
                           Phi q IN Y'`,
  MP_TAC(ISPECL [`(:real^3)`; `(:A)`] P2B_PROP_9_79_CAP_FIX) THEN
  REWRITE_TAC[P2B_PROP_9_79_CAP_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REMOVE_THEN "CF" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `Phi':A->real^3`) THEN
  SUBGOAL_THEN `open_in euclidean (U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_cap]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo euclidean (open_set_atlas (:real^3)) U (top:A topology)
                           (atlas:((A->bool)#(A->real^3))->bool)
                           (IMAGE (Phi:real^3->A) U) Phi Phi'` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN EXISTS_TAC `W:real^3->bool` THEN
    EXISTS_TAC `IMAGE (Phi:real^3->A) W` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Rq = mfd_scalar (open_set_atlas (:real^3)) (G0:real^3->real^3^3) q` THEN
  ABBREV_TAC `P = rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `&0 < inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REMOVE_THEN "CF" (MP_TAC o SPECL
    [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `G0:real^3->real^3^3`;
     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `\z:A. inv(h pow 2) %% (g:A->real^3^3) z`; `q:real^3`; `U:real^3->bool`;
     `Y:real^3->bool`; `Phi:real^3->A`; `Phi':A->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN
      REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_COMPACT_IMP_COMPLETE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `(&1 + inv c) pow (rfs_kreg delta) * d` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
    SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV];
                      ALL_TAC] THEN
    SUBGOAL_THEN
     `!Fm:real^3->real^3^3. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
      MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[SND; P2B9_PULLBACK_METRIC_CMUL] THEN REWRITE_TAC[P3H_PULLBACK_OPEN_UNIV] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field W (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) /\
                  metric_field W (G0:real^3->real^3^3)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[mfd_param] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[mfd_diffeo; OPEN_IN_EUCLIDEAN]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_kreg delta`; `W:real^3->bool`; `G0:real^3->real^3^3`;
                   `\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z`; `Rq:real`; `y:real^3`]
                  P2B9S_LCK_SCALE_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv Rq) pow rfs_kreg delta * d` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN
        SUBGOAL_THEN `&0 < inv Rq` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [SUBGOAL_THEN `&0 < inv Rq` MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          SUBGOAL_THEN `inv Rq <= inv c` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lck_dist2 (rfs_kreg delta) (G0:real^3->real^3^3)
                      (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) y` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `W:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `U':A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Y':A->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (\z:A. inv(h pow 2) %% (g:A->real^3^3) z) C' eps' U' Y'` THEN
  ASM_SIMP_TAC[P2BCS_CAP_CMUL]);;

(* ========================================================================= *)
(* Fresh caps, F5 (a): a set W open in the slice at ts that persists over   *)
(* no (ts - eta, ts] meets the closed core of a cap of an event at ts       *)
(* (P3H_EXPOSED_POINT, pc_p3_c172d, for T1 = ts).                            *)
(* ========================================================================= *)

let P3H_EXPOSED_AT = prove
 (`!(hs:(A)rfs_history) W ts.
     rfs_history_ok hs /\ &0 < ts /\ ts < rfs_horizon hs /\
     open_in (rfs_top_at hs ts) W /\
     ~(?eta0. &0 < eta0 /\ rfs_persists (rfs_view hs) W (ts - eta0) ts)
     ==> ?k i. 1 <= k /\ k <= hs_count hs /\ hs_time hs k = ts /\
               i IN ev_index(hs_event hs k) /\
               ~DISJOINT W (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "np"))))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) ts` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) k) W /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `open_in (rfs_top_at (hs:(A)rfs_history) ts) W` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[rfs_history_ok]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < ts /\
        (!s. a < s /\ s <= ts
             ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
                 open_in (rfs_top_at (hs:(A)rfs_history) s) W)
        ==> F`
  (LABEL_TAC "contra") THENL
   [X_GEN_TAC `a:real` THEN STRIP_TAC THEN USE_THEN "np" MP_TAC THEN
    REWRITE_TAC[] THEN EXISTS_TAC `ts - a` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)); P2C_RFS_VIEW_PARTS] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k = ts` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= t /\ ~(a < t) ==> a = t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN USE_THEN "contra" (MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k`) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) k = ts` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 0 = &0` SUBST1_TAC THENL
     [ASM_MESON_TAC[rfs_history_ok]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  SUBGOAL_THEN
   `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1)) (hs_metric hs (k - 1))
                 (hs_time hs k) (hs_top hs k,hs_atlas hs k) (hs_metric hs k)
                 (hs_event (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `k - 1 <= hs_count (hs:(A)rfs_history) /\ (k - 1) + 1 = k` STRIP_ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (hs_top hs (k - 1)) (hs_atlas (hs:(A)rfs_history) (k - 1))`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace(hs_top (hs:(A)rfs_history) (k - 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_CAPFREE_RETAINED THEN
    MAP_EVERY EXISTS_TAC [`hs_atlas (hs:(A)rfs_history) (k - 1)`;
                          `hs_metric (hs:(A)rfs_history) (k - 1)`;
                          `hs_time (hs:(A)rfs_history) k`; `hs_top (hs:(A)rfs_history) k`;
                          `hs_atlas (hs:(A)rfs_history) k`; `hs_metric (hs:(A)rfs_history) k`;
                          `hs_event (hs:(A)rfs_history) k`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capm")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `hs_metric (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                 `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k`; `hs_event (hs:(A)rfs_history) k`;
                 `W:A->bool`] P3S_EVENT_RETAINED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "contra" (MP_TAC o SPEC `hs_time (hs:(A)rfs_history) (k - 1)`) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs ((k - 1) + 1)` MP_TAC THENL
     [ASM_MESON_TAC[rfs_history_ok]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s:real = ts` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Fresh caps, F5 (b): a point Phi q of a fresh cap region at its event     *)
(* time with dist0(q) <= A0 + 4 + 1/eps lies in the core of a (C,eps)-cap  *)
(* of the stage (P3H_G0_CAPS, then P3H_CAP_TO_HIST_C with G0 = g0 and the   *)
(* closeness of p3_cap_param), once the surgery control is small.          *)
(* ========================================================================= *)

(* A twin of RFA_HC2_STD_DIST_OPEN of the unit pc_rfa_histc2c (same short   *)
(* proof: MFD_BALL_OPEN after unfolding).                                   *)

let P3H_STD_DIST_LT_OPEN = prove
 (`!g0 A0 m. p3_std_initial g0 A0 ==> open {y:real^3 | p3_std_dist g0 y < m}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y:real^3 | p3_std_dist g0 y < m} =
                mfd_ball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) m` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_ball; IN_ELIM_THM; P2C_RAD_JOINABLE; p3_std_dist]; ALL_TAC] THEN
  REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
  REWRITE_TAC[P2C_EUCLID_FACTS] THEN ASM_MESON_TAC[p3_std_initial]);;

let P3H_FRESH_CAPCASE = prove
 (`P2_THM_12_32_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_PROP_12_31_STATEMENT /\
   P3_STD_C2_BOUND_STATEMENT
   ==> ?eps0. &0 < eps0 /\
         !eps g0 A0. &0 < eps /\ eps <= eps0 /\ p3_std_initial g0 A0
           ==> ?C0. &1 < C0 /\
                 !C md. C0 <= C /\ p3_modulus md
                   ==> ?dbar. &0 < dbar /\
                         !dl h (hs:(A)rfs_history) k j Phi xi q.
                            rfs_history_ok hs /\ k <= hs_count hs /\
                            p3_cap_param (md,g0,A0) (dl,h) hs k j Phi xi /\
                            &0 < h(hs_time hs k) /\ &0 < dl(hs_time hs k) /\
                            dl(hs_time hs k) <= dbar /\
                            p3_std_dist g0 q <= A0 + &4 + inv eps
                            ==> ?U Y. rfs_cap (hs_top hs k,hs_atlas hs k)
                                              (hs_metric hs k (hs_time hs k)) C eps U Y /\
                                      Phi q IN Y`,
  STRIP_TAC THEN
  MP_TAC P3H_CAP_TO_HIST_C THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `ect:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CT"))))) THEN
  MP_TAC(MATCH_MP P3H_G0_CAPS (CONJ (ASSUME `P2_THM_12_32_STATEMENT`) (CONJ
    (ASSUME `P2_THM_12_5_STATEMENT`) (CONJ (ASSUME `P2_PROP_12_31_STATEMENT`)
    (ASSUME `P3_STD_C2_BOUND_STATEMENT`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `eg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G0C"))) THEN
  MP_TAC(ASSUME `P3_STD_C2_BOUND_STATEMENT`) THEN REWRITE_TAC[P3_STD_C2_BOUND_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C2"))) THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min ect (K * min eg ec2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_LT_MIN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps / K /\ eps / K <= eg /\ eps / K <= ec2 /\ K * eps / K = eps`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    SUBGOAL_THEN `K * min eg ec2 <= K * eg /\ K * min eg ec2 <= K * ec2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0 /\ riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "G0C" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps / K`;
                                     `A0 + &4 + inv eps`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAPS"))) THEN
  EXISTS_TAC `&2 * C1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `md:real->real`] THEN STRIP_TAC THEN
  REMOVE_THEN "C2" (MP_TAC o SPECL [`C1:real`; `eps / K`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KR"))) THEN
  REMOVE_THEN "CT" (MP_TAC o SPECL [`C1:real`; `eps / K`; `C:real`; `eps:real`; `Kr:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CT"))) THEN
  (* the fixed standard flow, the scalar lower bound c of Prop 12.31 at t = 0 *)
  MP_TAC(ASSUME `P2_THM_12_5_STATEMENT`) THEN REWRITE_TAC[P2_THM_12_5_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real->real^3->real^3^3` o CONJUNCT1) THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3) /\ G (&0) = g0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  MP_TAC(ASSUME `P2_PROP_12_31_STATEMENT`) THEN REWRITE_TAC[P2_PROP_12_31_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. c <= mfd_scalar (open_set_atlas (:real^3)) g0 x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `&0`; `x:real^3`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01; REAL_SUB_RZERO; REAL_DIV_1];
    ALL_TAC] THEN
  (* the size dd of the closeness region and of the closeness *)
  SUBGOAL_THEN `?dd. &0 < dd /\ dd <= delta /\
                     A0 + &4 + inv eps + &2 * C1 * inv(sqrt c) + &1 < inv dd /\
                     (&1 + inv c) pow (rfs_kreg delta) * dd pow 2 < delta pow 2`
  (X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THENL
   [ABBREV_TAC `P = (&1 + inv c) pow (rfs_kreg delta)` THEN
    SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_POW_LT THEN
      SUBGOAL_THEN `&0 < inv c` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `Lb = A0 + &4 + inv eps + &2 * C1 * inv(sqrt c) + &2` THEN
    SUBGOAL_THEN `&0 <= &2 * C1 * inv(sqrt c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Lb` ASSUME_TAC THENL [EXPAND_TAC "Lb" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `min delta (min (inv Lb) (delta / (P + &1)))` THEN
    SUBGOAL_THEN `&0 < inv Lb /\ &0 < delta / (P + &1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `dd = min delta (min (inv Lb) (delta / (P + &1)))` THEN
    SUBGOAL_THEN `&0 < dd /\ dd <= delta /\ dd <= inv Lb /\ dd <= delta / (P + &1)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `Lb <= inv dd` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "Lb" THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `dd pow 2 <= (delta / (P + &1)) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `P * (delta / (P + &1)) pow 2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `P * (delta / (P + &1)) pow 2 = (P / (P + &1) pow 2) * delta pow 2`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `~(P + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN
    SUBGOAL_THEN `&0 < (P + &1) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `&0 <= P * P` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `md (dd:real):real` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `p3_modulus md` THEN REWRITE_TAC[p3_modulus] THEN
    DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`dl:real->real`; `h:real->real`; `hs:(A)rfs_history`; `k:num`; `j:num`;
                       `Phi:real^3->A`; `xi:real^3->real^3`; `q:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < md(dd:real) /\ md dd <= dd` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_modulus md` THEN REWRITE_TAC[p3_modulus] THEN
    DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (hs_top (hs:(A)rfs_history) k) /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
                compact_space (hs_top hs k) /\
                riemannian_metric (hs_atlas hs k) (hs_metric hs k (hs_time hs k))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_time (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                   `hs_metric (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) k`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `p3_cap_param (md,g0,A0) (dl,h) (hs:(A)rfs_history) k j Phi xi`) THEN
  REWRITE_TAC[p3_cap_param] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dd:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_on")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_close_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CL"))) THEN
  (* the cap of g0 at q *)
  REMOVE_THEN "CAPS" (MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `Y:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q:real^3) IN U` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `C1:real`; `eps / K`; `U:real^3->bool`;
                   `Y:real^3->bool`] P2B_CAP_CORE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> p3_std_dist g0 y <= A0 + &4 + inv eps + &2 * C1 * inv(sqrt c)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `g0:real^3->real^3^3`; `C1:real`; `eps / K`;
                   `U:real^3->bool`; `Y:real^3->bool`; `q:real^3`; `c:real`] P3H_CAP_IN_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`z:real^3`; `v:real^3`] THEN
      MATCH_MP_TAC(REAL_ARITH `!a. &0 <= a ==> a <= &4 * a`) THEN
      ASM_CASES_TAC `v:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `g0:real^3->real^3^3`; `z:real^3`] RIEMANNIAN_METRIC_POS) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
      ANTS_TAC THENL
       [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
        ASM_SIMP_TAC[]];
      DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `W = {x:real^3 | p3_std_dist g0 x < inv dd /\
                              --(inv(dl(hs_time (hs:(A)rfs_history) k))) < A0 + &4 - p3_std_dist g0 x}` THEN
  SUBGOAL_THEN `inv dd <= inv(dl(hs_time (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `&2 * C1 * inv(sqrt c)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (W:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    SUBGOAL_THEN `{x:real^3 | p3_std_dist g0 x < inv dd /\
                              --(inv(dl(hs_time (hs:(A)rfs_history) k))) < A0 + &4 - p3_std_dist g0 x} =
                  {x | p3_std_dist g0 x < inv dd} INTER
                  {x | p3_std_dist g0 x < A0 + &4 + inv(dl(hs_time hs k))}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC P3H_STD_DIST_LT_OPEN THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (hs_top (hs:(A)rfs_history) k) (hs_atlas hs k) W Phi` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_param] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_TAC `Phi':A->real^3`) THEN REWRITE_TAC[mfd_param] THEN
    EXISTS_TAC `Phi':A->real^3` THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    EXISTS_TAC `{x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                            A0 + &4 - p3_std_dist g0 x}` THEN
    EXISTS_TAC `IMAGE (Phi:real^3->A) {x | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                                          A0 + &4 - p3_std_dist g0 x}` THEN
    ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN EXPAND_TAC "W" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) (g0:real^3->real^3^3)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(G:real->real^3->real^3^3) (&0) = g0`)) THEN
    MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_kreg delta <= rfs_kreg dd` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[RFS_KREG] THEN
    MATCH_MP_TAC FLOOR_MONO THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "CT" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `q:real^3`; `U:real^3->bool`; `Y:real^3->bool`;
     `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
     `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`; `h(hs_time (hs:(A)rfs_history) k):real`;
     `W:real^3->bool`; `Phi:real^3->A`; `d1:real`; `c:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REMOVE_THEN "KR" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `&0`; `q:real^3`;
                                        `U:real^3->bool`]) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      REWRITE_TAC[rfs_canonical_nbhd] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(&1 + inv c) pow (rfs_kreg delta) * dd pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN
      SUBGOAL_THEN `&0 < inv c` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg dd) g0
                    (\z. inv(h(hs_time (hs:(A)rfs_history) k) pow 2) %%
                         rfs_pullback (hs_atlas hs k) Phi (hs_metric hs k (hs_time hs k)) z) y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV];
          MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
           [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
            EXISTS_TAC `hs_top (hs:(A)rfs_history) k` THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]]];
        REMOVE_THEN "CL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y':A->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`U':A->bool`; `Y':A->bool`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Fresh caps, F5 (c): a point Phi q of the kept half of a surgery neck at  *)
(* its event time with dist0(q) > A0 + 4 + 1/eps is the centre of a strong  *)
(* eps-neck (P3H_FAR_RECENTRE with e1 = eps), once the control is small.    *)
(* ========================================================================= *)

let P3H_FRESH_NECKCASE = prove
 (`P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)
   ==> !eps g0 A0 L. &0 < eps /\ eps < &1 / &4 /\ p3_std_initial g0 A0
         ==> ?dbar. &0 < dbar /\
               !md dl h (hs:(A)rfs_history) k j Phi xi q.
                  rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\
                  1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                  p3_neck2_ok (dl,h) hs k /\ p3_cap_param (md,g0,A0) (dl,h) hs k j Phi xi /\
                  &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= dbar /\
                  A0 + &4 + inv eps < p3_std_dist g0 q /\ p3_std_dist g0 q <= L
                  ==> ?e. rfs_strong_neck (rfs_view hs) eps (Phi q) (hs_time hs k) e`,
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`; `L:real`] THEN
  STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:real^3`,`:A`] (MATCH_MP P2B9_NECK_CENTRE_UNIFORM P2B_REQ_LRG_RM_NEAR)) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THEN
  MP_TAC(SPEC `rfs_kreg eps` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M"))) THEN
  MP_TAC(SPECL [`&0`; `eps:real`; `M:real`; `K0:real`; `&1`; `&2`;
                `rfs_kreg eps + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delR:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(abs(L - (A0 + &4)) + inv eps + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?dbar. &0 < dbar /\ dbar <= delR /\
                       dbar <= inv(abs(L - (A0 + &4)) + inv eps + &1)`
  (X_CHOOSE_THEN `dbar:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min delR (inv(abs(L - (A0 + &4)) + inv eps + &1))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `dbar:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`md:real->real`; `dl:real->real`; `h:real->real`;
                       `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`;
                       `xi:real^3->real^3`; `q:real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`&0`; `eps:real`; `M:real`; `K0:real`; `&1`; `&2`;
                `rfs_kreg eps + 2`; `delR:real`;
                `dl(hs_time (hs:(A)rfs_history) k):real`] P3H_DELTA_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN ASM_REAL_ARITH_TAC;
                  STRIP_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (vec 0:real^3) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `~(q:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `A0 + &4 + inv eps < p3_std_dist g0 q` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(L - (A0 + &4)) + inv eps + &1 <=
                inv(dl(hs_time (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `M:real`; `eps:real`; `md:real->real`; `g0:real^3->real^3^3`;
                 `A0:real`; `dl:real->real`; `h:real->real`; `hs:(A)rfs_history`; `k:num`;
                 `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `q:real^3`]
                P3H_FAR_RECENTRE) THEN
  REWRITE_TAC[SQRT_0] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
  EXISTS_TAC `ev_neck (hs_event (hs:(A)rfs_history) k) j o
              (\v:real^3. norm(p3_std_nc g0 A0 q) % v)` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Fresh caps, F5 (d): if the ball B(x, ts, A R(x)^-1/2) on which R <= D R(x) *)
(* contains a point y of the closed core of a cap created at ts, then x has *)
(* a strong (C,eps)-canonical neighbourhood at ts, once the surgery control *)
(* is small: R(y) >= c h^-2 / 2 (Prop 12.31 at t = 0 through the closeness  *)
(* of p3_cap_param) bounds the radius by A sqrt(2D/c) h; the short curve    *)
(* from y to x lifts into the model (P3H_LIFT_SHORT_CURVE at s = 0, where   *)
(* g0 is the cylinder on the annulus); then P3H_FRESH_CAPCASE or            *)
(* P3H_FRESH_NECKCASE.                                                      *)
(* ========================================================================= *)

let P3H_171_FRESH = prove
 (`P2_THM_12_32_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_PROP_12_31_STATEMENT /\
   P3_STD_C2_BOUND_STATEMENT /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)
   ==> ?eps0. &0 < eps0 /\
         !eps g0 A0. &0 < eps /\ eps <= eps0 /\ p3_std_initial g0 A0
           ==> ?C0. &1 < C0 /\
                 !C md A D. C0 <= C /\ p3_modulus md /\ &0 < A /\ &0 < D
                   ==> ?dbar. &0 < dbar /\
                         !dl h (hs:(A)rfs_history) k j Phi xi x y.
                            rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\
                            1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                            p3_neck2_ok (dl,h) hs k /\
                            p3_cap_param (md,g0,A0) (dl,h) hs k j Phi xi /\
                            &0 < h(hs_time hs k) /\ &0 < dl(hs_time hs k) /\
                            dl(hs_time hs k) <= dbar /\
                            x IN topspace(hs_top hs k) /\
                            &0 < mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) x /\
                            y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                            mfd_joinable (hs_top hs k,hs_atlas hs k) x y /\
                            mfd_dist (hs_top hs k,hs_atlas hs k)
                              (hs_metric hs k (hs_time hs k)) x y <
                            A * inv(sqrt(mfd_scalar (hs_atlas hs k)
                                           (hs_metric hs k (hs_time hs k)) x)) /\
                            mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) y <=
                            D * mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) x
                            ==> (?U Y. rfs_cap (hs_top hs k,hs_atlas hs k)
                                                (hs_metric hs k (hs_time hs k)) C eps U Y /\
                                       x IN Y) \/
                                (?e. rfs_strong_neck (rfs_view hs) eps x (hs_time hs k) e)`,
  STRIP_TAC THEN
  MP_TAC(MATCH_MP P3H_FRESH_CAPCASE (CONJ (ASSUME `P2_THM_12_32_STATEMENT`) (CONJ
    (ASSUME `P2_THM_12_5_STATEMENT`) (CONJ (ASSUME `P2_PROP_12_31_STATEMENT`)
    (ASSUME `P3_STD_C2_BOUND_STATEMENT`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ec:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CC"))) THEN
  MP_TAC(MATCH_MP P3H_FRESH_NECKCASE
    (ASSUME `P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)`)) THEN
  DISCH_THEN(LABEL_TAC "NC") THEN
  EXISTS_TAC `min ec (&1 / &8)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  REMOVE_THEN "CC" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CC"))) THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `md:real->real`; `A:real`; `D:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "CC" (MP_TAC o SPECL [`C:real`; `md:real->real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CC"))) THEN
  SUBGOAL_THEN `&0 < A0 /\ riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  (* c: Prop 12.31 at t = 0 through a standard flow *)
  MP_TAC(ASSUME `P2_THM_12_5_STATEMENT`) THEN REWRITE_TAC[P2_THM_12_5_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real->real^3->real^3^3` o CONJUNCT1) THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3) /\ G (&0) = g0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  MP_TAC(ASSUME `P2_PROP_12_31_STATEMENT`) THEN REWRITE_TAC[P2_PROP_12_31_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. c <= lscalar (g0:real^3->real^3^3) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    SUBGOAL_THEN `lscalar (g0:real^3->real^3^3) x = mfd_scalar (open_set_atlas (:real^3)) g0 x`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFB_OPEN_SET_MFD_SCALAR THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `&0`; `x:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `c:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01; REAL_SUB_RZERO; REAL_DIV_1];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &4`] P3H_STD_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ds:real` STRIP_ASSUME_TAC) THEN
  (* the lift parameter el and the model radii *)
  SUBGOAL_THEN `&0 < sqrt(&2 * D / c)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `r1 = A * sqrt(&2 * D / c)` THEN
  SUBGOAL_THEN `&0 < r1` ASSUME_TAC THENL
   [EXPAND_TAC "r1" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `el = inv(&2 * r1 + &4)` THEN
  SUBGOAL_THEN `&0 < el /\ el <= &1 / &4 /\ inv el = &2 * r1 + &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "el" THEN REWRITE_TAC[REAL_INV_INV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `el:real` P3H_LIFT_SHORT_CURVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIFT"))) THEN
  REMOVE_THEN "NC" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`;
                                    `A0 + &5 + &2 * inv el`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dn:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NC"))) THEN
  (* the closeness parameter dd *)
  SUBGOAL_THEN `?dd. &0 < dd /\ dd <= &1 / &10 /\ dd <= el /\ dd <= dd0 /\
                     A0 + &5 + &2 * inv el + &2 <= inv dd /\
                     &72 * (&1 + abs Ds) * dd <= c / &2`
  (X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `&0 < c / (&144 * (&1 + abs Ds))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(A0 + &5 + &2 * inv el + &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN
      SUBGOAL_THEN `&0 < inv el` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `min (&1 / &10) (min el (min dd0 (min (inv(A0 + &5 + &2 * inv el + &2))
                  (c / (&144 * (&1 + abs Ds))))))` THEN
    ABBREV_TAC `dd = min (&1 / &10) (min el (min dd0 (min (inv(A0 + &5 + &2 * inv el + &2))
                       (c / (&144 * (&1 + abs Ds))))))` THEN
    SUBGOAL_THEN `&0 < dd /\ dd <= &1 / &10 /\ dd <= el /\ dd <= dd0 /\
                  dd <= inv(A0 + &5 + &2 * inv el + &2) /\
                  dd <= c / (&144 * (&1 + abs Ds))` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&72 * (&1 + abs Ds) * c / (&144 * (&1 + abs Ds))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&72 * (&1 + abs Ds) * c / (&144 * (&1 + abs Ds)) = c / &2`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      SUBGOAL_THEN `~(&1 + abs Ds = &0)` MP_TAC THENL
       [REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < md(dd:real) /\ md dd <= dd` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_modulus md` THEN REWRITE_TAC[p3_modulus] THEN
    DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?dbar. &0 < dbar /\ dbar <= dc /\ dbar <= dn /\ dbar <= md(dd:real)`
  (X_CHOOSE_THEN `dbar:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min dc (min dn (md(dd:real)))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `dbar:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`dl:real->real`; `h:real->real`; `hs:(A)rfs_history`; `k:num`; `j:num`;
                       `Phi:real^3->A`; `xi:real^3->real^3`; `x:A`; `y:A`] THEN
  STRIP_TAC THEN
  (* stage facts *)
  SUBGOAL_THEN `hausdorff_space (hs_top (hs:(A)rfs_history) k) /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
                riemannian_metric (hs_atlas hs k) (hs_metric hs k (hs_time hs k))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_time (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                   `hs_metric (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) k`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the cap parametrization and its closeness at dd *)
  MP_TAC(ASSUME `p3_cap_param (md,g0,A0) (dl,h) (hs:(A)rfs_history) k j Phi xi`) THEN
  REWRITE_TAC[p3_cap_param] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dd:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_on")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_close_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CL"))) THEN
  SUBGOAL_THEN `inv dd <= inv(dl(hs_time (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* y = Phi qy with qy in the cap region *)
  SUBGOAL_THEN `?qy:real^3. &0 <= A0 + &4 - p3_std_dist g0 qy /\ (Phi:real^3->A) qy = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) j) (cball(vec 0,&1))` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capm")) (concl th) &&
      is_eq(concl th))) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(Phi:real^3->A) qy = y`)) THEN
  ABBREV_TAC `Wd = {x:real^3 | p3_std_dist g0 x < inv dd /\
                               --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                               A0 + &4 - p3_std_dist g0 x}` THEN
  SUBGOAL_THEN `open (Wd:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Wd" THEN
    SUBGOAL_THEN `{x:real^3 | p3_std_dist g0 x < inv dd /\
                              --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                              A0 + &4 - p3_std_dist g0 x} =
                  {x | p3_std_dist g0 x < inv dd} INTER
                  {x | p3_std_dist g0 x < A0 + &4 + inv(dl(hs_time hs k))}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC P3H_STD_DIST_LT_OPEN THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!S:real^3->bool. open S /\
                 S SUBSET {x | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                               A0 + &4 - p3_std_dist g0 x}
                 ==> mfd_param (hs_top hs k) (hs_atlas hs k) S (Phi:real^3->A)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_param] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th) &&
      not (is_forall (concl th)))) THEN
    DISCH_THEN(X_CHOOSE_TAC `Phi':A->real^3`) THEN REWRITE_TAC[mfd_param] THEN
    EXISTS_TAC `Phi':A->real^3` THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    EXISTS_TAC `{x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                            A0 + &4 - p3_std_dist g0 x}` THEN
    EXISTS_TAC `IMAGE (Phi:real^3->A) {x | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                                          A0 + &4 - p3_std_dist g0 x}` THEN
    ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) (g0:real^3->real^3^3)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(G:real->real^3->real^3^3) (&0) = g0`)) THEN
    MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* R(y) >= c / (2 h^2) *)
  SUBGOAL_THEN `c / &2 <= h(hs_time (hs:(A)rfs_history) k) pow 2 *
                         mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k))
                                    ((Phi:real^3->A) qy)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`; `Wd:real^3->bool`;
                   `Phi:real^3->A`; `g0:real^3->real^3^3`;
                   `h(hs_time (hs:(A)rfs_history) k):real`; `qy:real^3`; `Ds:real`; `dd:real`]
                  P3H_PHI_SCALAR_AT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(qy:real^3) IN Wd` ASSUME_TAC THENL
       [EXPAND_TAC "Wd" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        SUBGOAL_THEN `&0 < inv(dl(hs_time (hs:(A)rfs_history) k))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Wd" THEN SET_TAC[];
        MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        SUBGOAL_THEN `lrm_deriv_norm2 0 (g0:real^3->real^3^3) qy <= Ds pow 2` MP_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `qy:real^3` o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `Ds:real`)) (concl th))) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[] THEN REMOVE_THEN "CL" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `qy:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th) &&
      can (find_term (fun t -> t = `c:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the radius of the ball is at most r1 h *)
  ABBREV_TAC `Q = mfd_scalar (hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k (hs_time hs k)) x` THEN
  ABBREV_TAC `hk = h(hs_time (hs:(A)rfs_history) k):real` THEN
  SUBGOAL_THEN `A * inv(sqrt Q) <= r1 * hk` ASSUME_TAC THENL
   [SUBGOAL_THEN `c / &2 <= hk pow 2 * (D * Q)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `hk pow 2 * mfd_scalar (hs_atlas (hs:(A)rfs_history) k)
                    (hs_metric hs k (hs_time hs k)) ((Phi:real^3->A) qy)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv Q <= (&2 * D / c) * hk pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv Q = &1 / Q` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `((&2 * D / c) * hk pow 2) * Q = (&2 / c) * (hk pow 2 * (D * Q))`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `&1 = (&2 / c) * (c / &2)` (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
       [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "r1" THEN
    SUBGOAL_THEN `inv(sqrt Q) <= sqrt(&2 * D / c) * hk` MP_TAC THENL
     [REWRITE_TAC[GSYM SQRT_INV] THEN
      SUBGOAL_THEN `sqrt(&2 * D / c) * hk = sqrt((&2 * D / c) * hk pow 2)` SUBST1_TAC THENL
       [REWRITE_TAC[SQRT_MUL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC POW_2_SQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      DISCH_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* a short curve from y = Phi qy to x *)
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`; `(Phi:real^3->A) qy`; `x:A`;
                 `r1 * hk`] APX_DIST_SHORT_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                     `x:A`; `(Phi:real^3->A) qy`] MFD_JOINABLE_SYM) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                     `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`; `x:A`;
                     `(Phi:real^3->A) qy`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  (* lift it into the model *)
  REMOVE_THEN "LIFT" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `hs_top (hs:(A)rfs_history) k`;
     `hs_atlas (hs:(A)rfs_history) k`; `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`;
     `Phi:real^3->A`; `A0 + &5 + &2 * inv el + &1`; `hk:real`; `g0:real^3->real^3^3`; `&0`;
     `A0 + &5 + inv el`; `dd:real`; `gamma:real->A`; `qy:real^3`]) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `A0 + &5 + &2 * inv el + &1 <= inv(dl(hs_time (hs:(A)rfs_history) k))`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `{x:real^3 | p3_std_dist g0 x < A0 + &5 + &2 * inv el + &1} SUBSET Wd`
    ASSUME_TAC THENL
     [EXPAND_TAC "Wd" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_param (hs_top (hs:(A)rfs_history) k) (hs_atlas hs k) Wd (Phi:real^3->A)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Wd" THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `rfs_kreg el <= rfs_kreg dd` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      SIMP_TAC[RFS_KREG; ASSUME `&0 < el`; ASSUME `&0 < dd`] THEN
      MATCH_MP_TAC FLOOR_MONO THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open {x:real^3 | A0 < p3_std_dist g0 x}` ASSUME_TAC THENL
     [SUBGOAL_THEN `{x:real^3 | A0 < p3_std_dist g0 x} =
                    (:real^3) DIFF {x | p3_std_dist g0 x <= A0}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC P3H_STD_REGION_COMPACT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* keep inv el unrewritten: the equation becomes two inequalities *)
    UNDISCH_TAC `inv el = &2 * r1 + &4` THEN
    DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP REAL_EQ_IMP_LE th) THEN
                         ASSUME_TAC(MATCH_MP REAL_EQ_IMP_LE (SYM th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[P3H_STD_DIST_LT_OPEN] THEN
      TRY(CONJ_TAC THENL
       [MATCH_MP_TAC P3H_STD_DIST_LT_OPEN THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
        ALL_TAC]) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN Wd` ASSUME_TAC THENL
       [UNDISCH_TAC `{x:real^3 | p3_std_dist g0 x < A0 + &5 + &2 * inv el + &1} SUBSET Wd` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg dd) g0
                    (\z. inv(hk pow 2) %%
                         rfs_pullback (hs_atlas (hs:(A)rfs_history) k) Phi
                                      (hs_metric hs k (hs_time hs k)) z) z` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `Wd:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV];
          MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
           [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
            EXISTS_TAC `hs_top (hs:(A)rfs_history) k` THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]]];
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[] THEN
        REMOVE_THEN "CL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`rfs_kreg el`; `mpullback (p3_std_nc g0 A0) (cylinder_flow (&0))`;
                     `g0:real^3->real^3^3`; `g0:real^3->real^3^3`; `g0:real^3->real^3^3`;
                     `{x:real^3 | A0 < p3_std_dist g0 x}`; `z:real^3`] LCK_DIST2_LOCAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
        UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
        DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[P2BL_LCK_DIST2_REFL] THEN
        ASM_SIMP_TAC[REAL_POW_LT]];
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `hk * sqrt(&1 - &0) / (&2 * el) = hk * (r1 + &2)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_SUB_RZERO; SQRT_1] THEN
        SUBGOAL_THEN `&2 * el = inv(r1 + &2)` SUBST1_TAC THENL
         [EXPAND_TAC "el" THEN UNDISCH_TAC `&0 < r1` THEN CONV_TAC REAL_FIELD;
          REWRITE_TAC[real_div; REAL_INV_INV; REAL_MUL_LID]];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `r1 * hk` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < hk * &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `cq:real->real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(gamma:real->A) (&1) = x`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(Phi:real^3->A) q = gamma (&1)`)) THEN
  ASM_CASES_TAC `p3_std_dist g0 q <= A0 + &4 + inv eps` THENL
   [DISJ1_TAC THEN REMOVE_THEN "CC" (MP_TAC o SPECL
      [`dl:real->real`; `h:real->real`; `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`;
       `xi:real^3->real^3`; `q:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISJ2_TAC THEN REMOVE_THEN "NC" (MP_TAC o SPECL
      [`md:real->real`; `dl:real->real`; `h:real->real`; `hs:(A)rfs_history`; `k:num`; `j:num`;
       `Phi:real^3->A`; `xi:real^3->real^3`; `q:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* N: closedness of kappa-noncollapsing at the bad time (MT p. 406: 'the    *)
(* condition of being kappa-non-collapsed is a closed constraint').  Helper *)
(* lemmas: quadratic-form comparisons pass from the preferred restricted    *)
(* chart to the preferred chart; open sets of a region agree in two slices  *)
(* related by the identity diffeomorphism; the two-sided metric comparison  *)
(* of a persisting region with |Rm| <= K (P2AP_METRIC_COMPARE) in terms of  *)
(* the slice metric at b and the pullback of the slice metric at s.         *)
(* ========================================================================= *)

let P3H_RESTRICT_QF = prove
 (`!top atlas W (F1:A->real^N^N) F2 z c.
     smooth_manifold_atlas top atlas /\ open_in top W /\ z IN W /\
     (!w. w dot (restrict_metric atlas W F1 z ** w) <=
          c * (w dot (restrict_metric atlas W F2 z ** w)))
     ==> !w. w dot (F1 z ** w) <= c * (w dot (F2 z ** w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `z:A`]
                MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `J = matrix(chart_jac (U:A->bool,phi:A->real^N)
                     (chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) z)` THEN
  SUBGOAL_THEN `!Fm:A->real^N^N. restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W Fm z =
                                transp J ** Fm z ** J`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[restrict_metric] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SND] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                   `phi:A->real^N`; `W:A->bool`; `Fm:A->real^N^N`; `z:A`]
                  MFDR_METRIC_LOCAL_RESTRICT_CHART) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[metric_local] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                   `phi:A->real^N`; `W:A->bool`; `z:A`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(J:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool,phi:A->real^N)`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`; `z:A`]
                  GRGE_CHART_JAC_INVERTIBLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CHART_AT]; SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN
  SUBGOAL_THEN `(J:real^N^N) ** (matrix_inv J ** w) = w` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REMOVE_THEN "H" (MP_TAC o SPEC `matrix_inv(J:real^N^N) ** w`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_REWRITE_TAC[]);;

let P3H_SUB_OPEN_SAME = prove
 (`!top1 (atlas1:((A->bool)#(A->real^N))->bool) top2 (atlas2:((A->bool)#(A->real^N))->bool)
    W S.
     mfd_diffeo top1 atlas1 W top2 atlas2 W (\y. y) (\y. y) /\ S SUBSET W
     ==> (open_in top1 S <=> open_in top2 S)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `W:A->bool`; `S:A->bool`] OPEN_IN_OPEN_SUBTOPOLOGY) THEN
  MP_TAC(ISPECL [`top2:A topology`; `W:A->bool`; `S:A->bool`] OPEN_IN_OPEN_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let P3H_VIEW_METRIC_COMPARE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K s y.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ &0 <= K /\
     (!t z. a < t /\ t <= b /\ z IN W
            ==> mfd_rm_norm (rfs_vatlas V t) (rfs_vmetric V t) z <= K) /\
     a < s /\ s < b /\ y IN W
     ==> !w. w dot (mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V s) (\y. y)
                                        (rfs_vmetric V s) y ** w) <=
             exp(&4 * K * (b - s)) * (w dot (rfs_vmetric V b y ** w)) /\
             w dot (rfs_vmetric V b y ** w) <=
             exp(&4 * K * (b - s)) *
             (w dot (mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V s) (\y. y)
                                         (rfs_vmetric V s) y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) /\ p2a_region V W a b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC P2CV_RV_SVS; MATCH_MP_TAC P2CV_RV_REGION] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w dot (p2a_rmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b s y ** w) <=
        exp(&4 * K * (b - s)) * (w dot (p2a_rmetric V W b b y ** w)) /\
        w dot (p2a_rmetric V W b b y ** w) <=
        exp(&4 * K * (b - s)) * (w dot (p2a_rmetric V W b s y ** w))`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2AP_METRIC_COMPARE THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[p3_vrm] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[P2AP_RMETRIC_VFAM; p2c_vfam] THEN BETA_TAC THEN
  SUBGOAL_THEN `~(s:real = b)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(GEN `w:real^3` (CONJUNCT1(SPEC `w:real^3` th))) THEN
                       ASSUME_TAC(GEN `w:real^3` (CONJUNCT2(SPEC `w:real^3` th)))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `y:A`]
                P2C_VIEW_LAST_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THEN
  MATCH_MP_TAC P3H_RESTRICT_QF THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) b`;
                        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) b`; `W:A->bool`] THEN
  ASM_REWRITE_TAC[ETA_AX]);;
let P3H_NONCOLL_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    kappa r0 ts x r d vB.
     p2c_regular_view V /\ (!t. compact_space (rfs_vtop V t)) /\ &0 < kappa /\
     x IN topspace(rfs_vtop V ts) /\ &0 < r /\ r <= r0 /\
     rfs_persists V (rfs_vball V ts x r) (ts - r pow 2) ts /\
     (!s y. ts - r pow 2 < s /\ s <= ts /\ y IN rfs_vball V ts x r
            ==> mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) y <= inv(r pow 2)) /\
     p3_noncoll_at V kappa r0 x (ts - r pow 2 * d / &2) /\
     &0 < d /\ d <= &1 / &48 /\
     mfd_has_volume (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) (rfs_vball V ts x r) vB
     ==> kappa * r pow 3 * (&1 - &12 * d) <= vB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                 t (y:A) rr. rfs_vball V' t y rr =
                             mfd_ball (rfs_vtop V' t,rfs_vatlas V' t) (rfs_vmetric V' t) y rr`
  (LABEL_TAC "VB") THENL
   [REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric]; ALL_TAC] THEN
  SUBGOAL_THEN `!(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                 (W:A->bool) a b.
                 rfs_persists V' W a b <=>
                 !s. a < s /\ s <= b
                     ==> smooth_manifold_atlas (rfs_vtop V' s) (rfs_vatlas V' s) /\
                         open_in (rfs_vtop V' s) W`
  (LABEL_TAC "PS") THENL
   [REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas]; ALL_TAC] THEN
  ABBREV_TAC `s = ts - r pow 2 * d / &2` THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `ts - r pow 2 < s /\ s < ts` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SUBGOAL_THEN `&0 < r pow 2 * d / &2 /\ r pow 2 * d / &2 < r pow 2` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
        ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s'. ts - r pow 2 < s' /\ s' <= ts
                     ==> smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s') (rfs_vatlas V s') /\
                         open_in (rfs_vtop V s') (rfs_vball V ts x r)`
  (LABEL_TAC "BO") THENL
   [UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (rfs_vball V ts x r) (ts - r pow 2) ts` THEN
    USE_THEN "PS" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "VB" (fun th -> RULE_ASSUM_TAC(fun a -> if concl a = concl th then a else REWRITE_RULE[th] a) THEN
                          REWRITE_TAC[th]) THEN
  ABBREV_TAC `B = mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r` THEN
  SUBGOAL_THEN `(x:A) IN B /\ open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts) B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]; MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s'. ts - r pow 2 < s' /\ s' <= ts
                     ==> mfd_diffeo (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s') (rfs_vatlas V s') B
                                    (rfs_vtop V ts) (rfs_vatlas V ts) B (\y:A. y) (\y. y)`
  (LABEL_TAC "DF") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `ts - r pow 2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) /\
                hausdorff_space (rfs_vtop V s) /\
                smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                riemannian_metric (rfs_vatlas V s) (rfs_vmetric V s)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)` ASSUME_TAC THENL
     [USE_THEN "BO" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2C_REGULAR_SLICE THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN B
        ==> !w. w dot (mfd_pullback_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts) (rfs_vatlas V s) (\y:A. y)
                                         (rfs_vmetric V s) y ** w) <=
              exp(&2 * d) * (w dot (rfs_vmetric V ts y ** w)) /\
              w dot (rfs_vmetric V ts y ** w) <=
              exp(&2 * d) *
              (w dot (mfd_pullback_metric (rfs_vatlas V ts) (rfs_vatlas V s) (\y. y)
                                          (rfs_vmetric V s) y ** w))`
  (LABEL_TAC "CMP") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 * d = &4 * inv(r pow 2) * (ts - s)` SUBST1_TAC THENL
     [EXPAND_TAC "s" THEN UNDISCH_TAC `&0 < r pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC P3H_VIEW_METRIC_COMPARE THEN
    MAP_EVERY EXISTS_TAC [`B:A->bool`; `ts - r pow 2`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `rho = r * (&1 - &2 * d) * exp(--d)` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= r /\ rho pow 2 <= r pow 2 * (&1 - &2 * d)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < exp(--d) /\ exp(--d) <= &1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - &2 * d /\ &1 - &2 * d <= &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - &2 * d) * exp(--d) /\ (&1 - &2 * d) * exp(--d) <= &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    EXPAND_TAC "rho" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `((&1 - &2 * d) * exp(--d)) pow 2 <= (&1 - &2 * d) * exp(--d)` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&1 - &2 * d) * exp(--d) <= &1 - &2 * d` MP_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts) (rfs_vatlas V ts) B
                           (rfs_vtop V s) (rfs_vatlas V s) B (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "DF" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s) x rho SUBSET B`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts)
                    (rfs_vtop V ts closure_of
                     mfd_ball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) x (r * (&1 - d)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    SUBGOAL_THEN `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts closure_of
                  mfd_ball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) x (r * (&1 - d))
                  SUBSET B`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_cball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts) (rfs_vmetric V ts) x (r * (&1 - d))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
        REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
        EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
        X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&0 < r * d` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts) (rfs_vmetric V ts) x (r * d)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(exp(&2 * d)) * rho <= sqrt(&1 - &0) * (r * (&1 - d) - r * d)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `sqrt(exp(&2 * d)) = exp d` SUBST1_TAC THENL
       [SUBGOAL_THEN `exp(&2 * d) = exp d pow 2` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_EXP_N]; ALL_TAC] THEN
        MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_EXP_POS_LE];
        ALL_TAC] THEN
      EXPAND_TAC "rho" THEN REWRITE_TAC[REAL_SUB_RZERO; SQRT_1; REAL_MUL_LID] THEN
      SUBGOAL_THEN `exp d * r * (&1 - &2 * d) * exp(--d) = r * (&1 - &2 * d) * (exp d * exp(--d))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_NEG_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!y v. y IN B
                        ==> (&1 - &0) * (v dot (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts y ** v)) <=
                            exp(&2 * d) *
                            (v dot (mfd_pullback_metric (rfs_vatlas V ts) (rfs_vatlas V s) (\y:A. y)
                                                        (rfs_vmetric V s) y ** v))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID] THEN
      USE_THEN "CMP" (MP_TAC o SPEC `y:A`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
                   `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `B:A->bool`; `B:A->bool`; `\y:A. y`; `\y:A. y`; `x:A`; `x:A`;
                   `r * (&1 - d)`; `r * d`; `exp(&2 * d)`; `&0`; `rho:real`; `q:A`]
                  LIM_PB_BALL_PREIMAGE) THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_LE_REFL; REAL_LT_01] THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < r * d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ts - r pow 2 < s - rho pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SUBGOAL_THEN `&0 < r pow 2 * d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `rho pow 2 <= r pow 2 * (&1 - &2 * d)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(r pow 2) <= inv(rho pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts) (mfd_ball (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s) x rho)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
                   `B:A->bool`; `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s) x rho`]
                  P3H_SUB_OPEN_SAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "DF" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?vs. mfd_has_volume (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s)
                       (mfd_ball (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s) x rho) vs /\
                     kappa * rho pow 3 <= vs`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_noncoll_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) kappa r0 x s` THEN
    REWRITE_TAC[p3_noncoll_at; rfs_parabolic_exists] THEN
    USE_THEN "VB" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "PS" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      USE_THEN "BO" (MP_TAC o SPEC `s':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s'`;
                     `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
                     `B:A->bool`; `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s) x rho`]
                    P3H_SUB_OPEN_SAME) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "DF" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`s'':real`; `y:A`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(r pow 2)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s) x rho SUBSET B`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_volume (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts) (rfs_vmetric V ts)
                  (mfd_ball (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s) x rho)
                  (mfd_volume (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts)
                     (mfd_ball (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s) x rho))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN
    EXISTS_TAC `topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts)` THEN
    ASM_REWRITE_TAC[GSYM compact_space] THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `vts = mfd_volume (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts) (rfs_vmetric V ts)
                     (mfd_ball (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s) x rho)` THEN
  SUBGOAL_THEN `exp(--(&2 * d)) * sqrt(exp(--(&2 * d))) * vs <= (&1 + &3 * &0) * vts`
  ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:A`,`:B`] LIM_VOL_IMAGE_UPPER) THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
      `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
      `B:A->bool`; `B:A->bool`; `\y:A. y`; `\y:A. y`;
      `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s) x rho`] THEN
    ASM_REWRITE_TAC[IMAGE_ID; REAL_EXP_POS_LT; REAL_LE_REFL; REAL_POS] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ADD_RID; REAL_MUL_LID] THEN
    SUBGOAL_THEN `(y:A) IN B` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s) x rho SUBSET B`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "CMP" (fun th -> MP_TAC(CONJUNCT1(SPEC `w:real^3`
      (MP (SPEC `y:A` th) (ASSUME `(y:A) IN B`))))) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * d)) * exp(&2 * d) *
                (w dot (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts y ** w))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL2; REAL_MUL_LID; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `vts <= vB` ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_MONO) THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s) (rfs_vmetric V s) x rho`;
      `B:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(exp(--(&2 * d))) = exp(--d)` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(--(&2 * d)) = exp(--d) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&2 * d)) * exp(--d) * (kappa * rho pow 3) =
                kappa * r pow 3 * (&1 - &2 * d) pow 3 * exp(--(&6 * d))` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(--(&6 * d)) = exp(--(&2 * d)) * exp(--d) * exp(--d) pow 3`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "rho" THEN REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `kappa * r pow 3 * (&1 - &2 * d) pow 3 * exp(--(&6 * d)) <= vB` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `vts:real` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * d)) * exp(--d) * vs` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      UNDISCH_TAC `exp(--(&2 * d)) * sqrt(exp(--(&2 * d))) * vs <= (&1 + &3 * &0) * vts` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - &12 * d <= (&1 - &2 * d) pow 3 * exp(--(&6 * d))` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= d * d /\ d * d * d <= d * d` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_SQUARE] THEN
      SUBGOAL_THEN `d * (d * d) <= &1 * (d * d)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 - &6 * d <= (&1 - &2 * d) pow 3` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 - &6 * d <= exp(--(&6 * d))` ASSUME_TAC THENL
     [MP_TAC(SPEC `--(&6 * d)` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - &6 * d) * (&1 - &6 * d)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `kappa * r pow 3 * (&1 - &2 * d) pow 3 * exp(--(&6 * d))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE]);;

let P3H_NONCOLL_CLOSED = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    kappa r0 ts x.
     p2c_regular_view V /\ (!t. compact_space (rfs_vtop V t)) /\ &0 < kappa /\
     x IN topspace(rfs_vtop V ts) /\
     (!s y. ts - r0 pow 2 < s /\ s < ts /\ y IN topspace(rfs_vtop V s)
            ==> p3_noncoll_at V kappa r0 y s)
     ==> p3_noncoll_at V kappa r0 x ts`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NC"))))) THEN
  GEN_REWRITE_TAC I [p3_noncoll_at] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                 t (y:A) rr. rfs_vball V' t y rr =
                             mfd_ball (rfs_vtop V' t,rfs_vatlas V' t) (rfs_vmetric V' t) y rr`
  (LABEL_TAC "VB") THENL
   [REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric]; ALL_TAC] THEN
  SUBGOAL_THEN `!(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                 (W:A->bool) a b.
                 rfs_persists V' W a b <=>
                 !s. a < s /\ s <= b
                     ==> smooth_manifold_atlas (rfs_vtop V' s) (rfs_vatlas V' s) /\
                         open_in (rfs_vtop V' s) W`
  (LABEL_TAC "PS") THENL
   [REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas]; ALL_TAC] THEN
  USE_THEN "VB" (fun th -> RULE_ASSUM_TAC(fun a -> if concl a = concl th then a
                                                   else REWRITE_RULE[th] a) THEN
                           REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rfs_parabolic_exists]) THEN
  USE_THEN "VB" (fun th -> RULE_ASSUM_TAC(fun a -> if concl a = concl th then a
                                                   else REWRITE_RULE[th] a)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?vB. mfd_has_volume (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts)
                                    (rfs_vmetric V ts)
                                    (mfd_ball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r) vB`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `mfd_volume (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts)
                           (rfs_vmetric V ts)
                           (mfd_ball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r)` THEN
    MATCH_MP_TAC LIM_OPEN_VOLUME THEN
    EXISTS_TAC `topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts)` THEN
    ASM_REWRITE_TAC[GSYM compact_space] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts)
                    (mfd_ball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r)`
    ASSUME_TAC THENL [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `vB:real` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= vB` ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_POS_LE) THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts`;
      `mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < kappa * r pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ d <= &1 / &48 /\
                    &12 * d * (kappa * r pow 3) = (kappa * r pow 3 - vB) / &4`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(kappa * r pow 3 - vB) / (&48 * kappa * r pow 3)` THEN
    SUBGOAL_THEN `&0 < &48 * kappa * r pow 3` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < kappa * r pow 3` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 2 * d / &2 /\ r pow 2 * d / &2 < r pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 <= r0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `kappa:real`; `r0:real`; `ts:real`; `x:A`; `r:real`; `d:real`; `vB:real`]
                P3H_NONCOLL_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                     (mfd_ball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r) (ts - r pow 2) ts` THEN
      USE_THEN "PS" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "NC" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                   (mfd_ball (rfs_vtop V ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r) (ts - r pow 2) ts` THEN
    USE_THEN "PS" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o SPEC `ts - r pow 2 * d / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(x:A) IN mfd_ball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ts,rfs_vatlas V ts) (rfs_vmetric V ts) x r` MP_TAC THENL
     [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  UNDISCH_TAC `&12 * d * (kappa * r pow 3) = (kappa * r pow 3 - vB) / &4` THEN
  UNDISCH_TAC `vB < kappa * r pow 3` THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* P and Claim 17.9 (MT p. 406): the infimum of persistence, and the       *)
(* trichotomy for a small ball around a point z of the worst bad slice:    *)
(* it persists over the Lemma 11.2 window, or its backward flow lines end  *)
(* in a surgery cap before ts (Lemma 17.7 case), or it meets a cap created *)
(* at ts itself (the fresh-cap case).                                       *)
(* ========================================================================= *)

let P3H_PERSIST_INF = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W T0 ts.
     T0 < ts /\ ~rfs_persists V W T0 ts
     ==> ?T1. T0 < T1 /\ T1 <= ts /\ rfs_persists V W T1 ts /\
              ~(?eta0. &0 < eta0 /\ rfs_persists V W (T1 - eta0) ts)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `W:A->bool`; `T0:real`; `ts:real`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `S = {s | T0 < s /\ s <= ts /\
                       ~(smooth_manifold_atlas ((TM:real->A topology) s) ((AT:real->((A->bool)#(A->real^3))->bool) s) /\
                         open_in (TM s) (W:A->bool))}` THEN
  SUBGOAL_THEN `(s0:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `ts:real` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `T1 = sup S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UB") (LABEL_TAC "LUB")) THEN
  SUBGOAL_THEN `T0 < T1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "UB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `T1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "LUB" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real) IN S` MP_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> USE_THEN "UB" (MP_TAC o C MATCH_MP th)) THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `eta0:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `T1 <= T1 - eta0` MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "LUB" MATCH_MP_TAC THEN
    X_GEN_TAC `s:real` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(smooth_manifold_atlas ((TM:real->A topology) s) ((AT:real->((A->bool)#(A->real^3))->bool) s) /\
                   open_in (TM s) (W:A->bool))` THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P3H_CONT_RIGHT_LE = prove
 (`!f a b M. a < b /\ f real_continuous_on real_interval[a,b] /\
             (!s. a < s /\ s <= b ==> f s <= M)
             ==> f a <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?d. &0 < d /\
                    (!x'. a <= x' /\ x' <= b /\ abs(x' - a) < d ==> abs(f x' - f a) < e)`
  (LABEL_TAC "EP") THENL
   [UNDISCH_TAC `f real_continuous_on real_interval[a,b]` THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real`) THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; real_continuous_withinreal; IN_REAL_INTERVAL; CONJ_ASSOC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  REMOVE_THEN "EP" (MP_TAC o SPEC `(f:real->real) a - M`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  SUBGOAL_THEN `?x'. a < x' /\ x' <= b /\ abs(x' - a) < d` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `a + min d (b - a) / &2` THEN
    SUBGOAL_THEN `&0 < min d (b - a) /\ min d (b - a) <= d /\ min d (b - a) <= b - a`
    MP_TAC THENL [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
                  REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "D" (MP_TAC o SPEC `x':real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P3H_OPEN_AT_EVENT = prove
 (`!(hs:(A)rfs_history) W k ts.
     rfs_history_ok hs /\ k <= hs_count hs /\ &0 <= hs_time hs k /\ hs_time hs k < ts /\
     ts < rfs_horizon hs /\ rfs_persists (rfs_view hs) W (hs_time hs k) ts
     ==> open_in (rfs_top_at hs (hs_time hs k)) W`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hs_time hs k < hs_time (hs:(A)rfs_history) (k + 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `?s. hs_time hs k < s /\ s <= ts /\ s < hs_time (hs:(A)rfs_history) (k + 1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min ts ((hs_time hs k + hs_time (hs:(A)rfs_history) (k + 1)) / &2)` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_top_at hs s = rfs_top_at (hs:(A)rfs_history) (hs_time hs k)` (SUBST1_TAC o SYM)
  THENL
   [REWRITE_TAC[rfs_top_at; rfs_live] THEN
    SUBGOAL_THEN `&0 <= s /\ s < hs_time (hs:(A)rfs_history) (hs_count hs + 1) /\
                  hs_time hs k < hs_time hs (hs_count hs + 1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ts < rfs_horizon (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_horizon] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `rfs_slab hs s = k /\ rfs_slab (hs:(A)rfs_history) (hs_time hs k) = k`
    (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC RFS_SLAB_UNIQUE THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_persists (rfs_view hs) (W:A->bool) (hs_time hs k) ts` THEN
  REWRITE_TAC[rfs_view; rfs_persists] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ASM_SIMP_TAC[]);;

let P3H_171_SMALLBALL = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x z D.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              z IN topspace(rfs_top_at hs ts) /\ &0 <= D /\
              rfs_vscalar (rfs_view hs) ts z <= D * rfs_vscalar (rfs_view hs) ts x /\
              inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < ts
              ==> (rfs_persists (rfs_view hs)
                     (rfs_vball (rfs_view hs) ts z
                        (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x))))
                     (ts - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) ts /\
                   !s y. ts - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < s /\
                         s <= ts /\
                         y IN rfs_vball (rfs_view hs) ts z
                                (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x)))
                         ==> rfs_vscalar (rfs_view hs) s y <=
                             &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x) \/
                  (?k j y. 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                           ts - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) <
                           hs_time hs k /\
                           hs_time hs k < ts /\
                           y IN rfs_vball (rfs_view hs) ts z
                                  (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x))) /\
                           y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                           p3_flowline hs y (hs_time hs k) ts /\
                           (!s. hs_time hs k <= s /\ s <= ts
                                ==> rfs_vscalar (rfs_view hs) s y <=
                                    &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) \/
                  (?k j y. 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                           hs_time hs k = ts /\
                           y IN rfs_vball (rfs_view hs) ts z
                                  (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x))) /\
                           y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_BACK_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BB"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                   (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  ABBREV_TAC `rr = inv(&2 * C * sqrt((D + &2) * Q))` THEN
  ABBREV_TAC `eta = inv(&16 * C * (D + &2) * Q)` THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) ts z rr` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rr /\ &0 < eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN EXPAND_TAC "eta" THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (rfs_top_at (hs:(A)rfs_history) ts) /\
                smooth_manifold_atlas (rfs_top_at hs ts) (rfs_atlas_at hs ts) /\
                riemannian_metric (rfs_atlas_at hs ts) (rfs_metric_at hs ts)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `ts:real`; `z:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) ts) W /\ (z:A) IN W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[rfs_vball; rfs_view] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ts` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W (ts - eta) ts` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    REMOVE_THEN "BB" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
       `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:real`;
       `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
       `ts:real`; `x:A`; `z:A`; `ts - eta`; `rr:real`; `D:real`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `ts - eta`; `ts:real`]
                P3H_PERSIST_INF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `T1:real = ts` THENL
   [DISJ2_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `ts:real`] P3H_EXPOSED_AT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  SUBGOAL_THEN `T1 < ts /\ &0 < T1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `T1:real`; `ts:real`] P3H_EXPOSED_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    REWRITE_RULE[DISJOINT] o check (fun th -> is_neg(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> concl th =
    `(y:A) IN W /\ y IN IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) j) (cball(vec 0,&1))`)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `y:A`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) T1) W` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `hs_time (hs:(A)rfs_history) k = T1`)) THEN
    MATCH_MP_TAC P3H_OPEN_AT_EVENT THEN EXISTS_TAC `ts:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3_flowline] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s':real = T1` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      UNDISCH_TAC `open_in (rfs_top_at (hs:(A)rfs_history) T1) W` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W T1 ts` THEN
      REWRITE_TAC[rfs_view; rfs_persists] THEN DISCH_THEN(MP_TAC o SPEC `s':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. T1 < s /\ s <= ts
                    ==> rfs_vscalar (rfs_view (hs:(A)rfs_history)) s y <= &2 * (D + &2) * Q`
  (LABEL_TAC "B1") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REMOVE_THEN "BB" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
       `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:real`;
       `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
       `ts:real`; `x:A`; `z:A`; `T1:real`; `rr:real`; `D:real`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = T1` THENL
   [ALL_TAC; USE_THEN "B1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MP_TAC(ISPECL [`\u. rfs_vscalar (rfs_view (hs:(A)rfs_history)) u y`; `T1:real`;
                 `(T1 + ts) / &2`; `&2 * (D + &2) * Q`] P3H_CONT_RIGHT_LE) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2C_VIEW_SCALAR_CONT_FROM THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `ts:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (rfs_view (hs:(A)rfs_history)) T1) W` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[rfs_view; rfs_vtop]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s'':real` THEN STRIP_TAC THEN USE_THEN "B1" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let P3H_171_CLAIM179 = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x A D.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              x IN topspace(rfs_top_at hs ts) /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              &0 < A /\ &0 <= D /\
              (!z. z IN rfs_vball (rfs_view hs) ts x
                          (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                   ==> rfs_vscalar (rfs_view hs) ts z <= D * rfs_vscalar (rfs_view hs) ts x) /\
              inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < ts
              ==> (rfs_persists (rfs_view hs)
                     (rfs_vball (rfs_view hs) ts x
                        (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                     (ts - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) ts /\
                   !s y. ts - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < s /\
                         s <= ts /\
                         y IN rfs_vball (rfs_view hs) ts x
                                (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                         ==> rfs_vscalar (rfs_view hs) s y <=
                             &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x) \/
                  (?k j y. 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                           ts - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) <
                           hs_time hs k /\
                           hs_time hs k < ts /\
                           y IN rfs_vball (rfs_view hs) ts x
                                  ((A + &1) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                           y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                           p3_flowline hs y (hs_time hs k) ts /\
                           (!s. hs_time hs k <= s /\ s <= ts
                                ==> rfs_vscalar (rfs_view hs) s y <=
                                    &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) \/
                  (?k j y. 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                           hs_time hs k = ts /\
                           y IN rfs_vball (rfs_view hs) ts x
                                  ((A + &1) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                           y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_SMALLBALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SB"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                   (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  ABBREV_TAC `rr = inv(&2 * C * sqrt((D + &2) * Q))` THEN
  ABBREV_TAC `eta = inv(&16 * C * (D + &2) * Q)` THEN
  ABBREV_TAC `BA = rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A * inv(sqrt Q))` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (rfs_top_at (hs:(A)rfs_history) ts) /\
                smooth_manifold_atlas (rfs_top_at hs ts) (rfs_atlas_at hs ts) /\
                riemannian_metric (rfs_atlas_at hs ts) (rfs_metric_at hs ts)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  (* the small balls lie in the (A+1)-ball *)
  SUBGOAL_THEN `rr <= inv(sqrt Q)` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
    REWRITE_TAC[SQRT_MUL] THEN
    SUBGOAL_THEN `&1 <= sqrt(D + &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &2 * C * sqrt(D + &2)` ASSUME_TAC THENL
     [SUBGOAL_THEN `C * &1 <= C * sqrt(D + &2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 * sqrt Q <= (&2 * C * sqrt(D + &2)) * sqrt Q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_MUL_LID; GSYM REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN BA
                    ==> rfs_vball (rfs_view (hs:(A)rfs_history)) ts z rr SUBSET
                        rfs_vball (rfs_view hs) ts x ((A + &1) * inv(sqrt Q))`
  (LABEL_TAC "SUB") THENL
   [X_GEN_TAC `z:A` THEN EXPAND_TAC "BA" THEN
    REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; SUBSET; IN_ELIM_THM] THEN
    STRIP_TAC THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (rfs_top_at hs ts,rfs_atlas_at hs ts) (rfs_metric_at hs ts) x z +
                mfd_dist (rfs_top_at (hs:(A)rfs_history) ts,rfs_atlas_at hs ts)
                         (rfs_metric_at hs ts) z y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) ts) BA /\ (x:A) IN BA`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "BA" THEN REWRITE_TAC[rfs_vball; rfs_view] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!z. z IN BA
        ==> rfs_persists (rfs_view (hs:(A)rfs_history)) (rfs_vball (rfs_view hs) ts z rr)
                         (ts - eta) ts /\
            !s y. ts - eta < s /\ s <= ts /\ y IN rfs_vball (rfs_view hs) ts z rr
                  ==> rfs_vscalar (rfs_view hs) s y <= &2 * (D + &2) * Q`
  THENL
   [DISJ1_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BU_BALL_PERSIST_UNION THEN ASM_REWRITE_TAC[rfs_view; rfs_vtop] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `&0 < eta` MP_TAC THENL
         [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_LT_INV THEN
          MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      EXISTS_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) ts y rr` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `eta:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_view; rfs_vball; rfs_vtop] THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at (hs:(A)rfs_history) ts)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) ts`; `BA:A->bool`] OPEN_IN_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LT_INV THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `eta:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at (hs:(A)rfs_history) ts)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) ts`; `BA:A->bool`] OPEN_IN_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[rfs_view; rfs_vball] THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:A` MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEG")) THEN
  REMOVE_THEN "SB" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:real`;
     `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
     `ts:real`; `x:A`; `z:A`; `D:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `open_in (rfs_top_at (hs:(A)rfs_history) ts) BA` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the first alternative of P3H_171_SMALLBALL was rewritten to F by NEG *)
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num`
                                (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)))
                              (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num`
                                (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)))) THENL
   [DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `y:A`] THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "SUB" (MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `y:A`] THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "SUB" (MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Prop 17.1, the counterexample sequence: one instance (a history at its   *)
(* first bad time ts with the worst bad point x, in the plain canonical     *)
(* notion that Lemma 11.2 and Thm 10.2 read), and MT Claim 17.9 for the     *)
(* sequence: for every A the ball B(x, ts, A R(x)^-1/2) persists over a     *)
(* backward window of rescaled length delta(A) with R <= K(A) R(x) on it,   *)
(* for all large indices, once caps in the window (Lemma 17.7) and caps     *)
(* created at ts (P3H_171_FRESH) are excluded.                              *)
(* ========================================================================= *)

(* In the unit pc_p3_c171a: p3h_inst. *)

let P3H_171_SEQ179_AT = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x A D N1.
              eps <= eps0 /\ &0 < p3_T i /\
              (!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
                     (dlt a,r a,rs' a,ks' a,dd a,hs a,ts a,x a)) /\
              (!B. ?N. !a. N <= a ==> B < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              &0 < A /\ &0 <= D /\
              (!a z. N1 <= a /\
                     z IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                            (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                     ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                         D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!Ap Dp tp. &0 < Ap /\ &0 < Dp /\ &0 < tp
                 ==> ?N. !a. N <= a
                         ==> ~(?y k j.
                                 y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                        (Ap * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                 1 <= k /\ k <= hs_count (hs a) /\ j IN ev_index(hs_event (hs a) k) /\
                                 ts a - tp * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) <=
                                 hs_time (hs a) k /\
                                 hs_time (hs a) k < ts a /\
                                 y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1)) /\
                                 p3_flowline (hs a) y (hs_time (hs a) k) (ts a) /\
                                 (!s. hs_time (hs a) k <= s /\ s <= ts a
                                      ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                          Dp * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
              (!A. &0 < A
                   ==> ?N. !a. N <= a
                           ==> ~(?k j y. 1 <= k /\ k <= hs_count (hs a) /\
                                         j IN ev_index(hs_event (hs a) k) /\
                                         hs_time (hs a) k = ts a /\
                                         y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                                (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                         y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1))))
              ==> ?N. !a. N <= a
                          ==> rfs_persists (rfs_view (hs a))
                                (rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                   (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))))
                                (ts a - inv(&16 * C * (D + &2)) *
                                        inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))
                                (ts a) /\
                              !s y. ts a - inv(&16 * C * (D + &2)) *
                                           inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) < s /\
                                    s <= ts a /\
                                    y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                           (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                    ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                        (&2 * (D + &2)) * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_CLAIM179) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C179"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "INST") (CONJUNCTS_THEN2 (LABEL_TAC "QINF")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H17") (LABEL_TAC "HF"))))))))) THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [USE_THEN "INST" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[p3h_inst] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `dl = inv(&16 * C * (D + &2))` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "H17" (MP_TAC o SPECL [`A + &1`; `&2 * (D + &2)`; `dl:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  REMOVE_THEN "HF" (MP_TAC o SPEC `A + &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  REMOVE_THEN "QINF" (MP_TAC o SPEC `dl * inv(p3_T i)`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N4:num`) THEN
  EXISTS_TAC `N1 + N2 + N3 + N4:num` THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  USE_THEN "INST" (MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) a)) (ts a) (x a)` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((r:num->real) a pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl * inv Q = inv(&16 * C * (D + &2) * Q)` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&16 * C * (D + &2) * Q) < ts (a:num)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `dl * inv Q = inv(&16 * C * (D + &2) * Q)`)) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `p3_T i` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `dl * inv(p3_T i) < Q` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `dl * inv(p3_T i)`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `dl * inv Q * Q < p3_T i * Q` MP_TAC THENL
     [SUBGOAL_THEN `dl * inv Q * Q = dl` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `dl * inv(p3_T i) * p3_T i = dl` (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THENL
       [UNDISCH_TAC `&0 < p3_T i` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      GEN_REWRITE_TAC (RAND_CONV) [REAL_MUL_SYM] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `Q:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "C179" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `(dlt:num->real) a`;
     `(rs':num->(num->real)) a`; `(ks':num->(num->real)) a`; `(dd:num->(num->real)) a`;
     `(hs:num->(A)rfs_history) a`; `(r:num->real) a`; `(ts:num->real) a`; `(x:num->A) a`;
     `A:real`; `D:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `z:A`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL [`y:A`; `k:num`; `j:num`]) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N3:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL [`k:num`; `j:num`; `y:A`]) THEN
    ASM_REWRITE_TAC[]]);;


let P3H_171_SEQ179 = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
              eps <= eps0 /\ &0 < p3_T i /\
              (!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
                     (dlt a,r a,rs' a,ks' a,dd a,hs a,ts a,x a)) /\
              (!B. ?N. !a. N <= a ==> B < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!A. &0 < A
                   ==> ?D N. &0 <= D /\
                             !a z. N <= a /\
                                   z IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                          (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                   ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                                       D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!Ap Dp tp. &0 < Ap /\ &0 < Dp /\ &0 < tp
                 ==> ?N. !a. N <= a
                         ==> ~(?y k j.
                                 y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                        (Ap * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                 1 <= k /\ k <= hs_count (hs a) /\ j IN ev_index(hs_event (hs a) k) /\
                                 ts a - tp * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) <=
                                 hs_time (hs a) k /\
                                 hs_time (hs a) k < ts a /\
                                 y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1)) /\
                                 p3_flowline (hs a) y (hs_time (hs a) k) (ts a) /\
                                 (!s. hs_time (hs a) k <= s /\ s <= ts a
                                      ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                          Dp * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
              (!A. &0 < A
                   ==> ?N. !a. N <= a
                           ==> ~(?k j y. 1 <= k /\ k <= hs_count (hs a) /\
                                         j IN ev_index(hs_event (hs a) k) /\
                                         hs_time (hs a) k = ts a /\
                                         y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                                (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                         y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1))))
              ==> !A. &0 < A
                      ==> ?dl K N. &0 < dl /\ &0 < K /\
                            !a. N <= a
                                ==> rfs_persists (rfs_view (hs a))
                                      (rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                         (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))))
                                      (ts a - dl * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))
                                      (ts a) /\
                                    !s y. ts a - dl * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) < s /\
                                          s <= ts a /\
                                          y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                          ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                              K * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_SEQ179_AT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AT"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capm")) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "AT" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
       `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
       `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
       `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `A:real`; `D:real`; `N1:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MAP_EVERY EXISTS_TAC [`inv(&16 * C * (D + &2))`; `&2 * (D + &2)`; `N:num`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]);;

let P3H_171_SEQ179U = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
              eps <= eps0 /\ &0 < p3_T i /\
              (!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
                     (dlt a,r a,rs' a,ks' a,dd a,hs a,ts a,x a)) /\
              (!B. ?N. !a. N <= a ==> B < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (?D. &0 <= D /\
                   !A. &0 < A
                       ==> ?N. !a z. N <= a /\
                                     z IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                            (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                     ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                                         D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!Ap Dp tp. &0 < Ap /\ &0 < Dp /\ &0 < tp
                 ==> ?N. !a. N <= a
                         ==> ~(?y k j.
                                 y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                        (Ap * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                 1 <= k /\ k <= hs_count (hs a) /\ j IN ev_index(hs_event (hs a) k) /\
                                 ts a - tp * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) <=
                                 hs_time (hs a) k /\
                                 hs_time (hs a) k < ts a /\
                                 y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1)) /\
                                 p3_flowline (hs a) y (hs_time (hs a) k) (ts a) /\
                                 (!s. hs_time (hs a) k <= s /\ s <= ts a
                                      ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                          Dp * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
              (!A. &0 < A
                   ==> ?N. !a. N <= a
                           ==> ~(?k j y. 1 <= k /\ k <= hs_count (hs a) /\
                                         j IN ev_index(hs_event (hs a) k) /\
                                         hs_time (hs a) k = ts a /\
                                         y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                                (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                         y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1))))
              ==> ?dl K. &0 < dl /\ &0 < K /\
                         !A. &0 < A
                             ==> ?N.
                            !a. N <= a
                                ==> rfs_persists (rfs_view (hs a))
                                      (rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                         (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))))
                                      (ts a - dl * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))
                                      (ts a) /\
                                    !s y. ts a - dl * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) < s /\
                                          s <= ts a /\
                                          y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                          ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                              K * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_SEQ179_AT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AT"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "UB" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capm")) (concl th)))) THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(&16 * C * (D + &2))`; `&2 * (D + &2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  REMOVE_THEN "UB" (MP_TAC o SPEC `A:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  REMOVE_THEN "AT" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
       `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
       `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
       `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `A:real`; `D:real`; `N1:num`]) THEN
  ASM_REWRITE_TAC[]);;

(* MT Claim 17.9 pointwise: backward flow lines of rescaled length          *)
(* mu / max(Q, R(y)), mu = 1/(64 C), from the points y of every A-ball, for *)
(* large indices (the flow-line clause of p3_blowup_seq).                   *)

let P3H_171_SEQ_FLOW = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
              eps <= eps0 /\ &0 < p3_T i /\
              (!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
                     (dlt a,r a,rs' a,ks' a,dd a,hs a,ts a,x a)) /\
              (!B. ?N. !a. N <= a ==> B < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!A. &0 < A
                   ==> ?D N. &0 <= D /\
                             !a z. N <= a /\
                                   z IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                          (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                   ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                                       D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!Ap Dp tp. &0 < Ap /\ &0 < Dp /\ &0 < tp
                 ==> ?N. !a. N <= a
                         ==> ~(?y k j.
                                 y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                        (Ap * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                 1 <= k /\ k <= hs_count (hs a) /\ j IN ev_index(hs_event (hs a) k) /\
                                 ts a - tp * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) <=
                                 hs_time (hs a) k /\
                                 hs_time (hs a) k < ts a /\
                                 y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1)) /\
                                 p3_flowline (hs a) y (hs_time (hs a) k) (ts a) /\
                                 (!s. hs_time (hs a) k <= s /\ s <= ts a
                                      ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                          Dp * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
              (!A. &0 < A
                   ==> ?N. !a. N <= a
                           ==> ~(?k j y. 1 <= k /\ k <= hs_count (hs a) /\
                                         j IN ev_index(hs_event (hs a) k) /\
                                         hs_time (hs a) k = ts a /\
                                         y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                                (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                         y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1))))
              ==> !A. &0 < A
                      ==> ?N. !a y. N <= a /\
                                    y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                           (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                    ==> p3_flowline (hs a) y
                                          (ts a - inv(&64 * C) *
                                                  inv(max (rfs_vscalar (rfs_view (hs a)) (ts a) (x a))
                                                          (rfs_vscalar (rfs_view (hs a)) (ts a) y)))
                                          (ts a)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_SMALLBALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SB"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "INST") (CONJUNCTS_THEN2 (LABEL_TAC "QINF")
    (CONJUNCTS_THEN2 (LABEL_TAC "BALL") (CONJUNCTS_THEN2 (LABEL_TAC "H17") (LABEL_TAC "HF"))))))) THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  REMOVE_THEN "BALL" (MP_TAC o SPEC `A:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [USE_THEN "INST" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[p3h_inst] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "H17" (MP_TAC o SPECL [`A + &1`; `&2 * (D + &2)`; `inv(&16 * C * &2)`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  REMOVE_THEN "HF" (MP_TAC o SPEC `A + &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  REMOVE_THEN "QINF" (MP_TAC o SPEC `inv(&16 * C * &2) * inv(p3_T i)`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N4:num`) THEN
  EXISTS_TAC `N1 + N2 + N3 + N4:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "INST" (MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) a)) (ts a) (x a)` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((r:num->real) a pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  ABBREV_TAC `Ry = rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) a)) (ts a) y` THEN
  SUBGOAL_THEN `Ry <= D * Q` ASSUME_TAC THENL
   [EXPAND_TAC "Ry" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `y:A`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?Dy. &0 <= Dy /\ Ry <= Dy * Q /\ Dy <= D /\ (Dy + &2) * Q <= &3 * max Q Ry`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `Q <= max Q Ry /\ Ry <= max Q Ry` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_MAX] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&0 <= Ry` THENL
     [EXISTS_TAC `Ry / Q` THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_DIV_RMUL;
                                           REAL_LT_IMP_NZ; REAL_LE_REFL; REAL_LE_LDIV_EQ;
                                           REAL_ADD_RDISTRIB] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < max Q Ry` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_MAX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) a))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) ((dlt:num->real) a)
                   ((rs':num->num->real) a,(ks':num->num->real) a,(dd:num->num->real) a)
                   ((hs:num->(A)rfs_history) a)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (rfs_top_at ((hs:num->(A)rfs_history) a) (ts a)) /\
                smooth_manifold_atlas (rfs_top_at (hs a) (ts a)) (rfs_atlas_at (hs a) (ts a)) /\
                riemannian_metric (rfs_atlas_at (hs a) (ts a)) (rfs_metric_at (hs a) (ts a))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) a)`; `(ts:num->real) a`; `(x:num->A) a`]
                  P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at ((hs:num->(A)rfs_history) a) (ts a))` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) a)) (ts a) (x a) (A * inv(sqrt Q))` THEN
    REWRITE_TAC[rfs_vball; rfs_view] THEN
    MP_TAC(ISPECL [`rfs_top_at ((hs:num->(A)rfs_history) a) (ts a)`; `rfs_atlas_at ((hs:num->(A)rfs_history) a) (ts a)`;
                   `rfs_metric_at ((hs:num->(A)rfs_history) a) (ts a)`; `(x:num->A) a`; `A * inv(sqrt Q)`]
                  P2CU_BALL_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&64 * C) * inv(max Q Ry)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&64 * C) * inv(max Q Ry) < inv(&16 * C * (Dy + &2) * Q) /\
                inv(&16 * C * (Dy + &2) * Q) <= inv(&16 * C * &2) * inv Q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &16 * C * (Dy + &2) * Q` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(&16 * C) * ((Dy + &2) * Q) < (&16 * C) * (&4 * max Q Ry)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(&16 * C) * (&2 * Q) <= (&16 * C) * ((Dy + &2) * Q)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&16 * C * &2) * inv Q < ts (a:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `p3_T i` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&16 * C * &2) * inv(p3_T i) < Q` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `N4:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `c0 = inv(&16 * C * &2)` THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    MESON_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  REMOVE_THEN "SB" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `(dlt:num->real) a`;
     `(rs':num->(num->real)) a`; `(ks':num->(num->real)) a`; `(dd:num->(num->real)) a`;
     `(hs:num->(A)rfs_history) a`; `(r:num->real) a`; `(ts:num->real) a`; `(x:num->A) a`;
     `y:A`; `Dy:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `rr = inv(&2 * C * sqrt((Dy + &2) * Q))` THEN
  SUBGOAL_THEN `&0 < rr /\ rr <= inv(sqrt Q)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
      REWRITE_TAC[SQRT_MUL] THEN
      SUBGOAL_THEN `&1 <= sqrt(Dy + &2)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= &2 * C * sqrt(Dy + &2)` ASSUME_TAC THENL
       [SUBGOAL_THEN `C * &1 <= C * sqrt(Dy + &2)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 * sqrt Q <= (&2 * C * sqrt(Dy + &2)) * sqrt Q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_MUL_LID; GSYM REAL_MUL_ASSOC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball (rfs_view ((hs:num->(A)rfs_history) a)) (ts a) y rr SUBSET
                rfs_vball (rfs_view (hs a)) (ts a) (x a) ((A + &1) * inv(sqrt Q))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) a)) (ts a) (x a) (A * inv(sqrt Q))` THEN
    REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; SUBSET; IN_ELIM_THM] THEN
    STRIP_TAC THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (rfs_top_at ((hs:num->(A)rfs_history) a) (ts a),rfs_atlas_at (hs a) (ts a))
                         (rfs_metric_at (hs a) (ts a)) (x a) y +
                mfd_dist (rfs_top_at (hs a) (ts a),rfs_atlas_at (hs a) (ts a))
                         (rfs_metric_at (hs a) (ts a)) y w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (Dy + &2) * Q <= &2 * (D + &2) * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [REWRITE_TAC[p3_flowline] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_persists (rfs_view ((hs:num->(A)rfs_history) a))
                   (rfs_vball (rfs_view (hs a)) (ts a) y rr)
                   (ts a - inv(&16 * C * (Dy + &2) * Q)) (ts a)` THEN
    REWRITE_TAC[rfs_view; rfs_persists] THEN DISCH_THEN(MP_TAC o SPEC `s':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[rfs_vball] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL [`y':A`; `k:num`; `j:num`]) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `A + &1`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * (Dy + &2) * Q` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N3:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL [`k:num`; `j:num`; `y':A`]) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `A + &1`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Prop 17.1: |Rm| from R under pinching, and the blow-up sequence of the  *)
(* counterexamples (the hypotheses of Thm 11.8, p3_blowup_seq): canonical   *)
(* neighbourhoods above 4 Q at earlier times (worst bad point), kappa-     *)
(* noncollapsing at the bad time (16.1 and closedness, as a hypothesis      *)
(* here) and backward flow lines of length 1/(64 C) / max(Q, R(y)).        *)
(* ========================================================================= *)

(* In the unit pc_p3_c171a: P3H_RM_FROM_R. *)

let P3H_171_BLOWUP_SEQ = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa.
     &0 < kappa /\
     (!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
            (dlt a,r a,rs' a,ks' a,dd a,hs a,ts a,x a)) /\
     (!B. ?N. !a. N <= a ==> B < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
     (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
              ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
     (!A. &0 < A
          ==> ?N. !a y. N <= a /\
                        y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                               (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                        ==> p3_flowline (hs a) y
                              (ts a - inv(&64 * C) *
                                      inv(max (rfs_vscalar (rfs_view (hs a)) (ts a) (x a))
                                              (rfs_vscalar (rfs_view (hs a)) (ts a) y)))
                              (ts a))
     ==> p3_blowup_seq (C,eps,kappa,eps,inv(&64 * C)) hs x ts`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "INST")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "NC") (LABEL_TAC "FL"))))) THEN
  REWRITE_TAC[p3_blowup_seq] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 <= C /\ &0 < eps` STRIP_ASSUME_TAC THENL
   [USE_THEN "INST" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[p3h_inst] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `n:num` THEN USE_THEN "INST" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) ((dlt:num->real) n)
                   ((rs':num->num->real) n,(ks':num->num->real) n,(dd:num->num->real) n)
                   ((hs:num->(A)rfs_history) n)` THEN
    SIMP_TAC[p3_step_hyp; p3_struct];
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "INST" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                   `ds:num->real`; `(dlt:num->real) n`; `(rs':num->num->real) n`;
                   `(ks':num->num->real) n`; `(dd:num->num->real) n`;
                   `(hs:num->(A)rfs_history) n`; `(r:num->real) n`; `(ts:num->real) n`;
                   `(x:num->A) n`; `&4`] P3H_171_CANON_ABOVE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `A:real` THEN
    REMOVE_THEN "FL" (MP_TAC o SPEC `max A (&1)`) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MAX] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < inv(sqrt(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n)))`
    ASSUME_TAC THENL
     [USE_THEN "INST" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((r:num->real) n pow 2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n)
                    (max A (&1) * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))`
    ASSUME_TAC THENL
     [ABBREV_TAC `q = inv(sqrt(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n)))` THEN
      UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n) (A * q)` THEN
      REWRITE_TAC[rfs_vball; rfs_view] THEN
      MATCH_MP_TAC(SET_RULE `!s t (y:A). s SUBSET t ==> y IN s ==> y IN t`) THEN
      MATCH_MP_TAC P2BC_BALL_MONO THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_MAX] THEN REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "NC" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n)
                     (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))` THEN
      REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The A-dependent backward regions of the counterexamples in the form of   *)
(* the Part 2C Thm 11.1 machinery (P2BU_SEQ_SHI, P2BU_SEQ_VOL): Claim 17.9  *)
(* with |Rm| from R by pinching.                                            *)

let P3H_171_REGION = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
              eps <= eps0 /\ &0 < p3_T i /\
              (!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
                     (dlt a,r a,rs' a,ks' a,dd a,hs a,ts a,x a)) /\
              (!B. ?N. !a. N <= a ==> B < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!A. &0 < A
                   ==> ?D N. &0 <= D /\
                             !a z. N <= a /\
                                   z IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                          (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                   ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                                       D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
              (!Ap Dp tp. &0 < Ap /\ &0 < Dp /\ &0 < tp
                 ==> ?N. !a. N <= a
                         ==> ~(?y k j.
                                 y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                        (Ap * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                 1 <= k /\ k <= hs_count (hs a) /\ j IN ev_index(hs_event (hs a) k) /\
                                 ts a - tp * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) <=
                                 hs_time (hs a) k /\
                                 hs_time (hs a) k < ts a /\
                                 y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1)) /\
                                 p3_flowline (hs a) y (hs_time (hs a) k) (ts a) /\
                                 (!s. hs_time (hs a) k <= s /\ s <= ts a
                                      ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                          Dp * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
              (!A. &0 < A
                   ==> ?N. !a. N <= a
                           ==> ~(?k j y. 1 <= k /\ k <= hs_count (hs a) /\
                                         j IN ev_index(hs_event (hs a) k) /\
                                         hs_time (hs a) k = ts a /\
                                         y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                                (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                                         y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1))))
              ==> !A. &0 < A
                      ==> ?dl K N. &0 < dl /\ &0 < K /\
                            !n. N <= n
                                ==> &1 <= rfs_vscalar (rfs_view (hs n)) (ts n) (x n) /\
                                    rfs_persists (rfs_view (hs n))
                                      (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                         (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                      (ts n - dl / rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) (ts n) /\
                                    !s y. ts n - dl / rfs_vscalar (rfs_view (hs n)) (ts n) (x n) < s /\
                                          s <= ts n /\
                                          y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                          ==> &0 <= s /\ y IN topspace(rfs_vtop (rfs_view (hs n)) s) /\
                                              p3_vrm (rfs_view (hs n)) s y <=
                                              K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_SEQ179) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S179"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  REMOVE_THEN "S179" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `A:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `B:real`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MAP_EVERY EXISTS_TAC [`dl:real`; `&2 * K + &12 + &2 * exp(&4)`; `N1 + N2:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `&4` REAL_EXP_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at ((hs:num->(A)rfs_history) n) s)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view ((hs:num->(A)rfs_history) n))
                   (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                      (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                   (ts n - dl * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))) (ts n)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_view]) THEN
    REWRITE_TAC[rfs_view; rfs_persists] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_view; rfs_vtop] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[P3H_TOPSPACE_TIME_POS]; ALL_TAC] THEN
  REWRITE_TAC[GSYM rfs_view] THEN
  MP_TAC(ISPEC `u:A->bool` P3H_RM_FROM_R) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst; p3_step_hyp; p3_struct] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst; p3_step_hyp; p3_struct] THEN SIMP_TAC[];
    MATCH_MP_TAC P3H_TOPSPACE_TIME_POS THEN
    MAP_EVERY EXISTS_TAC [`(hs:num->(A)rfs_history) n`; `y:A`] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K:real`)) (concl th))) THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Prop 17.1, the counterexample sequence as one predicate (instances, Q to *)
(* infinity, the Thm 10.2 ball bounds, no Lemma 17.7 configuration and no   *)
(* fresh cap near x for large indices), its passage to subsequences, and    *)
(* the start of the T' argument (MT Claims 17.10-17.11 at time 0): along a  *)
(* subsequence the balls B(x, ts, A Q^-1/2) persist over one backward       *)
(* window dl/Q for every A (time-0 slice limit, Prop 9.79 for the canonical *)
(* neighbourhoods of the limit, Prop 2.19 for its bounded curvature, then   *)
(* Lemma 11.2 with the uniform bound).                                       *)
(* ========================================================================= *)

(* In the unit pc_p3_c171a: p3h_cexseq, P3H_SUBSEQ_GE, P3H_CEXSEQ_SUBSEQ. *)

(* The Claim 17.9 lemmas in packaged form. *)

let P3H_171_REGION_CEX = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
              eps <= eps0 /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x)
              ==> !A. &0 < A
                      ==> ?dl K N. &0 < dl /\ &0 < K /\
                            !n. N <= n
                                ==> &1 <= rfs_vscalar (rfs_view (hs n)) (ts n) (x n) /\
                                    rfs_persists (rfs_view (hs n))
                                      (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                         (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                      (ts n - dl / rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) (ts n) /\
                                    !s y. ts n - dl / rfs_vscalar (rfs_view (hs n)) (ts n) (x n) < s /\
                                          s <= ts n /\
                                          y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                          ==> &0 <= s /\ y IN topspace(rfs_vtop (rfs_view (hs n)) s) /\
                                              p3_vrm (rfs_view (hs n)) s y <=
                                              K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_REGION) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[p3h_cexseq] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`] o check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `A:real`) THEN ASM_REWRITE_TAC[]);;

let P3H_171_SEQ179U_CEX = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x D.
              eps <= eps0 /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
              &0 <= D /\
              (!A. &0 < A
                   ==> ?N. !a z. N <= a /\
                                 z IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                        (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                                 ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                                     D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a))
              ==> ?dl. &0 < dl /\
                       !A. &0 < A
                           ==> ?N. !a. N <= a
                                   ==> rfs_persists (rfs_view (hs a))
                                         (rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                            (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))))
                                         (ts a - dl * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))
                                         (ts a)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_SEQ179U) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[p3h_cexseq] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`] o check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `dl:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  ASM_SIMP_TAC[]);;

