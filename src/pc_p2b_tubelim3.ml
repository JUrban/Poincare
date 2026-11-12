(* ========================================================================= *)
(* pc_p2b_tubelim3: the chain and the summability on the limit side of the   *)
(* bad tube (MT Sec 10.3, Claims 10.8-10.9): P2BTL_LIM_CHAIN (a one-sided    *)
(* infinite chain of 2 eps-necks in the limit, by APXN_GROW2 on the          *)
(* component of the neck centres through a deep point, on which R is         *)
(* unbounded) and P2BTL_LIM_SUMMABLE (the scales of such a chain are         *)
(* summable: crossing gains of the transferred necks in the approximants     *)
(* against the diameter bound 2 A1 of the cut sets).  The last unit of the   *)
(* chain pc_p2b_tubelim, pc_p2b_tubelim2, pc_p2b_tubelim3, which together    *)
(* prove the five limit-side statements of pc_p2b_tubelimst.                 *)
(* ========================================================================= *)

needs "src/pc_p2b_tubelim2.ml";;
needs "src/pc_apx_ncends.ml";;
needs "src/pc_p2b_conelib.ml";;
needs "src/pc_apx_mincs.ml";;   (* APXM_A6_CS: A.6 at every type *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* One approximant.  Scalar curvature at least 100 C^2 on a window neck     *)
(* puts sig at arc length at least 6/5 h0 / eps beyond the level s0, with  *)
(* h0 = 1 / sqrt(32 C^2) (P2BT_PROFILE_NEAR_R twice, with K = 36 C^2 and    *)
(* K = 64 C^2).                                                              *)
(* ------------------------------------------------------------------------- *)

let P2BTL_BEYOND_LEVEL2 = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      gamma s0 s1 EN sig y.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= sig /\ sig <= s1 /\ y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
        &100 * C pow 2 <= mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN sig y)
        ==> &6 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps <=
            (sig - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                  (gamma(&0)) (gamma(&1))`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pn"))
    (INST_TYPE [`:A`,`:A`] P2BT_PROFILE_NEAR_R) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min e0 e1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm c1 one sg0 sg1 ys r100" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C /\ &0 < C pow 2 /\ &0 < inv C * inv eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) /\
    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) s0) = &32 * C pow 2 /\
    &0 < s0 /\ s1 < &1`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "nh" (MP_TAC o SPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&99 * C pow 2 <=
                mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) sig)`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                   ((gamma:real->A)(&0)) (gamma(&1))` THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_ONE_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `sqrt(&36 * C pow 2) = &6 * C /\ sqrt(&64 * C pow 2) = &8 * C /\
                sqrt(&25 * C pow 2) = &5 * C`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(MESON[POW_2_SQRT] `!x y. &0 <= x /\ y = x pow 2 ==> sqrt y = x`) THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RING]);
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&32 * C pow 2)) <= inv(&5 * C)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&5 * C = sqrt(&25 * C pow 2)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps <= &6 / &25 * (inv C * inv eps)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&6 / &5 * inv(&5 * C) * inv eps` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&99 / &100 * inv(sqrt(&36 * C pow 2)) * inv eps = &33 / &200 * (inv C * inv eps) /\
                &99 / &100 * inv(sqrt(&64 * C pow 2)) * inv eps = &99 / &800 * (inv C * inv eps)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b < a ==> F) ==> a <= b`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(sig - s0) * L < &6 / &25 * (inv C * inv eps)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(sig - s0) * L < &4 / &25 * (inv C * inv eps)` THENL
   [USE_THEN "pn" (MP_TAC o SPECL
      [`eps:real`; `C:real`; `A:real`; `n:num`;
       `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `t:real`; `Q:real`;
       `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `s0:real`; `sig:real`;
       `&36 * C pow 2`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN `abs(sig - s0) = sig - s0` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the middle point at arc length 4/25 / (C eps) *)
  ABBREV_TAC `sm = s0 + (&4 / &25 * (inv C * inv eps)) / L` THEN
  SUBGOAL_THEN `(sm - s0) * L = &4 / &25 * (inv C * inv eps)` ASSUME_TAC THENL
   [EXPAND_TAC "sm" THEN REWRITE_TAC[REAL_ARITH `(s0 + x) - s0 = x`] THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 <= sm /\ sm <= sig` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= b - a ==> a <= b`) THEN
    MATCH_MP_TAC(MESON[REAL_LE_RMUL_EQ] `!L x. &0 < L /\ &0 * L <= x * L ==> &0 <= x`) THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "pn" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:real`; `Q:real`;
     `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `s0:real`; `sm:real`;
     `&36 * C pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `abs(sm - s0) = sm - s0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  USE_THEN "pn" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:real`; `Q:real`;
     `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `sm:real`; `sig:real`;
     `&64 * C pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(sig - sm) = sig - sm` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(sig - sm) * L = (sig - s0) * L - (sm - s0) * L` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One approximant, continued.  Arcs of the minimizer are connected;        *)
(* the point tau at arc length A1 - c from the level, where the far end     *)
(* forces R > Ks (and the bound Kc below A1 - c with 8 C^2 Kc <= n puts     *)
(* tau before s1); intermediate values of R along the minimizer.            *)
(* ------------------------------------------------------------------------- *)

let P2BTL_CURVE_ARC_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) gamma a b.
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ &0 <= a /\ b <= &1
     ==> connected_in top (IMAGE gamma (real_interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

let P2BTL_TAU_POINT = prove
 (`!eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    gamma s0 s1 EN A1 c Kc Ks.
     &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
     &0 < c /\ c < A1 /\ &0 < Kc /\ &8 * C pow 2 * Kc <= &n /\
     (!s. s0 <= s /\ s <= s1 /\
          (s - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                              (gamma(&0)) (gamma(&1)) <= A1 - c
          ==> mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) <= Kc) /\
     (!s. s0 <= s /\ s <= s1 /\
          abs((s - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                  (gamma(&0)) (gamma(&1)) - A1) <= c
          ==> Ks < mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s))
     ==> ?tau. s0 <= tau /\ tau <= s1 /\
               (tau - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                     (gamma(&0)) (gamma(&1)) = A1 - c /\
               Ks < mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma tau)`,
  REPEAT GEN_TAC THEN INTRO_TAC "c1 one cp ca kp kn kc far" THEN
  SUBGOAL_THEN
   `mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) s1) =
    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&1)) / (&2 * C) /\
    &2048 * C pow 4 + &n + &1 <=
    &4 * C * mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&1)) /\
    s0 < s1`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_ONE_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                   ((gamma:real->A)(&0)) (gamma(&1))` THEN
  EXISTS_TAC `s0 + (A1 - c) / L` THEN
  SUBGOAL_THEN `((s0 + (A1 - c) / L) - s0) * L = A1 - c` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(s0 + x) - s0 = x`] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (A1 - c) / L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s0 + (A1 - c) / L <= s1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(s1 < x ==> F) ==> x <= s1`) THEN DISCH_TAC THEN
    USE_THEN "kc" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((s0 + (A1 - c) / L) - s0) * L` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `&4 * C * mfd_scalar (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (rfs_vmetric V (&0))
         ((gamma:real->A)(&1)) =
      &8 * C pow 2 * mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s1)`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
          (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) s1) =
        mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&1)) / (&2 * C)` THEN
      SUBGOAL_THEN `~(C = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `C pow 2 * mfd_scalar (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (rfs_vmetric V (&0))
         ((gamma:real->A) s1) <= C pow 2 * Kc`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C pow 4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "far" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BTL_IVT_POINT = prove
 (`!eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    gamma s0 s1 EN tau v.
     &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\ s0 <= tau /\ tau <= &1 /\
     mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s0) <= v /\
     v <= mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma tau)
     ==> ?sig. s0 <= sig /\ sig <= tau /\
               mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig) = v`,
  REPEAT GEN_TAC THEN INTRO_TAC "c1 one st t1 v0 v1" THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0)) (rfs_vatlas V (&0)) /\
    riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\ &0 < s0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_ONE_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `IMAGE (gamma:real->A) (real_interval[s0,tau])`; `(gamma:real->A) s0`;
     `(gamma:real->A) tau`; `v:real`] APXN_IVT_CONNECTED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P2BTL_CURVE_ARC_CONNECTED) THEN
      EXISTS_TAC `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) (&0)` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; IN_REAL_INTERVAL] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A deep point of the limit.  For k large the minimizer of the             *)
(* approximant sub k reaches R = 200 C^2 before the arc length A1 - c where *)
(* the far end forces R > 400 C^2 (P2BTL_TAU_POINT, P2BTL_IVT_POINT); that  *)
(* window point lifts into a fixed W m (P2BTL_WINDOW_LIFT), and the uniform *)
(* convergence of R on the closure of W m gives a limit point with          *)
(* 110 C^2 <= R <= 300 C^2.                                                  *)
(* ------------------------------------------------------------------------- *)

let P2BTL_DEEP_POINT = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
              ==> ?P0. P0 IN topspace top /\
                       &110 * C pow 2 <= mfd_scalar atlas g P0 /\
                       mfd_scalar atlas g P0 <= &300 * C pow 2`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wl")) o
    MATCH_MP P2BTL_WINDOW_LIFT) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fe"))
    (INST_TYPE [`:A`,`:A`] P2BT_FAR_END) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "blev"))
    (INST_TYPE [`:A`,`:A`] P2BTL_BEYOND_LEVEL) THEN
  EXISTS_TAC `min (min e0 e1) e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  SUBGOAL_THEN `&0 < C pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A1` ASSUME_TAC THENL
   [USE_THEN "cut" (MP_TAC o CONJUNCT1 o REWRITE_RULE[p2bt_cut]) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x <= A1 ==> &0 < A1`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the far end: R > 400 C^2 within c0 of A1 *)
  USE_THEN "fe" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&400 * C pow 2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `N2:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")))) THEN
  ABBREV_TAC `c = min c0 (A1 / &2)` THEN
  SUBGOAL_THEN `&0 < c /\ c <= c0 /\ c < A1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the curvature bound up to arc length A1 - c *)
  USE_THEN "cut" (MP_TAC o SPEC `A1 - c` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[p2bt_cut]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc0:real` (LABEL_TAC "kc")) THEN
  ABBREV_TAC `Kc = max (&400 * C pow 2) Kc0 + &1` THEN
  SUBGOAL_THEN `&0 < Kc /\ Kc0 <= Kc /\ &400 * C pow 2 <= Kc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the lift of window points with R(gamma sig) <= Kc *)
  USE_THEN "wl" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Kc:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `N3:num` (LABEL_TAC "lft"))) THEN
  (* uniform convergence of R on the closure of W m *)
  SUBGOAL_THEN `compact_in top (top closure_of (W:num->B->bool) m) /\
                (W:num->B->bool) m SUBSET top closure_of W m /\
                (W:num->B->bool) m SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o SPEC `m:num` o el 5 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(W:num->B->bool) m SUBSET topspace top` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                        ((s1:num->real) n) A1`;
                 `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
                 `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `top closure_of (W:num->B->bool) m`; `C pow 2`] P2BTL_R_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` (LABEL_TAC "ru")) THEN
  (* one large index *)
  MP_TAC(SPEC `&8 * C pow 2 * Kc` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `Nq:num`) THEN
  ABBREV_TAC `k = (N2:num) + N3 + k2 + Nq` THEN
  SUBGOAL_THEN `(N2:num) <= k /\ (N3:num) <= k /\ (k2:num) <= k /\ (Nq:num) <= k`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k <= (sub:num->num) k` ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o MATCH_MP MONOTONE_BIGGER o REWRITE_RULE[p3_subseq] o
      el 0 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N2:num) <= (sub:num->num) k /\ &8 * C pow 2 * Kc <= &((sub:num->num) k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Nq` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bt_one eps C A ((sub:num->num) k)
      ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k))
      ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k))
      ((s1:num->real) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `(sub:num->num) k`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
       (real->A->real^3^3)) ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))
       ((gamma:num->real->A) ((sub:num->num) k) ((s0:num->real) ((sub:num->num) k))) =
    &32 * C pow 2 /\
    &0 < (s0:num->real) ((sub:num->num) k) /\
    (s1:num->real) ((sub:num->num) k) < &1 /\
    smooth_manifold_atlas (rfs_vtop (V ((sub:num->num) k)) (&0)) (rfs_vatlas (V ((sub:num->num) k)) (&0)) /\
    riemannian_metric (rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `p2bt_one eps C A ((sub:num->num) k)
      ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k))
      ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k))
      ((s1:num->real) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))` THEN
    REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the point tau at arc length A1 - c *)
  MP_TAC(ISPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `A1:real`; `c:real`; `Kc:real`; `&400 * C pow 2`] P2BTL_TAU_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Kc0:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "kc" (MP_TAC o SPECL [`(sub:num->num) k`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "far" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  (* a point with R = 200 C^2 before tau *)
  MP_TAC(ISPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `tau:real`; `&200 * C pow 2`] P2BTL_IVT_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sig:real` STRIP_ASSUME_TAC) THEN
  (* gamma sig is a window point *)
  MP_TAC(ISPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`]
     P2BT_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "blev" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `sig:real`; `y0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  (* the lift *)
  SUBGOAL_THEN `((gamma:num->real->A) ((sub:num->num) k) sig) IN
                topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) ((sub:num->num) k)) (&0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
      `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
      `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
      `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
      `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
      `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`]
      P2BT_ONE_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "lft" (MP_TAC o SPECL
    [`k:num`; `sig:real`; `y0:real^3`; `(gamma:num->real->A) ((sub:num->num) k) sig`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&200 * C pow 2)) * inv eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_dist (rfs_vtop ((V:num->(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),
                    rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))
                    ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
        `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
        `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
        `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
        `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
        `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`]
        P2BT_ONE_DIST) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(tau - (s0:num->real) ((sub:num->num) k)) *
                  mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) ((sub:num->num) k)) (&0),
                    rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))
                    ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `P:B` THEN
  USE_THEN "ru" (MP_TAC o C MATCH_MP (ASSUME `(k2:num) <= k`)) THEN
  DISCH_THEN(MP_TAC o SPEC `P:B` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The set T of one approximant, the union of the middle slab of the        *)
(* window neck at sig and the arc of the minimizer from sig to tau, is      *)
(* connected.                                                                *)
(* ------------------------------------------------------------------------- *)

let P2BTL_T_CONNECTED = prove
 (`!eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    gamma s0 s1 EN sig tau.
     &0 < eps /\ &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
     s0 <= sig /\ sig <= tau /\ tau <= s1
     ==> connected_in (rfs_vtop V (&0))
           (IMAGE (EN sig) (apx_slab (--inv(&2 * eps)) (inv(&2 * eps))) UNION
            IMAGE gamma (real_interval[sig,tau]))`,
  REPEAT GEN_TAC THEN INTRO_TAC "ep c1 one sg st ts" THEN
  SUBGOAL_THEN `&0 < s0 /\ s1 < &1` STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_ONE_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MATCH_MP_TAC CONNECTED_IN_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
      `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) eps
                     ((gamma:real->A) sig) ((EN:real->real^3->A) sig)` THEN
      SIMP_TAC[rfs_neck];
      REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3]];
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P2BTL_CURVE_ARC_CONNECTED) THEN
    EXISTS_TAC `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(gamma:real->A) sig` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(gamma:real->A) sig IN IMAGE ((EN:real->real^3->A) sig) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `sphere(vec 0,&1) SUBSET apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* R is unbounded on the neck centres connected to a deep point P0.         *)
(* For K: the far end at Ks = max K (400 C^2) + 1 gives c and the point tau *)
(* at arc length A1 - c with R > Ks; phi k P0 lies on the window neck at    *)
(* sig' with arc length in [6/5 h0 / eps, A1 - c) (P2BTL_BEYOND_LEVEL2,     *)
(* P2BT_WINDOW_FAR, P2BT_FAR_END); every point of the connected set T       *)
(* (P2BTL_T_CONNECTED) lifts into W m (P2BTL_WINDOW_LIFT) to a 2 eps-neck   *)
(* centre (P2BT_LIM_NECK); psi k T is the set Z.                             *)
(* ------------------------------------------------------------------------- *)

let P2BTL_ZK = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl P0 K.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl /\
              P0 IN topspace top /\ &110 * C pow 2 <= mfd_scalar atlas g P0 /\
              mfd_scalar atlas g P0 <= &300 * C pow 2
              ==> ?Z. connected_in top Z /\ P0 IN Z /\
                      (!z. z IN Z ==> ?e. rfs_neck (top,atlas) g (&2 * eps) z e) /\
                      (?z. z IN Z /\ K <= mfd_scalar atlas g z)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wl")) o
    MATCH_MP P2BTL_WINDOW_LIFT) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ln")) o
    MATCH_MP P2BT_LIM_NECK) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fe"))
    (INST_TYPE [`:A`,`:A`] P2BT_FAR_END) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wpos"))
    (INST_TYPE [`:A`,`:A`] P2BTL_WINDOW_POS) THEN
  X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bl2"))
    (INST_TYPE [`:A`,`:A`] P2BTL_BEYOND_LEVEL2) THEN
  X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wfar"))
    (INST_TYPE [`:A`,`:A`] P2BT_WINDOW_FAR) THEN
  X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min (min (min e0 e1) (min e2 e3)) (min (min e4 e5) (min e6 (&1 / &1000)))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx pt p110 p300" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2 /\ eps <= e3 /\ eps <= e4 /\ eps <= e5 /\
                eps <= e6 /\ eps <= &1 / &1000`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  SUBGOAL_THEN `&0 < C pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A1` ASSUME_TAC THENL
   [USE_THEN "cut" (MP_TAC o CONJUNCT1 o REWRITE_RULE[p2bt_cut]) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x <= A1 ==> &0 < A1`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Ks = max K (&400 * C pow 2) + &1` THEN
  SUBGOAL_THEN `K + &1 <= Ks /\ &400 * C pow 2 < Ks` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ks" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the far end at Ks *)
  USE_THEN "fe" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Ks:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `N2:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")))) THEN
  ABBREV_TAC `c = min c0 (A1 / &2)` THEN
  SUBGOAL_THEN `&0 < c /\ c <= c0 /\ c < A1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the curvature bound up to arc length A1 - c *)
  USE_THEN "cut" (MP_TAC o SPEC `A1 - c` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[p2bt_cut]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc0:real` (LABEL_TAC "kc")) THEN
  ABBREV_TAC `Kc = max Ks Kc0 + &1` THEN
  SUBGOAL_THEN `&0 < Kc /\ Kc0 <= Kc /\ Ks <= Kc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* margins below R = 400 C^2, the lift at Kc, the limit necks at 2 Kc *)
  USE_THEN "wfar" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&400 * C pow 2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c5:real` (X_CHOOSE_THEN `N5:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mar")))) THEN
  USE_THEN "wl" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Kc:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `N3:num` (LABEL_TAC "lft"))) THEN
  USE_THEN "ln" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * Kc`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "lnk")) THEN
  (* the W facts and the uniform convergence of R *)
  SUBGOAL_THEN `!k. open_in top ((W:num->B->bool) k) /\ top closure_of W k SUBSET W (SUC k)`
  (LABEL_TAC "wmon") THENL
   [USE_THEN "lim" (MP_TAC o el 5 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of (W:num->B->bool) m) /\
                (W:num->B->bool) m SUBSET top closure_of W m`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o SPEC `m:num` o el 5 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                        ((s1:num->real) n) A1`;
                 `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
                 `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `top closure_of (W:num->B->bool) m`; `&1 / &2`] P2BTL_R_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:num` (LABEL_TAC "rua")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                        ((s1:num->real) n) A1`;
                 `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
                 `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `{P0:B}`; `C pow 2 / &2`] P2BTL_R_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SING] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kb:num` (LABEL_TAC "rub")) THEN
  (* one large index *)
  MP_TAC(SPEC `&8 * C pow 2 * Kc` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `Nq:num`) THEN
  ABBREV_TAC `k = (N2:num) + N3 + N4 + N5 + ka + kb + Nq + m` THEN
  SUBGOAL_THEN `(N2:num) <= k /\ (N3:num) <= k /\ (N4:num) <= k /\ (N5:num) <= k /\
                (ka:num) <= k /\ (kb:num) <= k /\ (Nq:num) <= k /\ (m:num) <= k`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k <= (sub:num->num) k` ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o MATCH_MP MONOTONE_BIGGER o REWRITE_RULE[p3_subseq] o
      el 0 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N2:num) <= (sub:num->num) k /\ (N5:num) <= (sub:num->num) k /\
                &8 * C pow 2 * Kc <= &((sub:num->num) k)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Nq` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W k` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BTL_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bt_one eps C A ((sub:num->num) k)
      ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k))
      ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k))
      ((s1:num->real) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))`
  (LABEL_TAC "one") THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `(sub:num->num) k`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (s0:num->real) ((sub:num->num) k) /\ (s1:num->real) ((sub:num->num) k) < &1 /\
    (!s. s0 ((sub:num->num) k) <= s /\ s <= s1 ((sub:num->num) k)
         ==> &32 * C pow 2 <=
             mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
               (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((gamma:num->real->A) ((sub:num->num) k) s)) /\
    riemannian_metric (rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`] P2BT_ONE_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  (* the point tau at arc length A1 - c, where R > Ks *)
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `A1:real`; `c:real`; `Kc:real`; `Ks:real`] P2BTL_TAU_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Kc0:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "kc" (MP_TAC o SPECL [`(sub:num->num) k`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "far" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  (* phi k P0 and its window neck sg *)
  USE_THEN "rub" (MP_TAC o C MATCH_MP (ASSUME `(kb:num) <= k`)) THEN
  REWRITE_TAC[SING_SUBSET; IN_SING; FORALL_UNWIND_THM2] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(phi:num->B->A) k P0 IN
    p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))
      ((s0:num->real) ((sub:num->num) k)) ((s1:num->real) ((sub:num->num) k)) A1`
  ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o CONJUNCT1 o SPEC `k:num` o el 8 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
    BETA_TAC THEN UNDISCH_TAC `(P0:B) IN (W:num->B->bool) k` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "wpos" (MP_TAC o SPECL ([`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`; `A1:real`; `(phi:num->B->A) k P0`])) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (X_CHOOSE_THEN `y':real^3`
    (DESTRUCT_TAC "sg0 sg1 ys we r99 r101 pos"))) THEN
  REMOVE_THEN "we" (ASSUME_TAC o SYM) THEN
  USE_THEN "bl2" (MP_TAC o SPECL ([`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`; `sg:real`; `y':real^3`])) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "mar" (MP_TAC o SPECL [`(sub:num->num) k`; `sg:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `&0 < inv(sqrt(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
           (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((gamma:num->real->A) ((sub:num->num) k) sg))) *
         inv eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sg - (s0:num->real) ((sub:num->num) k)) *
    mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
             (rfs_vmetric (V ((sub:num->num) k)) (&0))
             ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1)) < A1 - c`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(A1 - c <= x ==> F) ==> x < A1 - c`) THEN DISCH_TAC THEN
    USE_THEN "far" (MP_TAC o SPECL [`(sub:num->num) k`; `sg:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg <= tau` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(tau < sg ==> F) ==> sg <= tau`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(tau - (s0:num->real) ((sub:num->num) k)) *
      mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
               (rfs_vmetric (V ((sub:num->num) k)) (&0))
               ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1)) <=
      (sg - s0 ((sub:num->num) k)) *
      mfd_dist (rfs_vtop (V ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
               (rfs_vmetric (V ((sub:num->num) k)) (&0))
               (gamma ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the window points between sg and tau *)
  SUBGOAL_THEN
   `!sig y. sg <= sig /\ sig <= tau /\ y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))
            ==> ?P. P IN (W:num->B->bool) m /\
                    (phi:num->B->A) k P = (EN:num->real->real^3->A) ((sub:num->num) k) sig y /\
                    ?e. rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) P e`
  (LABEL_TAC "wpt") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s0:num->real) ((sub:num->num) k) <= sig /\ sig <= (s1:num->real) ((sub:num->num) k)`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`] P2BT_TUBE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "nh" (MP_TAC o SPECL
      [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
       `eps:real`; `(gamma:num->real->A) ((sub:num->num) k) sig`;
       `(EN:num->real->real^3->A) ((sub:num->num) k) sig`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `(sig - (s0:num->real) ((sub:num->num) k)) *
      mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
               (rfs_vmetric (V ((sub:num->num) k)) (&0))
               ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1)) <= A1 - c`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(tau - (s0:num->real) ((sub:num->num) k)) *
                  mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
                    (rfs_vmetric (V ((sub:num->num) k)) (&0))
                    ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1))` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))
        ((gamma:num->real->A) ((sub:num->num) k) sig) <= Kc0 /\
      &32 * C pow 2 <=
      mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))
        (gamma ((sub:num->num) k) sig)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "kc" (MP_TAC o SPECL [`(sub:num->num) k`; `sig:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        FIRST_X_ASSUM(MP_TAC o SPEC `sig:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
          (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((gamma:num->real->A) ((sub:num->num) k) sig))) *
          inv eps <=
      (sig - (s0:num->real) ((sub:num->num) k)) *
      mfd_dist (rfs_vtop (V ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
               (rfs_vmetric (V ((sub:num->num) k)) (&0))
               (gamma ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&6 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
           [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
          REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(sg - (s0:num->real) ((sub:num->num) k)) *
                    mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
                      (rfs_vmetric (V ((sub:num->num) k)) (&0))
                      ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < inv(sqrt(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
           (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((gamma:num->real->A) ((sub:num->num) k) sig))) *
         inv eps`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((EN:num->real->real^3->A) ((sub:num->num) k) sig y) IN
      topspace (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
                     (rfs_vmetric (V ((sub:num->num) k)) (&0)) eps
                     ((gamma:num->real->A) ((sub:num->num) k) sig)
                     ((EN:num->real->real^3->A) ((sub:num->num) k) sig)` THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_neck_dom eps`;
                     `(EN:num->real->real^3->A) ((sub:num->num) k) sig`; `rfs_neck_dom eps`]
                    MFD_PARAM_IMAGE_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "lft" (MP_TAC o SPECL
      [`k:num`; `sig:real`; `y:real^3`; `(EN:num->real->real^3->A) ((sub:num->num) k) sig y`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
      SUBGOAL_THEN
       `&0 < inv(sqrt(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
           (rfs_vmetric (V ((sub:num->num) k)) (&0))
           ((EN:num->real->real^3->A) ((sub:num->num) k) sig y))) * inv eps`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `P:B` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "lnk" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `sig:real`; `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the connected set Tw of the approximant and its lifts *)
  ABBREV_TAC `Tw = IMAGE ((EN:num->real->real^3->A) ((sub:num->num) k) sg)
                        (apx_slab (--inv(&2 * eps)) (inv(&2 * eps))) UNION
                  IMAGE ((gamma:num->real->A) ((sub:num->num) k)) (real_interval[sg,tau])` THEN
  SUBGOAL_THEN `connected_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)) (Tw:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tw" THEN
    MP_TAC(ISPECL ([`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`; `sg:real`; `tau:real`]) P2BTL_T_CONNECTED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN Tw
        ==> ?P. P IN (W:num->B->bool) m /\ (phi:num->B->A) k P = q /\
                ?e. rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) P e`
  (LABEL_TAC "tl") THENL
   [EXPAND_TAC "Tw" THEN REWRITE_TAC[IN_UNION; IN_IMAGE; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "wpt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`] P2BT_TUBE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "wpt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the inverse map psi k on IMAGE (phi k) (W k) *)
  USE_THEN "diffs" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `psi:A->B` (fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP MFD_DIFFEO_MAPS th)))) THEN
  SUBGOAL_THEN `(Tw:A->bool) SUBSET IMAGE ((phi:num->B->A) k) (W k)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    USE_THEN "tl" (MP_TAC o C MATCH_MP (ASSUME `(q:A) IN Tw`)) THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `P:B` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(P:B) IN (W:num->B->bool) m` THEN
    UNDISCH_TAC `(W:num->B->bool) m SUBSET W k` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (psi:A->B) Tw` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)) (IMAGE ((phi:num->B->A) k) (W k))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(phi:num->B->A) k P0` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[];
      EXPAND_TAC "Tw" THEN REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y':real^3` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    USE_THEN "tl" (MP_TAC o C MATCH_MP (ASSUME `(q:A) IN Tw`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `P:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(psi:A->B) q = P` SUBST1_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(phi:num->B->A) k P = q`)) THEN
      SUBGOAL_THEN `(P:B) IN (W:num->B->bool) k` ASSUME_TAC THENL
       [UNDISCH_TAC `(P:B) IN (W:num->B->bool) m` THEN
        UNDISCH_TAC `(W:num->B->bool) m SUBSET W k` THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      ASM_MESON_TAC[]];
    SUBGOAL_THEN `((gamma:num->real->A) ((sub:num->num) k) tau) IN Tw` ASSUME_TAC THENL
     [EXPAND_TAC "Tw" THEN REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "tl" (MP_TAC o C MATCH_MP
      (ASSUME `((gamma:num->real->A) ((sub:num->num) k) tau) IN Tw`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `Pt:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Pt:B` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(gamma:num->real->A) ((sub:num->num) k) tau` THEN ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(ASSUME
        `(phi:num->B->A) k Pt = (gamma:num->real->A) ((sub:num->num) k) tau`)) THEN
      CONV_TAC SYM_CONV THEN
      SUBGOAL_THEN `(Pt:B) IN (W:num->B->bool) k` ASSUME_TAC THENL
       [UNDISCH_TAC `(Pt:B) IN (W:num->B->bool) m` THEN
        UNDISCH_TAC `(W:num->B->bool) m SUBSET W k` THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "rua" (MP_TAC o C MATCH_MP (ASSUME `(ka:num) <= k`)) THEN
    DISCH_THEN(MP_TAC o SPEC `Pt:B` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(Pt:B) IN (W:num->B->bool) m` THEN
      UNDISCH_TAC `(W:num->B->bool) m SUBSET top closure_of W m` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The theorem P2BTL_LIM_CHAIN.  X is the connected component through       *)
(* the deep point P0 (P2BTL_DEEP_POINT) of the set of 2 eps-neck centres;   *)
(* it contains every set of P2BTL_ZK, so R is unbounded on X, while the     *)
(* union of a finite chain has bounded R (APXN_FIN_CHAIN_R_BOUND); hence    *)
(* APXN_GROW2 (with the sphere separation of the limit, P2BT_LIM_SEP) gives *)
(* a chain on a half-line or on all of the integers, which is reindexed to  *)
(* the integers i >= 0 (APXN_CHAIN_SHIFT_GEN, APXN_CHAIN_REV, APX21_SUBCHAIN). *)
(* ------------------------------------------------------------------------- *)

let P2BTL_CHAIN_REINDEX = prove
 (`!top atlas (g:B->real^3^3) eps Ix x e.
     riemannian_metric atlas g /\ apx_chain (top,atlas) g eps Ix x e /\
     ((?a. a <= &0 /\ Ix = {i:int | a <= i}) \/
      (?b. &0 <= b /\ Ix = {i:int | i <= b}) \/ Ix = (:int))
     ==> ?x' e'. apx_chain (top,atlas) g eps {i:int | &0 <= i} x' (e':int->real^3->B)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `Ix:int->bool`; `x:int->B`; `e:int->real^3->B`; `a:int`]
                  APXN_CHAIN_SHIFT_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `{i:int | i + a IN {i:int | a <= i}} = {i:int | &0 <= i}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN INT_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `Ix:int->bool`; `x:int->B`; `e:int->real^3->B`] APXN_CHAIN_REV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC `--b:int` o MATCH_MP APXN_CHAIN_SHIFT_GEN) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `{i:int | i + --b IN {i:int | --i IN {i:int | i <= b}}} = {i:int | &0 <= i}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN INT_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[];
    MAP_EVERY EXISTS_TAC [`x:int->B`; `e:int->real^3->B`] THEN
    MATCH_MP_TAC APX21_SUBCHAIN THEN EXISTS_TAC `Ix:int->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; apx_int_interval; IN_ELIM_THM] THEN
    CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&0:int` THEN
    INT_ARITH_TAC]);;

let P2BTL_LIM_CHAIN = prove
 (`!(u:A->bool) (w:B->bool). P2BT_LIM_CHAIN_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BT_LIM_CHAIN_STATEMENT] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dp")) o
    MATCH_MP (INST_TYPE [`:B`,`:B`] P2BTL_DEEP_POINT)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "zk")) o
    MATCH_MP (INST_TYPE [`:B`,`:B`] P2BTL_ZK)) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:B`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "more"))
    (INST_TYPE [`:B`,`:A`] APX_CH_MORE_HOLDS) THEN
  X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r"))
    (INST_TYPE [`:B`,`:A`] APX_CH_N4R_HOLDS) THEN
  X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))
    (INST_TYPE [`:B`,`:A`] APX21_EXT_HOLDS) THEN
  X_CHOOSE_THEN `e7:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:B`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min (min e0 e1) (min (min (e3 / &2) (e4 / &2))
                                   (min (min (e5 / &2) (e6 / &2)) (e7 / &2)))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ &0 < &2 * eps /\ &2 * eps <= e3 /\ &2 * eps <= e4 /\
                &2 * eps <= e5 /\ &2 * eps <= e6 /\ &2 * eps <= e7`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  SUBGOAL_THEN `apx_sphere_sep (top:B topology) atlas` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BT_LIM_SEP THEN
    MAP_EVERY EXISTS_TAC
     [`eps:real`; `C:real`; `A:real`;
      `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `t:num->real`; `Q:num->real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
      `EN:num->real->real^3->A`;
      `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
             ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n) ((s0:num->real) n)
             ((s1:num->real) n) A1`;
      `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
      `sub:num->num`; `g:B->real^3^3`; `zl:B`; `W:num->B->bool`; `phi:num->B->A`;
      `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the deep point and its neck *)
  USE_THEN "dp" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P0:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!K. ?Z. connected_in top Z /\ (P0:B) IN Z /\
            (!z. z IN Z ==> ?e. rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) z e) /\
            (?z. z IN Z /\ K <= mfd_scalar atlas g z)`
  (LABEL_TAC "zs") THENL
   [X_GEN_TAC `K:real` THEN USE_THEN "zk" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`C:real`; `A:real`;
      `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `t:num->real`; `Q:num->real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
      `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `zl:B`; `W:num->B->bool`;
      `phi:num->B->A`;
      `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e00:real^3->B. rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) P0 e00`
  (X_CHOOSE_TAC `e00:real^3->B`) THENL
   [USE_THEN "zs" (MP_TAC o SPEC `&0`) THEN MESON_TAC[]; ALL_TAC] THEN
  (* the component X *)
  ABBREV_TAC `NC = {x:B | ?e. rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) x e}` THEN
  ABBREV_TAC `X = connected_component_of (subtopology (top:B topology) NC) P0` THEN
  SUBGOAL_THEN `connected_in (top:B topology) X /\ X SUBSET NC /\ (P0:B) IN X`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology (top:B topology) NC`; `P0:B`]
                  CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "NC" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `e00:real^3->B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!K. ?z. z IN X /\ K <= mfd_scalar atlas (g:B->real^3^3) z` (LABEL_TAC "unb") THENL
   [X_GEN_TAC `K:real` THEN USE_THEN "zs" (X_CHOOSE_THEN `Z:B->bool` STRIP_ASSUME_TAC o SPEC `K:real`) THEN
    EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Z:B->bool) SUBSET X` (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
    EXPAND_TAC "X" THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    EXPAND_TAC "NC" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* APXN_GROW2 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `&2 * eps`; `\x:B e:real^3->B. rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) x e`;
                 `X:B->bool`; `P0:B`; `e00:real^3->B`] APXN_GROW2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "ctx" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:B->real^3^3`; `&2 * eps`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "ctx" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:B->real^3^3`; `&2 * eps`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "more" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "n4r" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "ext" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      UNDISCH_TAC `(X:B->bool) SUBSET NC` THEN EXPAND_TAC "NC" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:B`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:int`; `b:int`; `x:int->B`; `e:int->real^3->B`] THEN
    REWRITE_TAC[apxn_good; apx_balanced] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `&2 * eps`; `{i:int | a <= i /\ i <= b}`; `x:int->B`; `e:int->real^3->B`;
                   `a:int`] APXN_CHAIN_SHIFT_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{i:int | i + a IN {i:int | a <= i /\ i <= b}} = {i:int | &0 <= i /\ i <= &n}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      UNDISCH_TAC `b - a = &n:int` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `&2 * eps`; `n:num`; `\i. (x:int->B)(i + a)`; `\i. (e:int->real^3->B)(i + a)`]
                  APXN_FIN_CHAIN_R_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "nh" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                    `g:B->real^3^3`; `&2 * eps`; `x':B`; `e':real^3->B`;
                                    `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `cb:real`) THEN DISCH_TAC THEN
    USE_THEN "unb" (X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC o SPEC `cb + &1`) THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) z <= cb` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ix:int->bool` (X_CHOOSE_THEN `x:int->B`
    (X_CHOOSE_THEN `e:int->real^3->B` (fun th ->
      MATCH_MP_TAC P2BTL_CHAIN_REINDEX THEN
      MAP_EVERY EXISTS_TAC [`Ix:int->bool`; `x:int->B`; `e:int->real^3->B`] THEN
      ASM_REWRITE_TAC[] THEN MP_TAC th THEN SIMP_TAC[])))));;

(* ------------------------------------------------------------------------- *)
(* Tools for the summability.  R >= 31 C^2 everywhere in the limit          *)
(* (P2BTL_LIM_R_LOWER); the limit-side closeness converted to the           *)
(* approximant side (P2BTL_FLIP_CLOSE); a 2 eps-neck of the limit is, for   *)
(* k large, carried by phi k to a 3 eps-neck of the approximant             *)
(* (P2BTL_NECK_TRANSFER, P2BT_NECK_TO_LIMIT with the roles of the limit and *)
(* the approximant exchanged); distances between images of W k are at most  *)
(* 2 A1 (P2BTL_CUT_DIST).                                                    *)
(* ------------------------------------------------------------------------- *)

let P2BTL_LIM_R_LOWER = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
      sub (top:B topology) atlas g zl W phi Vl y.
        &0 < eps /\ eps <= eps0 /\
        p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl /\
        y IN topspace top
        ==> &31 * C pow 2 <= mfd_scalar atlas g y`,
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wpos"))
    (INST_TYPE [`:A`,`:A`] P2BTL_WINDOW_POS) THEN
  EXISTS_TAC `e3:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx yt" THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  SUBGOAL_THEN `&0 < C pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                        ((s1:num->real) n) A1`;
                 `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
                 `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `{y:B}`; `C pow 2 / &2`] P2BTL_R_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SING] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (MP_TAC o SPEC `k:num`)) THEN
  REWRITE_TAC[LE_REFL; SING_SUBSET; IN_SING; FORALL_UNWIND_THM2] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2bt_one eps C A ((sub:num->num) k)
      ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k))
      ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k))
      ((s1:num->real) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))`
  (LABEL_TAC "one") THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `(sub:num->num) k`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(phi:num->B->A) k y IN
    p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))
      ((s0:num->real) ((sub:num->num) k)) ((s1:num->real) ((sub:num->num) k)) A1`
  ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o CONJUNCT1 o SPEC `k:num` o el 8 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
    BETA_TAC THEN UNDISCH_TAC `(y:B) IN (W:num->B->bool) k` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "wpos" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`;
     `A1:real`; `(phi:num->B->A) k y`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sig:real` (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
  USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
  p2bt_drop_rescale_eq_tac THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sig:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `&2 * C`)) (concl th) && can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BTL_FLIP_CLOSE = prove
 (`!m. ?M. &0 <= M /\
     !top atlas (g:B->real^3^3) top' atlas' (g':A->real^3^3) X (phi:B->A) psi S d.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
        mfd_diffeo top atlas X top' atlas' (IMAGE phi X) phi psi /\
        S SUBSET IMAGE phi X /\ d <= &1 / &4 /\
        (!y. y IN IMAGE psi S
             ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g)
                             (rfs_pullback atlas' (phi o chart_inv (chart_at atlas y)) g')
                             (SND(chart_at atlas y) y) <= d)
        ==> !x. x IN S
                ==> lck_dist2 m (metric_local atlas' (chart_at atlas' x) g')
                                (metric_local atlas' (chart_at atlas' x)
                                              (mfd_pullback_metric atlas' atlas psi g))
                                (SND(chart_at atlas' x) x) <= M * d`,
  GEN_TAC THEN
  X_CHOOSE_THEN `M0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "flip"))
    (SPEC `m:num` P2BT_LCK_FLIP) THEN
  EXISTS_TAC `M0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "sm smp rm rmp df ss d4 hd" THEN
  USE_THEN "df" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "flip" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `top':A topology`; `X:B->bool`; `phi:B->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:A) IN S` THEN UNDISCH_TAC `S SUBSET IMAGE (phi:B->A) X` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                 `X:B->bool`; `phi:B->A`; `psi:A->B`; `(psi:A->B) x`; `m:num`]
                P2BT_LIM_CLOSE_CONVERT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN S` THEN UNDISCH_TAC `S SUBSET IMAGE (phi:B->A) X` THEN
    UNDISCH_TAC `IMAGE (psi:A->B) (IMAGE (phi:B->A) X) SUBSET X` THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "hd" MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

let P2BTL_SHELL_COMPACT = prove
 (`!r1 r2. compact {y:real^3 | r1 <= norm y /\ norm y <= r2}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y:real^3 | r1 <= norm y /\ norm y <= r2} = cball(vec 0,r2) DIFF ball(vec 0,r1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]);;

let P2BTL_CUT_DIST = prove
 (`!eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
    sub (top:B topology) atlas g zl W phi Vl k y y'.
     &0 < eps /\
     p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl /\
     y IN W k /\ y' IN W k
     ==> mfd_joinable (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0)) (phi k y) (phi k y') /\
         mfd_dist (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0))
                  (rfs_vmetric (V (sub k)) (&0)) (phi k y) (phi k y') <= &2 * A1`,
  REPEAT GEN_TAC THEN INTRO_TAC "ep lctx yw yw'" THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  USE_THEN "lim" (MP_TAC o CONJUNCT1 o SPEC `k:num` o el 8 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
  BETA_TAC THEN REWRITE_TAC[p2bt_cutset; SUBSET; FORALL_IN_IMAGE; IN_INTER; mfd_ball; IN_ELIM_THM] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `y:B` th) THEN MP_TAC(SPEC `y':B` th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
       (real->A->real^3^3)) ((sub:num->num) k)) (&0)) (rfs_vatlas (V ((sub:num->num) k)) (&0)) /\
    riemannian_metric (rfs_vatlas (V ((sub:num->num) k)) (&0)) (rfs_vmetric (V ((sub:num->num) k)) (&0))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_joinable (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
       (real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
       ((phi:num->B->A) k y) ((gamma:num->real->A) ((sub:num->num) k) ((s0:num->real) ((sub:num->num) k)))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
        (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
        (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
        (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `(phi:num->B->A) k y`; `(gamma:num->real->A) ((sub:num->num) k) ((s0:num->real) ((sub:num->num) k))`;
     `(phi:num->B->A) k y'`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
    [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
        (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
        (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
        (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `(phi:num->B->A) k y`; `(gamma:num->real->A) ((sub:num->num) k) ((s0:num->real) ((sub:num->num) k))`]
     MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

let P2BTL_DOM_SHELL = prove
 (`!eps. &0 < eps
         ==> rfs_neck_dom (&5 / &2 * eps) SUBSET
             {y:real^3 | exp(--inv(&5 / &2 * eps) / sqrt(&2)) <= norm y /\
                         norm y <= exp(inv(&5 / &2 * eps) / sqrt(&2))} /\
             {y:real^3 | exp(--inv(&5 / &2 * eps) / sqrt(&2)) <= norm y /\
                         norm y <= exp(inv(&5 / &2 * eps) / sqrt(&2))} SUBSET
             rfs_neck_dom (&2 * eps)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; annulus; SUBSET; IN_ELIM_THM] THEN
  SUBGOAL_THEN `exp(--inv(&2 * eps) / sqrt(&2)) < exp(--inv(&5 / &2 * eps) / sqrt(&2)) /\
                exp(inv(&5 / &2 * eps) / sqrt(&2)) < exp(inv(&2 * eps) / sqrt(&2))`
  MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
    SUBGOAL_THEN `inv(&5 / &2 * eps) < inv(&2 * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let P2BTL_NECK_TRANSFER = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
      sub (top:B topology) atlas g zl W phi Vl x e.
        &0 < eps /\ eps <= eps0 /\
        p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl /\
        rfs_neck (top,atlas) g (&2 * eps) x e
        ==> ?N. !k. N <= k
                    ==> x IN W k /\ IMAGE e (rfs_neck_dom (&5 / &2 * eps)) SUBSET W k /\
                        rfs_neck (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0))
                                 (rfs_vmetric (V (sub k)) (&0)) (&3 * eps)
                                 (phi k x) (phi k o e)`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rlow"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_LIM_R_LOWER) THEN
  EXISTS_TAC `min e1 (&1 / &100)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx nk" THEN
  MP_TAC(INST_TYPE [`:B`,`:A`; `:A`,`:B`]
    (SPECL [`&5 / &2 * eps`; `&3 * eps`] P2BT_NECK_TO_LIMIT)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ntl")))) THEN
  X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fc"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] (SPEC `m:num` P2BTL_FLIP_CLOSE)) THEN
  MP_TAC(SPECL [`M:real`; `eta:real`] P2BTL_ETA_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  (* the compact shell image *)
  MP_TAC(SPEC `eps:real` P2BTL_DOM_SHELL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Kn = IMAGE (e:real^3->B)
                     {y:real^3 | exp(--inv(&5 / &2 * eps) / sqrt(&2)) <= norm y /\
                                 norm y <= exp(inv(&5 / &2 * eps) / sqrt(&2))}` THEN
  SUBGOAL_THEN `mfd_param (top:B topology) atlas (rfs_neck_dom (&2 * eps)) (e:real^3->B) /\
                (x:B) IN IMAGE e (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) x (e:real^3->B)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (top:B topology) Kn` ASSUME_TAC THENL
   [EXPAND_TAC "Kn" THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom (&2 * eps)`] THEN
    ASM_REWRITE_TAC[P2BTL_SHELL_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->B) (rfs_neck_dom (&5 / &2 * eps)) SUBSET Kn /\ (x:B) IN Kn`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kn" THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:B) (f:real^3->B). s SUBSET t ==> x IN IMAGE f s ==> x IN IMAGE f t`) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_neck_dom (&5 / &2 * eps)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the convergence on Kn *)
  USE_THEN "lim" (MP_TAC o SPECL [`Kn:B->bool`; `m:num`; `d:real`] o el 9 o CONJUNCTS o
    REWRITE_RULE[p2bt_lim]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "cv")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(k0:num) <= k`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cvk")) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "diffs" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `psi:A->B` (fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP MFD_DIFFEO_MAPS th)))) THEN
  SUBGOAL_THEN `open_in (top:B topology) (IMAGE (e:real^3->B) (rfs_neck_dom (&5 / &2 * eps)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom (&2 * eps)`] THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN
    MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->B) (rfs_neck_dom (&5 / &2 * eps)) SUBSET (W:num->B->bool) k`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "ntl" (MP_TAC o SPECL
    [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `IMAGE ((phi:num->B->A) k) (W k)`; `psi:A->B`; `(phi:num->B->A) k`;
     `IMAGE (e:real^3->B) (rfs_neck_dom (&5 / &2 * eps))`; `x:B`; `e:real^3->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `&2 * eps` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "rlow" (MP_TAC o SPECL
        [`eps:real`; `C:real`; `A:real`;
         `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
         `t:num->real`; `Q:num->real`;
         `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
         `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
         `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
         `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
         `W:num->B->bool`; `phi:num->B->A`;
         `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
         `x:B`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) x (e:real^3->B)` THEN
        REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `rfs_neck_dom (&2 * eps)`; `e:real^3->B`; `rfs_neck_dom (&2 * eps)`]
                      MFD_PARAM_IMAGE_SUBSET) THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN
        UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
        MP_TAC(SPEC `&2 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= C pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `M * d` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fc" (MP_TAC o SPECL
      [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
       `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
       `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`;
       `IMAGE ((phi:num->B->A) k) (IMAGE (e:real^3->B) (rfs_neck_dom (&5 / &2 * eps)))`;
       `d:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(psi:A->B) ((phi:num->B->A) k ((e:real^3->B) w)) = e w` SUBST1_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!x:B. x IN Wk ==> (psi:A->B) ((phi:B->A) x) = x`) (concl th))) THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "cvk" MATCH_MP_TAC THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The summability counts.  Points of an interval with pairwise gaps at     *)
(* least r_i + r_j: sum 2 r_i <= length + 2 max r (real measure of disjoint *)
(* open intervals, P2BTL_INTERVALS_SUM); two 3 eps-necks, the first having  *)
(* a point of sval about -1/4 eps outside the second, have centres at       *)
(* distance at least 3/50 h_1 / eps (P2BTL_PAIR_DIST).                       *)
(* ------------------------------------------------------------------------- *)

let P2BTL_INTERVALS_SUM = prove
 (`!n (p:num->real) r a b M.
     (!i. i <= n ==> a <= p i /\ p i <= b /\ &0 <= r i /\ r i <= M) /\
     (!i j. i <= n /\ j <= n /\ ~(i = j) ==> r i + r j <= abs(p i - p j))
     ==> sum(0..n) (\i. &2 * r i) <= (b - a) + &2 * M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `real_measure(UNIONS (IMAGE (\i. real_interval(p i - r i,p i + r i)) (0..n))) =
    sum(0..n) (\i. real_measure(real_interval(p i - r i,p i + r i)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURE_DISJOINT_UNIONS_IMAGE THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_MEASURABLE_REAL_INTERVAL] THEN
    REWRITE_TAC[IN_NUMSEG; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN X_GEN_TAC `z:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[LE_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(0..n) (\i. real_measure(real_interval(p i - r i,p i + r i))) =
                sum(0..n) (\i. &2 * r i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_MEASURE_REAL_INTERVAL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measure(UNIONS (IMAGE (\i. real_interval(p i - r i,p i + r i)) (0..n))) <=
    real_measure(real_interval(a - M,b + M))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_MEASURE_SUBSET THEN REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_UNIONS THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE; REAL_MEASURABLE_REAL_INTERVAL];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; SUBSET; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `z:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MEASURE_REAL_INTERVAL] THEN
  SUBGOAL_THEN `&0 <= M /\ a <= b` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    REWRITE_TAC[LE_0] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BTL_PAIR_DIST = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps x1 e1 x2 e2 yq.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g (&3 * eps) x1 e1 /\
        rfs_neck (top,atlas) g (&3 * eps) x2 (e2:real^3->A) /\
        yq IN rfs_neck_dom (&3 * eps) /\ abs(apx_sval yq) <= &51 / &200 * inv eps /\
        ~((e1:real^3->A) yq IN IMAGE e2 (rfs_neck_dom (&3 * eps))) /\
        mfd_joinable (top,atlas) x1 x2
        ==> &3 / &50 * inv(sqrt(mfd_scalar atlas g x1)) * inv eps <=
            mfd_dist (top,atlas) g x1 x2`,
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min (e2 / &3) (min (e3 / &3) (&1 / &1000))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x1:A`; `f1:real^3->A`; `x2:A`; `f2:real^3->A`; `yq:real^3`] THEN
  INTRO_TAC "ep epm hs sm rm n1 n2 yq sq out jn" THEN
  SUBGOAL_THEN `&0 < &3 * eps /\ &3 * eps <= e2 /\ &3 * eps <= e3 /\ eps <= &1 / &1000`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `&3 * eps`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  UNDISCH_TAC `apx_eng_n2 top atlas (g:A->real^3^3) (&3 * eps) (&1 / &100)` THEN
  REWRITE_TAC[apx_eng_n2] THEN DISCH_THEN(LABEL_TAC "eng") THEN
  (* the centres on the unit spheres *)
  SUBGOAL_THEN `?y1. y1 IN rfs_neck_dom (&3 * eps) /\ apx_sval y1 = &0 /\ (f1:real^3->A) y1 = x1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (&3 * eps) x1 (f1:real^3->A)` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE; IN_SPHERE_0] THEN STRIP_TAC THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO] THEN
    MP_TAC(SPEC `&3 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y2. y2 IN rfs_neck_dom (&3 * eps) /\ apx_sval y2 = &0 /\ (f2:real^3->A) y2 = x2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (&3 * eps) x2 (f2:real^3->A)` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE; IN_SPHERE_0] THEN STRIP_TAC THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO] THEN
    MP_TAC(SPEC `&3 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the distance from x1 to q = f1 yq *)
  USE_THEN "eng" (MP_TAC o SPECL [`x1:A`; `f1:real^3->A`; `y1:real^3`; `yq:real^3`] o
    REWRITE_RULE[IMP_CONJ]) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x1)) /\
                &0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x2)) /\ &1000 <= inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (&3 * eps) x1 (f1:real^3->A)` THEN
      SIMP_TAC[rfs_neck];
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (&3 * eps) x2 (f2:real^3->A)` THEN
      SIMP_TAC[rfs_neck];
      MP_TAC(SPECL [`eps:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC P2BT_SQRT2_PI THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(&3 * eps) = &1 / &3 * inv eps` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_CASES_TAC `(x2:A) IN IMAGE (f1:real^3->A) (rfs_neck_dom (&3 * eps))` THENL
   [ALL_TAC;
    (* x2 outside the first neck *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 - &1 / &100) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x1)) *
                (inv(&3 * eps) - abs(apx_sval(y1:real^3)))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_SUB_RZERO] THEN
      SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x1)) * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:real->A` THEN STRIP_TAC THEN
    USE_THEN "eng" (MP_TAC o SPECL [`x1:A`; `f1:real^3->A`; `y1:real^3`; `y1:real^3`] o
      REWRITE_RULE[IMP_CONJ]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:real->A`; `&0`; `&1`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]] THEN
  (* x2 inside the first neck: comparable scales, q outside the second neck *)
  UNDISCH_TAC `(x2:A) IN IMAGE (f1:real^3->A) (rfs_neck_dom (&3 * eps))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "nh" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `&3 * eps`; `x1:A`; `f1:real^3->A`; `z:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(x2:A) = f1 (z:real^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) (x2:A) ((f1:real^3->A) yq)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - &1 / &100) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x2)) *
                (inv(&3 * eps) - abs(apx_sval(y2:real^3))) <=
                mfd_dist (top,atlas) g x2 ((f1:real^3->A) yq)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:real->A` THEN STRIP_TAC THEN
    USE_THEN "eng" (MP_TAC o SPECL [`x2:A`; `f2:real^3->A`; `y2:real^3`; `y2:real^3`] o
      REWRITE_RULE[IMP_CONJ]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:real->A`; `&0`; `&1`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x2:A`; `x1:A`; `(f1:real^3->A) yq`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x2:A`; `x1:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `apx_sval(y2:real^3) = &0`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `inv(&3 * eps) = &1 / &3 * inv eps`;
                              REAL_ABS_NUM; REAL_SUB_RZERO]) THEN
  SUBGOAL_THEN
   `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x1)) * (abs(apx_sval(yq:real^3)) + sqrt(&2) * pi) <=
    inv(sqrt(mfd_scalar atlas g x1)) * (&51 / &200 * inv eps + &24 / &5) /\
    inv(sqrt(mfd_scalar atlas g x1)) * &1000 <= inv(sqrt(mfd_scalar atlas g x1)) * inv eps /\
    inv(sqrt(mfd_scalar atlas g x1)) * inv eps <=
    &51 / &50 * (inv(sqrt(mfd_scalar atlas g x2)) * inv eps)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for the summability.  Finitely many eventual properties hold      *)
(* together; scales under curvature comparison; points of given sval; the   *)
(* pairwise distance of transported chain centres (P2BTL_CHAIN_PAIR, from   *)
(* the end-slab disjointness of apx_chain and P2BTL_PAIR_DIST); every point *)
(* of the cut set lies within 5 h of the minimizer (P2BTL_ARC_POINT, by     *)
(* P2BTL_WINDOW_POS and P2BT_WINDOW_LEVEL_POINT).                            *)
(* ------------------------------------------------------------------------- *)

let P2BTL_FINITE_EVENTUALLY = prove
 (`!(P:num->num->bool) n.
     (!i. i <= n ==> ?N. !k. N <= k ==> P i k)
     ==> ?N. !i k. i <= n /\ N <= k ==> P i k`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "h") THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "h" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
  USE_THEN "h" (MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
  EXISTS_TAC `MAX N1 N2` THEN MAP_EVERY X_GEN_TAC [`i:num`; `k:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i = SUC n` THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "n2" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    USE_THEN "n1" MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let P2BTL_H_COMPARE = prove
 (`!a b. &0 < a /\ &0 < b /\ b <= &10201 / &10000 * a
         ==> inv(sqrt a) <= &101 / &100 * inv(sqrt b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt b <= &101 / &100 * sqrt a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt a /\ &0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt a) = inv(sqrt a) * (sqrt b * inv(sqrt b))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_RID]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(sqrt a) * ((&101 / &100 * sqrt a) * inv(sqrt b))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(sqrt a = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

let P2BTL_SVAL_POINT = prove
 (`!c. ~(exp(c / sqrt(&2)) % (&1 % basis 1:real^3) = vec 0) /\
       apx_sval(exp(c / sqrt(&2)) % (&1 % basis 1:real^3)) = c`,
  GEN_TAC THEN MP_TAC(SPECL [`c:real`; `&1`] APX_SVAL_SCALED_BASIS) THEN
  REWRITE_TAC[REAL_LT_01; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID]);;

let P2BTL_CHAIN_PAIR = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:B->real^3^3) top' atlas' (g':A->real^3^3) W (phi:B->A) psi eps x e i j.
        &0 < eps /\ eps <= eps0 /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_diffeo top atlas W top' atlas' (IMAGE phi W) phi psi /\
        apx_chain (top,atlas) g (&2 * eps) {i:int | &0 <= i} x (e:int->real^3->B) /\
        &0 <= i /\ i < j /\
        IMAGE (e i) (rfs_neck_dom (&5 / &2 * eps)) SUBSET W /\
        IMAGE (e j) (rfs_neck_dom (&5 / &2 * eps)) SUBSET W /\
        rfs_neck (top',atlas') g' (&3 * eps) (phi (x i)) (phi o e i) /\
        rfs_neck (top',atlas') g' (&3 * eps) (phi (x j)) (phi o e j) /\
        mfd_joinable (top',atlas') (phi (x i)) (phi (x j))
        ==> &3 / &50 * inv(sqrt(mfd_scalar atlas' g' (phi (x i)))) * inv eps <=
            mfd_dist (top',atlas') g' (phi (x i)) (phi (x j)) /\
            &3 / &50 * inv(sqrt(mfd_scalar atlas' g' (phi (x j)))) * inv eps <=
            mfd_dist (top',atlas') g' (phi (x i)) (phi (x j))`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd"))
    (INST_TYPE [`:A`,`:A`] P2BTL_PAIR_DIST) THEN
  EXISTS_TAC `min e0 (&1 / &1000)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm hs sm rm df ch i0 ij wi wj ni nj jn" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= &1 / &1000` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "df" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  USE_THEN "ch" (MP_TAC o SPECL [`i:int`; `j:int`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    CONJUNCT2 o REWRITE_RULE[apx_chain]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `inv(&2 * &2 * eps) = &1 / &4 * inv eps /\ inv(&2 * eps) = &1 / &2 * inv eps /\
                inv(&3 * eps) = &1 / &3 * inv eps /\ inv(&5 / &2 * eps) = &2 / &5 * inv eps`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom (&3 * eps) SUBSET rfs_neck_dom (&5 / &2 * eps) /\
                rfs_neck_dom (&3 * eps) SUBSET rfs_neck_dom (&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the point below *)
  ABBREV_TAC `yq = exp((--(&51 / &200 * inv eps)) / sqrt(&2)) % (&1 % basis 1:real^3)` THEN
  ABBREV_TAC `yr = exp((&51 / &200 * inv eps) / sqrt(&2)) % (&1 % basis 1:real^3)` THEN
  SUBGOAL_THEN `~(yq:real^3 = vec 0) /\ apx_sval yq = --(&51 / &200 * inv eps) /\
                ~(yr:real^3 = vec 0) /\ apx_sval yr = &51 / &200 * inv eps`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "yq" THEN EXPAND_TAC "yr" THEN REWRITE_TAC[P2BTL_SVAL_POINT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `yq IN rfs_neck_dom (&3 * eps) /\ yq IN rfs_neck_dom (&5 / &2 * eps) /\
    yq IN apx_slab (--inv(&2 * eps)) (--inv(&2 * &2 * eps)) /\
    yr IN rfs_neck_dom (&3 * eps) /\ yr IN rfs_neck_dom (&5 / &2 * eps) /\
    yr IN apx_slab (inv(&2 * &2 * eps)) (inv(&2 * eps))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "pd" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(phi:B->A) o (e:int->real^3->B) i`; `(phi:B->A) o (e:int->real^3->B) j`;
                          `yq:real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[o_THM; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:int->real^3->B) i yq = e j z` ASSUME_TAC THENL
     [SUBGOAL_THEN `(e:int->real^3->B) i yq IN W /\ (e:int->real^3->B) j z IN W`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE ((e:int->real^3->B) j) (rfs_neck_dom (&2 * eps)))
                   (IMAGE (e i) (apx_slab (--inv(&2 * eps)) (--inv(&2 * &2 * eps))))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->B) i yq`) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `yq:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the point above, with the roles of i and j exchanged *)
  MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                 `(phi:B->A) ((x:int->B) i)`; `(phi:B->A) ((x:int->B) j)`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "pd" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(phi:B->A) o (e:int->real^3->B) j`; `(phi:B->A) o (e:int->real^3->B) i`;
                        `yr:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[o_THM; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:int->real^3->B) j yr = e i z` ASSUME_TAC THENL
     [SUBGOAL_THEN `(e:int->real^3->B) j yr IN W /\ (e:int->real^3->B) i z IN W`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE ((e:int->real^3->B) i) (rfs_neck_dom (&2 * eps)))
                   (IMAGE (e j) (apx_slab (inv(&2 * &2 * eps)) (inv(&2 * eps))))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->B) j yr`) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `yr:real^3` THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[MFD_JOINABLE_SYM]]);;

let P2BTL_ARC_POINT = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            gamma s0 s1 EN A1 w.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\
              p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
              w IN p2bt_cutset eps V gamma EN s0 s1 A1
              ==> ?t'. &0 <= t' /\ t' <= &1 /\
                       mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) w (gamma t') /\
                       mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                w (gamma t') <=
                       &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) w))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wlp")) o
    MATCH_MP P2BT_WINDOW_LEVEL_POINT) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wpos"))
    (INST_TYPE [`:A`,`:A`] P2BTL_WINDOW_POS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min (min e0 e1) e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm c1 one wc" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "wpos" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:real`; `Q:real`;
     `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `A1:real`; `w:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sig:real` (X_CHOOSE_THEN `y:real^3`
    (DESTRUCT_TAC "sg0 sg1 ys we r99 r101 pos"))) THEN
  REMOVE_THEN "we" (ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ abs(apx_sval y) <= &19 / &20 * inv eps`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      UNDISCH_TAC `apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) SUBSET rfs_neck_dom eps` THEN
      SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `inv(&2 * eps) = &1 / &2 * inv eps /\ &0 < inv eps` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_INV_MUL; REAL_LT_INV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "wlp" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:real`; `Q:real`;
     `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `sig:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t':real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
                 `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0))`
  ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "nh" (MP_TAC o SPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC P2BT_SQRT2_PI THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= inv(sqrt(mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
       (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) sig)))`
  ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_INV_EQ; SQRT_POS_LE] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN
    UNDISCH_TAC `rfs_neck (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
       (real->A->real^3^3)) (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) eps ((gamma:real->A) sig)
       ((EN:real->real^3->A) sig)` THEN
    SIMP_TAC[rfs_neck; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(sqrt(mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
       (real->A->real^3^3)) (&0)) (rfs_vmetric V (&0)) ((gamma:real->A) sig))) * (sqrt(&2) * pi) <=
    inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * (&24 / &5)`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The count at one approximant.  The transported centres are pairwise      *)
(* far apart (P2BTL_CHAIN_PAIR) and each lies within 5 h of the minimizer   *)
(* c, which has constant speed L; so the arc positions are separated by     *)
(* (h_i + h_j) / (40 eps), and P2BTL_INTERVALS_SUM bounds the sum of the    *)
(* scales by 40 eps L + 1.                                                   *)
(* ------------------------------------------------------------------------- *)

let P2BTL_SUM_AT_K = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:B->real^3^3) top' atlas' (g':A->real^3^3) W (phi:B->A) psi eps x e n
      (c:real->A) L.
        &0 < eps /\ eps <= eps0 /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_diffeo top atlas W top' atlas' (IMAGE phi W) phi psi /\
        apx_chain (top,atlas) g (&2 * eps) {i:int | &0 <= i} x (e:int->real^3->B) /\
        &0 <= L /\
        (!a b. &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1
               ==> mfd_joinable (top',atlas') (c a) (c b) /\
                   mfd_dist (top',atlas') g' (c a) (c b) = abs(b - a) * L) /\
        (!i. i <= n
             ==> IMAGE (e(&i)) (rfs_neck_dom (&5 / &2 * eps)) SUBSET W /\
                 rfs_neck (top',atlas') g' (&3 * eps) (phi (x(&i))) (phi o e(&i)) /\
                 &1 <= mfd_scalar atlas' g' (phi (x(&i))) /\
                 ?t'. &0 <= t' /\ t' <= &1 /\
                      mfd_joinable (top',atlas') (phi (x(&i))) (c t') /\
                      mfd_dist (top',atlas') g' (phi (x(&i))) (c t') <=
                      &5 * inv(sqrt(mfd_scalar atlas' g' (phi (x(&i)))))) /\
        (!i j. i <= n /\ j <= n
               ==> mfd_joinable (top',atlas') (phi (x(&i))) (phi (x(&j))))
        ==> sum(0..n) (\i. inv(sqrt(mfd_scalar atlas' g' (phi (x(&i)))))) <=
            &40 * eps * L + &1`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cp"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_CHAIN_PAIR) THEN
  EXISTS_TAC `min e0 (&1 / &1000)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm hs sm rm df ch l0 cd pts jn" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= &1 / &1000 /\ &0 < inv eps /\ &1000 <= inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      MP_TAC(SPECL [`eps:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `hp = \i. inv(sqrt(mfd_scalar atlas' (g':A->real^3^3) ((phi:B->A) ((x:int->B)(&i)))))` THEN
  SUBGOAL_THEN `!i. i <= (n:num) ==> &0 < (hp:num->real) i /\ (hp:num->real) i <= &1` (LABEL_TAC "hb") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "hp" THEN
    USE_THEN "pts" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* arc positions *)
  SUBGOAL_THEN
   `?tt. !i. i <= n
             ==> &0 <= (tt:num->real) i /\ (tt:num->real) i <= &1 /\
                 mfd_joinable (top',atlas') ((phi:B->A) ((x:int->B)(&i))) ((c:real->A) (tt i)) /\
                 mfd_dist (top',atlas') (g':A->real^3^3) (phi (x(&i))) (c (tt i)) <= &5 * (hp:num->real) i`
  (X_CHOOSE_THEN `tt:num->real` (LABEL_TAC "tt")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num <= n` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pts" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN
    EXPAND_TAC "hp" THEN MESON_TAC[];
    ALL_TAC] THEN
  (* pairwise separation of the arc positions *)
  SUBGOAL_THEN
   `!i j. i <= n /\ j <= n /\ i < j
          ==> (&1 / &80 * inv eps) * (hp:num->real) i + (&1 / &80 * inv eps) * (hp:num->real) j <=
              abs(tt i * L - (tt:num->real) j * L)`
  (LABEL_TAC "sep") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "pts" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN STRIP_TAC THEN
    USE_THEN "pts" (MP_TAC o C MATCH_MP (ASSUME `j:num <= n`)) THEN STRIP_TAC THEN
    USE_THEN "cp" (MP_TAC o SPECL
      [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
       `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
       `W:B->bool`; `phi:B->A`; `psi:A->B`; `eps:real`; `x:int->B`; `e:int->real^3->B`;
       `&i:int`; `&j:int`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN
      USE_THEN "jn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "tt" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN STRIP_TAC THEN
    USE_THEN "tt" (MP_TAC o C MATCH_MP (ASSUME `j:num <= n`)) THEN STRIP_TAC THEN
    USE_THEN "cd" (MP_TAC o SPECL [`(tt:num->real) i`; `(tt:num->real) j`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `mfd_dist (top',atlas') (g':A->real^3^3) ((phi:B->A) ((x:int->B)(&i))) (phi (x(&j))) <=
      mfd_dist (top',atlas') g' (phi (x(&i))) ((c:real->A) ((tt:num->real) i)) +
      mfd_dist (top',atlas') g' (c (tt i)) (c (tt j)) +
      mfd_dist (top',atlas') g' (phi (x(&j))) (c (tt j))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                     `(phi:B->A) ((x:int->B)(&i))`; `(c:real->A) ((tt:num->real) i)`;
                     `(phi:B->A) ((x:int->B)(&j))`] MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                     `(c:real->A) ((tt:num->real) i)`; `(c:real->A) ((tt:num->real) j)`;
                     `(phi:B->A) ((x:int->B)(&j))`] MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                     `(c:real->A) ((tt:num->real) j)`; `(phi:B->A) ((x:int->B)(&j))`]
                    MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(tt j - (tt:num->real) i) * L = abs(tt i * L - (tt:num->real) j * L)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= L ==> abs L = L`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&3 / &50 * inv(sqrt(mfd_scalar atlas' (g':A->real^3^3)
                   ((phi:B->A) ((x:int->B)(&i))))) * inv eps <=
                 mfd_dist (top',atlas') g' (phi (x(&i))) (phi (x(&j)))` THEN
    UNDISCH_TAC `&3 / &50 * inv(sqrt(mfd_scalar atlas' (g':A->real^3^3)
                   ((phi:B->A) ((x:int->B)(&j))))) * inv eps <=
                 mfd_dist (top',atlas') g' (phi (x(&i))) (phi (x(&j)))` THEN
    UNDISCH_TAC `mfd_dist (top',atlas') (g':A->real^3^3) ((phi:B->A) ((x:int->B)(&i)))
                   ((c:real->A) ((tt:num->real) i)) <= &5 * (hp:num->real) i` THEN
    UNDISCH_TAC `mfd_dist (top',atlas') (g':A->real^3^3) ((phi:B->A) ((x:int->B)(&j)))
                   ((c:real->A) ((tt:num->real) j)) <= &5 * (hp:num->real) j` THEN
    EXPAND_TAC "hp" THEN BETA_TAC THEN
    SUBGOAL_THEN
     `&1000 * inv(sqrt(mfd_scalar atlas' (g':A->real^3^3) ((phi:B->A) ((x:int->B)(&i))))) <=
      inv(sqrt(mfd_scalar atlas' g' (phi (x(&i))))) * inv eps /\
      &1000 * inv(sqrt(mfd_scalar atlas' g' (phi (x(&j))))) <=
      inv(sqrt(mfd_scalar atlas' g' (phi (x(&j))))) * inv eps`
    MP_TAC THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the measure count *)
  MP_TAC(SPECL [`n:num`; `\i. (tt:num->real) i * L`; `\i. (&1 / &80 * inv eps) * (hp:num->real) i`;
                `&0`; `L:real`; `&1 / &80 * inv eps`] P2BTL_INTERVALS_SUM) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "tt" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN STRIP_TAC THEN
      USE_THEN "hb" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `i:num < j` THENL
       [USE_THEN "sep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `j:num < i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
        USE_THEN "sep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN EXPAND_TAC "hp" THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC; SUM_RMUL; SUM_LMUL] THEN
  ABBREV_TAC `S = sum(0..n) (\i. inv(sqrt(mfd_scalar atlas' (g':A->real^3^3)
                     ((phi:B->A) ((x:int->B)(&i))))))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `eps * inv eps = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&40 * eps) * ((&2 * &1 / &80 * inv eps) * S) <= (&40 * eps) * (L + &2 * &1 / &80 * inv eps)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&40 * eps) * ((&2 * &1 / &80 * inv eps) * S) = (eps * inv eps) * S /\
                (&40 * eps) * (L + &2 * &1 / &80 * inv eps) = &40 * eps * L + eps * inv eps`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorem P2BTL_LIM_SUMMABLE.  For fixed n and k large, all the        *)
(* chain necks N_i (i <= n) are transported to 3 eps-necks of the          *)
(* approximant sub k (P2BTL_NECK_TRANSFER) with R_k close to R            *)
(* (P2BTL_R_UNIF); P2BTL_SUM_AT_K bounds their scales by 40 eps L + 1 with  *)
(* L <= A + 5 C / eps, and the limit scales are at most 101/100 times       *)
(* larger.  A.6 is the theorem APXM_A6_CS.                                  *)
(* ------------------------------------------------------------------------- *)

let P2BTL_GAMMA_DIST = prove
 (`!eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    gamma s0 s1 EN.
     &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN
     ==> !a b. &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1
               ==> mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (gamma a) (gamma b) /\
                   mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                            (gamma a) (gamma b) =
                   abs(b - a) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                         (gamma(&0)) (gamma(&1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN DISCH_THEN(LABEL_TAC "d") THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (rfs_vatlas V (&0))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a <= b` THENL
   [USE_THEN "d" (MP_TAC o SPECL [`a:real`; `b:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    USE_THEN "d" (MP_TAC o SPECL [`b:real`; `a:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&0)`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) (&0)`;
                   `(gamma:real->A) a`; `(gamma:real->A) b`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2BTL_LIM_SUMMABLE = prove
 (`!(u:A->bool) (w:B->bool). P2BT_LIM_SUMMABLE_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BT_LIM_SUMMABLE_STATEMENT] THEN
  MP_TAC(ISPEC `u:A->bool` APXM_A6_CS) THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "arc")) o
    MATCH_MP P2BTL_ARC_POINT) THEN
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sak"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_SUM_AT_K) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nt"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_NECK_TRANSFER) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rl"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_LIM_R_LOWER) THEN
  EXISTS_TAC `min (min e0 e1) (min e2 e3)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epm lctx ch" THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2 /\ eps <= e3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  SUBGOAL_THEN `&1 <= C pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `&2 * (&40 * eps * A + &200 * C + &1)` THEN X_GEN_TAC `n:num` THEN
  (* the chain necks *)
  SUBGOAL_THEN
   `!i. rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) ((x:int->B)(&i)) ((e:int->real^3->B)(&i)) /\
        x(&i) IN topspace top`
  (LABEL_TAC "cn") THENL
   [X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) ((x:int->B)(&i))
                    ((e:int->real^3->B)(&i))` ASSUME_TAC THENL
     [USE_THEN "ch" (MP_TAC o SPEC `&i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        REWRITE_RULE[apx_chain]) THEN
      REWRITE_TAC[IN_ELIM_THM; INT_POS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) ((x:int->B)(&i))
                   ((e:int->real^3->B)(&i))` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom (&2 * eps)`; `(e:int->real^3->B)(&i)`; `rfs_neck_dom (&2 * eps)`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `((x:int->B)(&i)) IN IMAGE ((e:int->real^3->B)(&i)) (sphere(vec 0,&1))` THEN
    MP_TAC(SPEC `&2 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
    ALL_TAC] THEN
  (* transport and curvature closeness, eventually in k, for all i <= n *)
  MP_TAC(ISPECL
    [`\i k. ((x:int->B)(&i)) IN (W:num->B->bool) k /\
            IMAGE ((e:int->real^3->B)(&i)) (rfs_neck_dom (&5 / &2 * eps)) SUBSET W k /\
            rfs_neck (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) ((sub:num->num) k)) (&0),
                      rfs_vatlas (V ((sub:num->num) k)) (&0))
                     (rfs_vmetric (V ((sub:num->num) k)) (&0)) (&3 * eps)
                     ((phi:num->B->A) k (x(&i))) (phi k o e(&i)) /\
            abs(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
                           (rfs_vmetric (V ((sub:num->num) k)) (&0)) (phi k (x(&i))) -
                mfd_scalar atlas (g:B->real^3^3) (x(&i))) <= &1 / &2`;
     `n:num`] P2BTL_FINITE_EVENTUALLY) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "nt" (MP_TAC o SPECL
      [`eps:real`; `C:real`; `A:real`;
       `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `t:num->real`; `Q:num->real`;
       `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
       `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
       `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
       `W:num->B->bool`; `phi:num->B->A`;
       `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
       `(x:int->B)(&i)`; `(e:int->real^3->B)(&i)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                          ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                          ((s1:num->real) n) A1`;
                   `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
                   `sub:num->num`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                   `W:num->B->bool`; `phi:num->B->A`;
                   `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                   `{(x:int->B)(&i)}`; `&1 / &2`] P2BTL_R_UNIF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_IN_SING] THEN
      TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "k1")) THEN
    EXISTS_TAC `N1 + k1:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "n1" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "k1" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SING_SUBSET; IN_SING; FORALL_UNWIND_THM2] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (LABEL_TAC "ev")) THEN
  SUBGOAL_THEN
   `!i. i <= n
        ==> ((x:int->B)(&i)) IN (W:num->B->bool) k /\
            IMAGE ((e:int->real^3->B)(&i)) (rfs_neck_dom (&5 / &2 * eps)) SUBSET W k /\
            rfs_neck (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) ((sub:num->num) k)) (&0),
                      rfs_vatlas (V ((sub:num->num) k)) (&0))
                     (rfs_vmetric (V ((sub:num->num) k)) (&0)) (&3 * eps)
                     ((phi:num->B->A) k (x(&i))) (phi k o e(&i)) /\
            abs(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
                           (rfs_vmetric (V ((sub:num->num) k)) (&0)) (phi k (x(&i))) -
                mfd_scalar atlas (g:B->real^3^3) (x(&i))) <= &1 / &2`
  (LABEL_TAC "evk") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "ev" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  (* the approximant at sub k *)
  USE_THEN "diffs" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  SUBGOAL_THEN
   `p2bt_one eps C A ((sub:num->num) k)
      ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k))
      ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
      ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k))
      ((s1:num->real) ((sub:num->num) k)) ((EN:num->real->real^3->A) ((sub:num->num) k))`
  (LABEL_TAC "one") THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `(sub:num->num) k`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)) /\
    mfd_dist (rfs_vtop (V ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
             (rfs_vmetric (V ((sub:num->num) k)) (&0))
             ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1)) <=
    A + &5 * C / eps`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o REWRITE_RULE[p2bt_one]) THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`] P2BT_ONE_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`] P2BTL_GAMMA_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "gd") THEN
  (* the per-index facts *)
  SUBGOAL_THEN
   `!i. i <= n
        ==> IMAGE ((e:int->real^3->B)(&i)) (rfs_neck_dom (&5 / &2 * eps)) SUBSET (W:num->B->bool) k /\
            rfs_neck (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
                     (rfs_vmetric (V ((sub:num->num) k)) (&0)) (&3 * eps)
                     ((phi:num->B->A) k ((x:int->B)(&i))) (phi k o e(&i)) /\
            &1 <= mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
                             (rfs_vmetric (V ((sub:num->num) k)) (&0)) (phi k (x(&i))) /\
            ?t'. &0 <= t' /\ t' <= &1 /\
                 mfd_joinable (rfs_vtop (V ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
                              (phi k (x(&i))) ((gamma:num->real->A) ((sub:num->num) k) t') /\
                 mfd_dist (rfs_vtop (V ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
                          (rfs_vmetric (V ((sub:num->num) k)) (&0)) (phi k (x(&i)))
                          (gamma ((sub:num->num) k) t') <=
                 &5 * inv(sqrt(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
                                          (rfs_vmetric (V ((sub:num->num) k)) (&0)) (phi k (x(&i)))))`
  (LABEL_TAC "pts") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "evk" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "rl" (MP_TAC o SPECL ([`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`; `(x:int->B)(&i)`])) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "arc" (MP_TAC o SPECL ([`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
     `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`; `A1:real`; `(phi:num->B->A) k ((x:int->B)(&i))`])) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "lim" (MP_TAC o CONJUNCT1 o SPEC `k:num` o el 8 o CONJUNCTS o REWRITE_RULE[p2bt_lim]) THEN
      BETA_TAC THEN UNDISCH_TAC `((x:int->B)(&i)) IN (W:num->B->bool) k` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sak" (MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
     `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`; `eps:real`;
     `x:int->B`; `e:int->real^3->B`; `n:num`; `(gamma:num->real->A) ((sub:num->num) k)`;
     `mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
               (rfs_vmetric (V ((sub:num->num) k)) (&0))
               ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL ([`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`; `k:num`; `(x:int->B)(&i)`; `(x:int->B)(&j)`]) P2BTL_CUT_DIST) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `S' = sum(0..n) (\i. inv(sqrt(mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
                     (rfs_vmetric (V ((sub:num->num) k)) (&0)) ((phi:num->B->A) k ((x:int->B)(&i))))))` THEN
  DISCH_TAC THEN
  (* back to the limit *)
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * S'` THEN CONJ_TAC THENL
   [EXPAND_TAC "S'" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "evk" (MP_TAC o C MATCH_MP (ASSUME `i:num <= n`)) THEN STRIP_TAC THEN
    USE_THEN "rl" (MP_TAC o SPECL ([`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`; `(x:int->B)(&i)`])) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC P2BTL_H_COMPARE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps * (&5 * C / eps) = &5 * C` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(eps = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&40 * eps * mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0),rfs_vatlas (V ((sub:num->num) k)) (&0))
               (rfs_vmetric (V ((sub:num->num) k)) (&0))
               ((gamma:num->real->A) ((sub:num->num) k) (&0)) (gamma ((sub:num->num) k) (&1)) <=
    &40 * eps * (A + &5 * C / eps)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= eps * A` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

