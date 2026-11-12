(* ========================================================================= *)
(* Unit pc_p2b_x2s (Part 2B, MT Cor 9.49 with Cor 9.52 for shrinker flows): *)
(* the route X2s,                                                            *)
(*   P2BX2_SCYL_ROUTE |- !w. P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT w. *)
(* The statement X2s: for every sequence pp k leaving compact sets with      *)
(* R(G(-1))(pp k) -> L > 0, where R <= L + e outside a compact set for     *)
(* every e > 0 (L >= the limsup of R at infinity), a subsequence has the   *)
(* based limit at time -1 normalized by R(pp(sub k)) on s <= 0, with        *)
(* R(xl,0) = 1, the limit flow upto 0, and the limit is the cylinder model. *)
(* Proof: X0 at the given points (P2BX2_SPLIT_AT_PTS: no point picking; the *)
(* balls B(pp k, A/sqrt R(pp k)) eventually avoid the compact set, so       *)
(* R <= 3L/2 <= 4 R(pp k) there), then the X2 steps (class, lorient,        *)
(* SPLIT_ROUND, the model at time 0).  d(p,pp k) -> infinity (compact       *)
(* closed balls), so R d^2 -> infinity.                                      *)
(* ========================================================================= *)

needs "src/pc_p2b_x2.ml";;
needs "src/pc_p2b_x0lim.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Real sequences, the scalar curvature bound at time -1, distances to       *)
(* points leaving compact sets, X2s from X2, and the route.                  *)
(* ========================================================================= *)

(* a k -> l > 0 and d k -> infinity give a k d k^2 -> infinity. *)

let P2BX2_PROD_DIVERGE = prove
 (`!(a:num->real) d l.
     (a ---> l) sequentially /\ &0 < l /\ (!M. ?N. !k. N <= k ==> M < d k)
     ==> !M. ?N. !k. N <= k ==> M < a k * d k pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `M:real` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `l / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 + &2 * abs M / l`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `l / &2 < (a:num->real) k /\ &1 + &2 * abs M / l < (d:num->real) k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs(x - l) < l / &2 ==> l / &2 < x`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * abs M / l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:num->real) k <= d k pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `l / &2 * (&2 * abs M / l) = abs M` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < l` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `l / &2 * (d:num->real) k` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `l / &2 * (&2 * abs M / l)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a:num->real) k * d k` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

(* Squeeze along a subsequence: a(sub k) <= b k <= l and a -> l give b -> l. *)

let P2BX2_SQUEEZE_SUBSEQ = prove
 (`!(a:num->real) b l sub.
     p3_subseq sub /\ (a ---> l) sequentially /\ (!k. a(sub k) <= b k /\ b k <= l)
     ==> (b ---> l) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "le"))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((a:num->real)((sub:num->num) k) - l) < e` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `sub:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_ARITH_TAC;
    USE_THEN "le" (MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC]);;

(* Scalar curvature at time -1: positive everywhere and at most 6C, so its *)
(* sup is positive and bounds every value.                                   *)

let P2BX2_SCAL_SUP = prove
 (`!kappa top atlas (G:real->B->real^3^3) C.
     p2b_ancflow0 kappa (top,atlas) G (&0) /\
     (!t x. t < &0 /\ x IN topspace top ==> mfd_rm_norm atlas (G t) x <= C / abs t) /\
     (!t x u v. t < &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 < mfd_sectional atlas (G t) x u v)
     ==> &0 < sup {mfd_scalar atlas (G(--(&1))) x | x IN topspace top} /\
         !x. x IN topspace top
             ==> &0 < mfd_scalar atlas (G(--(&1))) x /\
                 mfd_scalar atlas (G(--(&1))) x <=
                 sup {mfd_scalar atlas (G(--(&1))) x | x IN topspace top}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm") (LABEL_TAC "sec"))) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `G:real->B->real^3^3`; `&0`] P2BX0_ANC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((G:real->B->real^3^3) (--(&1)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `basis 1:real^3` P2BX0_NONCOLLINEAR_EXISTS) THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `u0:real^3`) THEN
  SUBGOAL_THEN `!x. x IN topspace top
                    ==> &0 < mfd_scalar atlas ((G:real->B->real^3^3) (--(&1))) x /\
                        mfd_scalar atlas (G(--(&1))) x <= &6 * C`
  (LABEL_TAC "rb") THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(G:real->B->real^3^3) (--(&1))`; `x:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(G:real->B->real^3^3) (--(&1))`; `x:B`; `u0:real^3`; `basis 1:real^3`]
                  MFD_SECTIONAL_LE_RM_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sec" (MP_TAC o SPECL [`--(&1)`; `x:B`; `u0:real^3`; `basis 1:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ARITH `--(&1) < &0`]; ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    USE_THEN "rm" (MP_TAC o SPECL [`--(&1)`; `x:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ARITH `--(&1) < &0`]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_1; REAL_DIV_1] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(G:real->B->real^3^3) (--(&1))`; `x:B`; `C:real`]
                  P2BFF_MFD_SCALAR_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top
                    ==> mfd_scalar atlas ((G:real->B->real^3^3) (--(&1))) x <=
                        sup {mfd_scalar atlas (G(--(&1))) x | x IN topspace top}`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `&6 * C` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `?x0:B. x0 IN topspace top` (X_CHOOSE_TAC `x0:B`) THENL
   [UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (G:real->B->real^3^3) (&0)` THEN
    REWRITE_TAC[p2b_ancflow0] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((G:real->B->real^3^3) (--(&1))) x0` THEN ASM_SIMP_TAC[]);;

(* Points leaving every compact set go to infinity (compact closed balls of *)
(* a complete connected manifold, MFD_HOPF_RINOW_POINT and GEOH_CBALL_COMPACT). *)

let P2BX2_LEAVE_DIST = prove
 (`!top atlas (g:B->real^3^3) p (pp:num->B).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\ p IN topspace top /\
     (!k. pp k IN topspace top) /\
     (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S))
     ==> !M. ?N. !k. N <= k ==> M < mfd_dist (top,atlas) g p (pp k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `M:real` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`] MFD_HOPF_RINOW_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `M:real`] GEOH_CBALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `mfd_cball (top,atlas) (g:B->real^3^3) p M`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `p:B`;
                 `(pp:num->B) k`] MFD_JOINABLE_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* A compact set lies at bounded distance from a point of a connected      *)
(* manifold (open balls cover it).                                           *)

let P2BX2_COMPACT_DIST_BOUND = prove
 (`!top atlas (g:B->real^3^3) p S.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     connected_space top /\ p IN topspace top /\ compact_in top S
     ==> ?B. !x. x IN S ==> mfd_dist (top,atlas) g p x <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [compact_in]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `IMAGE (\n. mfd_ball (top,atlas) (g:B->real^3^3) p (&n)) (:num)`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `mfd_dist (top,atlas) (g:B->real^3^3) p x` REAL_ARCH_LT) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\n. mfd_ball (top,atlas) (g:B->real^3^3) p (&n)`; `(:num)`;
                 `V:(B->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_FINITE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN EXISTS_TAC `&a:real` THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. n IN s /\ (x:B) IN mfd_ball (top,atlas) (g:B->real^3^3) p (&n)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `S SUBSET UNIONS (V:(B->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:B) IN mfd_ball (top,atlas) (g:B->real^3^3) p (&n)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n:real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE]);;

(* ========================================================================= *)
(* X0 at prescribed points.  When the given points already satisfy the       *)
(* curvature bound of the point picking (R <= 4 R(q0 k) on the balls), the   *)
(* X0 limit can be taken along a subsequence of them.  The proof is that of  *)
(* P2BX0_SPLIT_BODY (pc_p2b_x0) with the point picking step removed (copied  *)
(* and adapted; the X0 lemmas are reused).                                   *)
(* ========================================================================= *)

let P2BX2_SPLIT_AT_PTS = prove
 (`!w:B->bool.
     LIM_DIST_STATEMENT w w /\ LIM_BALL_STATEMENT w w /\ LIM_KNC_STATEMENT w w /\
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) b s0 p q0.
           p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\ p IN topspace top /\
           (!k. q0 k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q0 k)) /\
           (!M. ?N. !k. N <= k
                        ==> M < mfd_scalar atlas (g s0) (q0 k) *
                                mfd_dist (top,atlas) (g s0) p (q0 k) pow 2) /\
           (!A. ?N. !k y. N <= k /\
                          y IN mfd_ball (top,atlas) (g s0) (q0 k)
                                        (A * inv(sqrt(mfd_scalar atlas (g s0) (q0 k))))
                          ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q0 k))
           ==> ?sub (top':B topology) atlas' g' xl W phi X.
                  p3_subseq sub /\
                  p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s < b} g) (q0 o sub)
                                      (\k. s0) (\k. mfd_scalar atlas (g s0) ((q0 o sub) k))
                                      {s | s <= &0} (top',atlas') g' xl W phi /\
                  connected_space top' /\
                  (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
                  (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s)) /\
                  (!s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                             ==> &0 <= mfd_sectional atlas' (g' s) y u v) /\
                  mfd_scalar atlas' (g'(&0)) xl = &1 /\
                  (?K. !s y. s <= &0 /\ y IN topspace top' ==> mfd_rm_norm atlas' (g' s) y <= K) /\
                  (!r0. rfs_kappa_noncollapsed (rfs_flow_view (top',atlas') {s | s <= &0} g')
                                               kappa r0) /\
                  (!s y dR. s <= &0 /\ y IN topspace top' /\
                            ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                            ==> &0 <= dR) /\
                  p2b_gsplit (top',atlas') g' {s | s <= &0} X`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "L2")
    (CONJUNCTS_THEN2 (LABEL_TAC "L3") (CONJUNCTS_THEN2 (LABEL_TAC "L5")
    (CONJUNCTS_THEN2 (LABEL_TAC "L6") (LABEL_TAC "AC")))))) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s0:real`; `p:B`; `q0:num->B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "q0")
      (CONJUNCTS_THEN2 (LABEL_TAC "q0div") (LABEL_TAC "q0balls")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0_ANC_BASIC) THEN
  (* facts at time s0 *)
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0) /\
                mfd_complete (top,atlas) (g s0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) s0) y u v`
  (LABEL_TAC "sec0") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `q0:num->B`] P2BX0_DIST_DIVERGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "q0" (fun th -> REWRITE_TAC[th]);
    DISCH_THEN(LABEL_TAC "q0far")] THEN
  (* almost-line pairs along q0 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `q0:num->B`;
                 `\n. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q0:num->B) n)`]
                P2BX0_ALMOST_PAIRS) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `suba:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pairs"))) THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) k` (LABEL_TAC "subage") THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the X0 limit along q0 o suba *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s0:real`; `(q0:num->B) o (suba:num->num)`] P2BX0_LIMIT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "q0balls" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "subage" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subb:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xlim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "comp0")))))))))))) THEN
  USE_THEN "xlim" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
                             STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th)) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!s. s <= &0 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) ((subb:num->num) k)` (LABEL_TAC "subge") THENL
   [MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    USE_THEN "subage" (MP_TAC o SPEC `(subb:num->num) k`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. ?N. !k y. N <= k /\
                  y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0)
                         ((((q0:num->B) o (suba:num->num)) o (subb:num->num)) k)
                         (A * inv(sqrt(mfd_scalar atlas (g s0) (((q0 o suba) o subb) k))))
                  ==> mfd_scalar atlas (g s0) y <=
                      &4 * mfd_scalar atlas (g s0) (((q0 o suba) o subb) k)`
  (LABEL_TAC "qballs") THENL
   [REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "q0balls" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "subge" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* X0.6: the limit properties *)
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_COMPLETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "compall")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_SEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "secl")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_R1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "r1")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_R4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "r4")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_RM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "rm")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_DRDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "drds")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_KNC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "knc")] THEN
  (* X0.8: exact pairs at time 0, then a line *)
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?a b. a IN topspace top' /\ b IN topspace top' /\
                  mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl a = A /\
                  mfd_dist (top',atlas') (g' (&0)) xl b = A /\
                  mfd_dist (top',atlas') (g' (&0)) a b = &2 * A`
  (LABEL_TAC "lpairs") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`w:B->bool`; `w:B->bool`;
      `\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
      `((q0:num->B) o (suba:num->num)) o (subb:num->num)`; `\k:num. (s0:real)`;
      `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0)
                      ((((q0:num->B) o (suba:num->num)) o (subb:num->num)) k)`;
      `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `A:real`]
     P2BX0_LIMIT_PAIRS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS; IN_ELIM_THM; o_THM] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pairs" (MP_TAC o SPECL [`A:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPEC `(subb:num->num) k`) THEN
    ANTS_TAC THENL
     [MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `xl:B`] P2BX0_LINE_FROM_PAIRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real->B` (LABEL_TAC "line")) THEN
  (* X0.9: the splitting field at time 0 *)
  MP_TAC(SPEC `w:B->bool` CMP_R3_SPLIT) THEN REWRITE_TAC[CMP_R3_SPLIT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `(g':real->B->real^3^3) (&0)`; `lam:real->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "secl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC)) THEN
  (* X0.10: time invariance *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `X:B->real^3`; `xl:B`; `&2`] P2BX0_TIME_INVARIANCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the conclusion *)
  SUBGOAL_THEN `p3_subseq ((suba:num->num) o (subb:num->num))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?K. !s y. s <= &0 /\ y IN topspace top'
                          ==> mfd_rm_norm atlas' ((g':real->B->real^3^3) s) y <= K`
  ASSUME_TAC THENL [EXISTS_TAC `&2` THEN USE_THEN "rm" ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(suba:num->num) o (subb:num->num)`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `X:B->real^3`] THEN
  REWRITE_TAC[o_ASSOC] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* X2s: the cylinder limit at a subsequence of                              *)
(* the GIVEN points pp k, normalized by R(pp(sub k)), with R(xl,0) = 1.     *)
(* No point picking: R <= sup R <= 4 R(pp k) for large k.                    *)
(* ========================================================================= *)

let P2BX2_SCYL_BODY = prove
 (`!w:B->bool.
     LIM_DIST_STATEMENT w w /\ LIM_BALL_STATEMENT w w /\ LIM_KNC_STATEMENT w w /\
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_SPLIT_ROUND_STATEMENT w
     ==> P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT w`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sr"))))))) THEN
  MP_TAC(SPEC `w:B->bool` P2BX2_SPLIT_AT_PTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "pts")] THEN
  REWRITE_TAC[P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `G:real->B->real^3^3`; `C:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rm") (LABEL_TAC "sec")))) THEN
  X_GEN_TAC `pp:num->B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ppin")
    (CONJUNCTS_THEN2 (LABEL_TAC "ppleave") (X_CHOOSE_THEN `L:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pplim") (LABEL_TAC "Loff")))))) THEN
  SUBGOAL_THEN `p2b_ancflow0 kappa (top,atlas) (G:real->B->real^3^3) (&0) /\
                p2b_ksep top atlas` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_ancflow kappa (top,atlas) (G:real->B->real^3^3) (&0)` THEN
    SIMP_TAC[p2b_ancflow];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `G:real->B->real^3^3`; `&0`] P2BX0_ANC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((G:real->B->real^3^3) (--(&1))) /\
                mfd_complete (top,atlas) ((G:real->B->real^3^3) (--(&1)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `G:real->B->real^3^3`; `C:real`] P2BX2_SCAL_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rle")) THEN
  ABBREV_TAC `p = (pp:num->B) 0` THEN
  SUBGOAL_THEN `(p:B) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN USE_THEN "ppin" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. ?N. !k. N <= k
                ==> M < mfd_scalar atlas ((G:real->B->real^3^3) (--(&1))) ((pp:num->B) k) *
                        mfd_dist (top,atlas) (G(--(&1))) p (pp k) pow 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\k:num. mfd_scalar atlas ((G:real->B->real^3^3) (--(&1))) ((pp:num->B) k)`;
      `\k:num. mfd_dist (top,atlas) ((G:real->B->real^3^3) (--(&1))) p ((pp:num->B) k)`;
      `L:real`] P2BX2_PROD_DIVERGE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(G:real->B->real^3^3) (--(&1))`; `p:B`; `pp:num->B`] P2BX2_LEAVE_DIST) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. ?N. !k y. N <= k /\
                  y IN mfd_ball (top,atlas) ((G:real->B->real^3^3) (--(&1))) ((pp:num->B) k)
                         (A * inv(sqrt(mfd_scalar atlas (G(--(&1))) (pp k))))
                  ==> mfd_scalar atlas (G(--(&1))) y <=
                      &4 * mfd_scalar atlas (G(--(&1))) (pp k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `A:real` THEN
    USE_THEN "Loff" (MP_TAC o SPEC `L / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "off"))) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(G:real->B->real^3^3) (--(&1))`; `p:B`; `S:B->bool`]
      P2BX2_COMPACT_DIST_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `Bd:real` (LABEL_TAC "bd"))] THEN
    USE_THEN "pplim" (MP_TAC o SPEC `L / &4` o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1"))] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(G:real->B->real^3^3) (--(&1))`; `p:B`; `pp:num->B`] P2BX2_LEAVE_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `Bd + abs A * inv(sqrt(&3 * L / &4))`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
    EXISTS_TAC `N1 + N2:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `y:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&3 * L / &4 < mfd_scalar atlas ((G:real->B->real^3^3) (--(&1))) ((pp:num->B) k)`
    ASSUME_TAC THENL
     [USE_THEN "N1" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `Bd + abs A * inv(sqrt(&3 * L / &4)) <
                  mfd_dist (top,atlas) ((G:real->B->real^3^3) (--(&1))) p ((pp:num->B) k)`
    ASSUME_TAC THENL
     [USE_THEN "N2" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((G:real->B->real^3^3) (--(&1))) ((pp:num->B) k)
                   (A * inv(sqrt(mfd_scalar atlas (G(--(&1))) (pp k))))` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `A * inv(sqrt(mfd_scalar atlas ((G:real->B->real^3^3) (--(&1))) ((pp:num->B) k))) <=
      abs A * inv(sqrt(&3 * L / &4))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs A * inv(sqrt(mfd_scalar atlas ((G:real->B->real^3^3) (--(&1)))
                                     ((pp:num->B) k)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
        MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((y:B) IN S)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `mfd_dist (top,atlas) ((G:real->B->real^3^3) (--(&1))) p (y:B) <= Bd`
      ASSUME_TAC THENL [USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `mfd_dist (top,atlas) ((G:real->B->real^3^3) (--(&1))) p ((pp:num->B) k) <=
        mfd_dist (top,atlas) (G(--(&1))) p (y:B) + mfd_dist (top,atlas) (G(--(&1))) y (pp k)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[MFD_JOINABLE_SYM]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `mfd_dist (top,atlas) ((G:real->B->real^3^3) (--(&1))) (y:B) ((pp:num->B) k) =
        mfd_dist (top,atlas) (G(--(&1))) (pp k) y`
      ASSUME_TAC THENL [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "off" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(y:B) IN topspace top`) (ASSUME `~((y:B) IN S)`))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "pts" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                  `atlas:((B->bool)#(B->real^3))->bool`; `G:real->B->real^3^3`;
                                  `&0`; `--(&1)`; `p:B`; `pp:num->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `--(&1) < &0`] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "ppin" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "rle" (MP_TAC o C MATCH_MP (SPEC `k:num` (ASSUME `!k. (pp:num->B) k IN topspace top`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC)))))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM]) THEN
  SUBGOAL_THEN `p2b_ancflow0 kappa (top':B topology,atlas') g' (&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:A`] P2BX2_LIMIT_CLASS) THEN
    MAP_EVERY EXISTS_TAC [`\k:num. rfs_flow_view (top,atlas) {s | s < &0} (G:real->B->real^3^3)`;
                          `(pp:num->B) o (sub:num->num)`; `\k:num. --(&1)`;
                          `\k:num. mfd_scalar atlas ((G:real->B->real^3^3) (--(&1)))
                                     ((pp:num->B) ((sub:num->num) k))`;
                          `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (G:real->B->real^3^3) (&0)` THEN
      SIMP_TAC[p2b_ancflow0];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_lorient (top':B topology) atlas'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX2_LIMIT_LORIENT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `G:real->B->real^3^3`; `&0`; `--(&1)`; `(pp:num->B) o (sub:num->num)`;
                          `\k:num. mfd_scalar atlas ((G:real->B->real^3^3) (--(&1)))
                                     ((pp:num->B) ((sub:num->num) k))`;
                          `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                          `phi:num->B->B`] THEN
    ASM_REWRITE_TAC[REAL_ARITH `--(&1) < &0`];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_gsplit (top':B topology,atlas') g' {s | s < &0} X` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_gsplit (top':B topology,atlas') g' {s | s <= &0} X` THEN
    REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_cyl_model (top':B topology,atlas') g'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX2_MODEL_AT_ZERO THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sr" (MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                                   `atlas':((B->bool)#(B->real^3))->bool`;
                                   `g':real->B->real^3^3`; `&0`; `X:B->real^3`] o
                   REWRITE_RULE[P2B_SPLIT_ROUND_STATEMENT]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
  ASM_REWRITE_TAC[]);;

(* The route: SPLIT_ROUND and ANCIENT_COMPACT with the proved LIM theorems  *)
(* (the pc_lim units, loaded through pc_p2b_x0lim); SPLIT_AT_INFINITY and   *)
(* FLAT_FORWARD are not needed.                                              *)

let P2BX2_SCYL_ROUTE = prove
 (`!w:B->bool. P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN MATCH_MP_TAC P2BX2_SCYL_BODY THEN
  ASM_REWRITE_TAC[LIM_DIST; LIM_BALL; LIM_KNC; LIM_CURV; LIM_FLOW_COMPLETE_BACK]);;

