(* ========================================================================= *)
(* Unit pc_p2c_stdc1 (Part 2C; MT Ch 12): MT Thm 12.28 for the maximal       *)
(* standard flow Gs on [0,Tm): for 0 < eps <= eps1 there are C and r such    *)
(* that every point with R >= r^-2 has t > r^2 and a canonical neighbourhood *)
(* in the sense of p2b_canon_L with necks of length 1 + eps.  Point picking  *)
(* (MT's proof), the blow-up hypotheses of P2C_THM_11_8_VIEW for the flow    *)
(* view of Gs, the kappa-solution limit and P2B_COR_9_95_VIEW_FIX.           *)
(* Noncollapsing is the input P2C_STD_NONCOLL_STATEMENT.                     *)
(* ========================================================================= *)

needs "src/pc_p2c_stdres.ml";;
needs "src/pc_p2c_stdncs.ml";;
needs "src/pc_p2b_slice.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The flow view of the maximal standard flow and its basic                *)
(* properties: regular, empty before 0, pinched (sec >= 0 gives R >= 0),    *)
(* sphere-separating (R^3 is simply connected), orientable, complete        *)
(* slices, persisting sets, bounded scalar curvature on [0,t1], t1 < Tm.    *)
(* ------------------------------------------------------------------------- *)

let stds_gv = new_definition
 `stds_gv (g0:real^3->real^3^3) =
    rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < stds_tm g0}
                  (stds_gs g0)`;;

let STDS_GV_PARTS = prove
 (`!g0 s.
     rfs_vtop (stds_gv g0) s =
       (if &0 <= s /\ s < stds_tm g0 then euclidean else discrete_topology {}) /\
     rfs_vatlas (stds_gv g0) s = open_set_atlas (:real^3) /\
     rfs_vmetric (stds_gv g0) s = stds_gs g0 s`,
  REWRITE_TAC[stds_gv; P2CF_FLOW_VIEW_PARTS; IN_ELIM_THM]);;

let STDS_GV_TOPSPACE = prove
 (`!g0 s (x:real^3). x IN topspace(rfs_vtop (stds_gv g0) s) <=>
                     &0 <= s /\ s < stds_tm g0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STDS_GV_PARTS] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]);;

let STDS_EUCLID_ORIENTABLE = prove
 (`mfd_orientable (euclidean:(real^3)topology) (open_set_atlas (:real^3))`,
  REWRITE_TAC[mfd_orientable] THEN EXISTS_TAC `open_set_atlas (:real^3)` THEN
  REWRITE_TAC[UNION_IDEMPOT; P2C_EUCLID_FACTS; mfd_oriented_atlas;
              RFB_OPEN_SET_ATLAS_CASES] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `(:real^3)`;
                 `\x:real^3. x`; `x:real^3`] CHART_JAC_SELF) THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; RFB_OPEN_SET_ATLAS_CASES; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_ID; DET_I; REAL_LT_01]);;

(* The basic facts, for any flow G from g0 on [0,Tm) with sec >= 0 (applied  *)
(* to the maximal flow).                                                     *)

let STDS_GV_FACTS = prove
 (`!g0 A0.
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ APX_SC_SPHERE_SEP_STATEMENT (:real^3) /\
     (!t x u v. &0 <= t /\ t < stds_tm g0 /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t) x u v)
     ==> p2c_regular_view (stds_gv g0) /\
         (!s. s < &0 ==> rfs_vtop (stds_gv g0) s = discrete_topology {}) /\
         rfs_pinched (stds_gv g0) /\
         (!s. apx_sphere_sep (rfs_vtop (stds_gv g0) s) (rfs_vatlas (stds_gv g0) s)) /\
         (!s. ~(topspace(rfs_vtop (stds_gv g0) s) = {})
              ==> mfd_orientable (rfs_vtop (stds_gv g0) s) (rfs_vatlas (stds_gv g0) s)) /\
         (!s. &0 <= s /\ s < stds_tm g0
              ==> mfd_complete (rfs_vtop (stds_gv g0) s,rfs_vatlas (stds_gv g0) s)
                               (rfs_vmetric (stds_gv g0) s)) /\
         (!W a b. &0 <= a /\ b < stds_tm g0 /\ open W
                  ==> rfs_persists (stds_gv g0) W a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (stds_tm g0)
                  (stds_gs g0)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
    SIMP_TAC[p3_partial_std];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < stds_tm g0
                    ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[STDS_RIEM_UNIV_EQ] THEN
    ASM_MESON_TAC[STDS_RT_METRIC_FIELD];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[stds_gv] THEN
    MATCH_MP_TAC(REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT]
                   (ISPEC `(:real^3)` P2C_FLOW_VIEW_REGULAR)) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    REPEAT STRIP_TAC THEN REWRITE_TAC[STDS_GV_PARTS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[stds_gv; rfs_flow_view; rfs_pinched; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN COND_CASES_TAC THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    STRIP_TAC THEN REWRITE_TAC[rfs_pinched_at] THEN
    SUBGOAL_THEN `&0 <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `stds_gs g0 t`; `x:real^3`; `&0`] P2BS_MFD_SCALAR_SECT) THEN
      ASM_SIMP_TAC[P2C_EUCLID_FACTS; IN_UNIV; REAL_MUL_RZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_sec_min (open_set_atlas (:real^3)) (stds_gs g0 t) x`
    ASSUME_TAC THENL
     [REWRITE_TAC[mfd_sec_min] THEN MATCH_MP_TAC REAL_LE_INF THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t) x
                                (basis 1) (basis 2)`;
                              `basis 1:real^3`; `basis 2:real^3`] THEN
        REWRITE_TAC[P3S_NONCOLL_BASIS];
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LE0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[STDS_GV_PARTS] THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `APX_SC_SPHERE_SEP_STATEMENT (:real^3)` THEN
      REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[P2C_EUCLID_FACTS] THEN X_GEN_TAC `U:real^3->bool` THEN
      SUBGOAL_THEN `connected_components_of (euclidean:(real^3)topology) = {(:real^3)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING; P2C_EUCLID_FACTS; UNIV_NOT_EMPTY];
        ALL_TAC] THEN
      REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EUCLIDEAN] THEN
      SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_UNIV];
      REWRITE_TAC[apx_sphere_sep; mfd_neck_chart; mfd_param; mfd_diffeo] THEN
      X_GEN_TAC `e:real^3->real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `open_in (discrete_topology {})
                     (IMAGE (e:real^3->real^3) (annulus (&1 / &2) (&2)))` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
      MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^3` THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[STDS_GV_PARTS] THEN COND_CASES_TAC THEN
    REWRITE_TAC[STDS_EUCLID_ORIENTABLE; TOPSPACE_DISCRETE_TOPOLOGY];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[STDS_GV_PARTS] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[P2CO_PERSISTS_ALT; STDS_GV_PARTS] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s /\ s < stds_tm g0` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; OPEN_IN_EUCLIDEAN]]);;

(* ------------------------------------------------------------------------- *)
(* Point picking (MT's proof of Thm 12.28).  If a property P                *)
(* of space-time points fails at points of arbitrarily large R, and R is    *)
(* bounded on [0,t1] for every t1 < T, then there are failing points        *)
(* (x_n,t_n) with R(x_n,t_n) -> inf and t_n -> T such that P holds at every *)
(* (y,s), s <= t_n, with R(y,s) > 2 R(x_n,t_n): R_n is the sup of R over     *)
(* failing points with t <= T - T/(n + 2), and R(x_n,t_n) > R_n / 2.         *)
(* ------------------------------------------------------------------------- *)

let STDS_PICK = prove
 (`!(P:real^3->real->bool) (R:real^3->real->real) TT.
     &0 < TT /\
     (!t1. t1 < TT ==> ?K. !x t. &0 <= t /\ t <= t1 ==> R x t <= K) /\
     ~(?B. !x t. &0 <= t /\ t < TT /\ B <= R x t ==> P x t)
     ==> ?(x:num->real^3) (t:num->real).
           (!n. &0 <= t n /\ t n < TT /\ ~P (x n) (t n) /\ &0 < R (x n) (t n)) /\
           (!B. ?N. !n. N <= n ==> B < R (x n) (t n)) /\
           (!e. &0 < e ==> ?N. !n. N <= n ==> TT - e < t n) /\
           (!n y s. &0 <= s /\ s <= t n /\ &2 * R (x n) (t n) < R y s ==> P y s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bd") MP_TAC)) THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP] THEN DISCH_THEN(LABEL_TAC "neg") THEN
  ABBREV_TAC `tp = \n:num. TT - TT / (&n + &2)` THEN
  SUBGOAL_THEN `!n. &0 <= (tp:num->real) n /\ tp n < TT /\
                    (!m. m <= n ==> tp m <= tp n)` (LABEL_TAC "tp") THENL
   [GEN_TAC THEN EXPAND_TAC "tp" THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 < &n + &2` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < TT /\ TT * &1 <= TT * x ==> TT <= TT * x`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> TT - x < TT`) THEN ASM_SIMP_TAC[REAL_LT_DIV];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `b <= a ==> TT - a <= TT - b`) THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_ARITH `&0 < &m + &2`] THEN
      UNDISCH_TAC `m:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?N. !n. N <= n ==> TT - e < (tp:num->real) n`
  (LABEL_TAC "tpl") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `TT / e` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "tp" THEN
    BETA_TAC THEN MATCH_MP_TAC(REAL_ARITH `x < e ==> TT - e < TT - x`) THEN
    SUBGOAL_THEN `&0 < &n + &2` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `TT / e <= &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = \n. (&0) INSERT {(R:real^3->real->real) x t | x,t |
                                   &0 <= t /\ t <= (tp:num->real) n /\ ~P x t}` THEN
  SUBGOAL_THEN
   `!n z. z IN (S:num->real->bool) n <=>
          z = &0 \/ ?x t. &0 <= t /\ t <= (tp:num->real) n /\ ~P x t /\
                          z = (R:real^3->real->real) x t`
  (LABEL_TAC "sm") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ~((S:num->real->bool) k = {}) /\ (?b. !z. z IN S k ==> z <= b)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `&0` THEN USE_THEN "sm" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    USE_THEN "bd" (MP_TAC o SPEC `(tp:num->real) k`) THEN
    USE_THEN "tp" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC `k:num` th))]) THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN EXISTS_TAC `max (&0) K` THEN
    X_GEN_TAC `z:real` THEN USE_THEN "sm" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Rs = \n. sup((S:num->real->bool) n)` THEN
  SUBGOAL_THEN
   `!k. (!z. z IN (S:num->real->bool) k ==> z <= (Rs:num->real) k) /\
        (!b. (!z. z IN S k ==> z <= b) ==> Rs k <= b)`
  (LABEL_TAC "sup") THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "Rs" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (!x t. &0 <= t /\ t <= (tp:num->real) n /\ ~P x t
               ==> (R:real^3->real->real) x t <= (Rs:num->real) n) /\
        &0 <= Rs n /\
        (&0 < Rs n ==> ?x t. &0 <= t /\ t <= tp n /\ ~P x t /\ Rs n / &2 < R x t) /\
        (!m. m <= n ==> Rs m <= Rs n)`
  (LABEL_TAC "rs") THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "sup" (MATCH_MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
      USE_THEN "sm" (fun th -> REWRITE_TAC[th]) THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^3`; `t:real`] THEN ASM_REWRITE_TAC[];
      USE_THEN "sup" (MATCH_MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
      USE_THEN "sm" (fun th -> REWRITE_TAC[th]);
      DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `(Rs:num->real) n <= Rs n / &2` MP_TAC THENL
       [USE_THEN "sup" (MATCH_MP_TAC o CONJUNCT2 o SPEC `n:num`) THEN
        X_GEN_TAC `z:real` THEN USE_THEN "sm" (fun th -> REWRITE_TAC[th]) THEN
        STRIP_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN ASM_REWRITE_TAC[]];
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      USE_THEN "sup" (MATCH_MP_TAC o CONJUNCT2 o SPEC `m:num`) THEN
      X_GEN_TAC `z:real` THEN DISCH_TAC THEN
      USE_THEN "sup" (MATCH_MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
      UNDISCH_TAC `(z:real) IN (S:num->real->bool) m` THEN
      USE_THEN "sm" (fun th -> REWRITE_TAC[th]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^3`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(tp:num->real) m` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "tp" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* Rs is unbounded *)
  SUBGOAL_THEN `!M. ?n. M < (Rs:num->real) n` (LABEL_TAC "unb") THENL
   [X_GEN_TAC `M:real` THEN USE_THEN "neg" (MP_TAC o SPEC `M + &1`) THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC)) THEN
    USE_THEN "tpl" (MP_TAC o SPEC `TT - t0`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN EXISTS_TAC `N:num` THEN
    USE_THEN "rs" (MP_TAC o CONJUNCT1 o SPEC `N:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`x0:real^3`; `t0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "unb" (X_CHOOSE_TAC `N0:num` o SPEC `&0`) THEN
  SUBGOAL_THEN
   `!n. ?x t. &0 <= t /\ t <= (tp:num->real) (n + N0) /\ ~P x t /\
              (Rs:num->real) (n + N0) / &2 < (R:real^3->real->real) x t`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "rs" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                                SPEC `n + N0:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(Rs:num->real) N0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rs" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `n + N0:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:num->real^3` (X_CHOOSE_THEN `t:num->real`
      (LABEL_TAC "pick")) o REWRITE_RULE[SKOLEM_THM])] THEN
  MAP_EVERY EXISTS_TAC [`x:num->real^3`; `t:num->real`] THEN
  SUBGOAL_THEN `!B. ?N. !n. N <= n ==> B < (R:real^3->real->real) ((x:num->real^3) n)
                                                                    ((t:num->real) n)`
  (LABEL_TAC "big") THENL
   [X_GEN_TAC `B:real` THEN USE_THEN "unb" (X_CHOOSE_TAC `N1:num` o SPEC `&2 * B`) THEN
    EXISTS_TAC `N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "pick" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    USE_THEN "rs" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `n + N0:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `N1:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "pick" (MP_TAC o SPEC `n:num`) THEN
    USE_THEN "tp" (MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC `n + N0:num`) THEN
    USE_THEN "rs" (MP_TAC o SPEC `N0:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                   SPEC `n + N0:num`) THEN
    REWRITE_TAC[LE_ADDR] THEN DISCH_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o SPEC `TT - e`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "kb"))] THEN
    USE_THEN "big" (X_CHOOSE_THEN `N:num` (LABEL_TAC "nb") o SPEC `K:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `K < (R:real^3->real->real) ((x:num->real^3) n) ((t:num->real) n)`
    MP_TAC THENL [USE_THEN "nb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(R:real^3->real->real) ((x:num->real^3) n) ((t:num->real) n) <= K`
    MP_TAC THENL
     [USE_THEN "kb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "pick" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
      REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`; `s:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "pick" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    USE_THEN "rs" (MP_TAC o CONJUNCT1 o SPEC `n + N0:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The blow-up hypotheses of Thm 11.8 for the constant view                 *)
(* stds_gv g0 along a picked sequence (MT's proof of Thm 12.28): the view   *)
(* facts above, canonical neighbourhoods above 2 R_n from the picking (an  *)
(* evolving neck of length L >= 1 is a strong neck), noncollapsing from     *)
(* P2C_STD_NONCOLL, and persistence back to t_n - Tb / R_n >= 0 since       *)
(* t_n -> Tm > 0 and R_n -> inf.                                            *)
(* ------------------------------------------------------------------------- *)

let STDS_GV_SCALAR = prove
 (`!g0 t (x:real^3).
     rfs_vscalar (stds_gv g0) t x =
     mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x`,
  REWRITE_TAC[stds_gv; rfs_flow_view; rfs_vscalar]);;

let STDS_GV_BALL = prove
 (`!g0 t (x:real^3) r.
     &0 <= t /\ t < stds_tm g0
     ==> rfs_vball (stds_gv g0) t x r =
         mfd_ball (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) x r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_gv; rfs_flow_view; rfs_vball; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[]);;

let STDS_CLOSE_FAM_SUBSET = prove
 (`!k eps J J' s (G0:real->real^N->real^N^N) G.
     rfs_close_fam k eps J s G0 G /\ J' SUBSET J ==> rfs_close_fam k eps J' s G0 G`,
  REWRITE_TAC[rfs_close_fam; SUBSET] THEN MESON_TAC[]);;

(* p2b_canon_L with L >= 1 at a point of positive scalar curvature gives a *)
(* strong canonical neighbourhood (an evolving neck of length L >= 1       *)
(* restricts to one of length 1).                                          *)

let STDS_CANON_L_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps L x t.
     p2b_canon_L V C eps L x t /\ &1 <= L /\ &0 < rfs_vscalar V t x
     ==> p3_canon_at V C eps x t`,
  REWRITE_TAC[FORALL_PAIR_THM; p2b_canon_L; p3_canon_at; rfs_strong_canonical;
              rfs_strong_neck; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `eps:real`; `L:real`; `x:A`;
                       `t:real`] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN DISJ1_TAC THEN
    EXISTS_TAC `e:real^3->A` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_evolving_neck (TM,AT,G) eps (x:A) t L e` THEN
    REWRITE_TAC[rfs_evolving_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`t - L / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                                  ((G:real->A->real^3^3) t) (x:A)`;
                            `t:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> t - b <= t - a`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      MATCH_MP_TAC STDS_CLOSE_FAM_SUBSET THEN
      EXISTS_TAC `{s | --L < s /\ s <= &0}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* Scalar curvature is bounded above on [0,t1] for t1 < Tm.                   *)

let STDS_GS_RBOUND = prove
 (`!g0 A0 t1.
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ t1 < stds_tm g0
     ==> ?K. !x t. &0 <= t /\ t <= t1
                   ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
  REWRITE_TAC[p3_partial_std] THEN
  DISCH_THEN(MP_TAC o SPEC `t1:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K1:real`) THEN
  X_CHOOSE_THEN `Cs:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SC"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_SCALAR_FROM_RMNORM) THEN
  EXISTS_TAC `Cs * max (&0) K1` THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a <= b`) THEN
  USE_THEN "SC" MATCH_MP_TAC THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; REAL_LE_MAX; REAL_LE_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[STDS_RIEM_UNIV_EQ] THEN MATCH_MP_TAC STDS_RT_METRIC_FIELD THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term ((=) `stds_rotm`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The blow-up hypotheses.                                                   *)

let STDS_BLOWUP_SEQ = prove
 (`!g0 A0 C eps kappa r0 (x:num->real^3) (t:num->real).
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ APX_SC_SPHERE_SEP_STATEMENT (:real^3) /\
     (!t x u v. &0 <= t /\ t < stds_tm g0 /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t) x u v) /\
     &0 < kappa /\ &0 < r0 /\
     (!y s. p3_noncoll_at (stds_gv g0) kappa r0 y s) /\
     (!n. &0 <= t n /\ t n < stds_tm g0 /\ &0 < rfs_vscalar (stds_gv g0) (t n) (x n)) /\
     (!B. ?N. !n. N <= n ==> B < rfs_vscalar (stds_gv g0) (t n) (x n)) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> stds_tm g0 - e < t n) /\
     (!n y s. &0 <= s /\ s <= t n /\
              &2 * rfs_vscalar (stds_gv g0) (t n) (x n) < rfs_vscalar (stds_gv g0) s y
              ==> p3_canon_at (stds_gv g0) C eps y s)
     ==> p2c_vblowup_seq (C,eps,kappa,r0,&1) (\n. stds_gv g0) x t /\
         (!Tb. &0 < Tb ==> p2c_vblowup_back (kappa,r0) (\n. stds_gv g0) x t Tb)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "nc") (CONJUNCTS_THEN2 (LABEL_TAC "tn")
   (CONJUNCTS_THEN2 (LABEL_TAC "big") (CONJUNCTS_THEN2 (LABEL_TAC "tlim")
    (LABEL_TAC "can"))))))))))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "per"))))))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* eventually t n - Tb / R_n > 0 *)
  SUBGOAL_THEN
   `!Tb. &0 < Tb
         ==> ?N. !n. N <= n
                     ==> &0 < (t:num->real) n -
                              Tb * inv(rfs_vscalar (stds_gv g0) (t n) ((x:num->real^3) n))`
  (LABEL_TAC "pos") THENL
   [X_GEN_TAC `Tb:real` THEN DISCH_TAC THEN
    USE_THEN "tlim" (MP_TAC o SPEC `stds_tm g0 / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
    USE_THEN "big" (MP_TAC o SPEC `(&2 * Tb) / stds_tm g0`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `stds_tm g0 - stds_tm g0 / &2 < (t:num->real) n /\
                  (&2 * Tb) / stds_tm g0 < rfs_vscalar (stds_gv g0) (t n) ((x:num->real^3) n)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "tn" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a < t ==> &0 < t - a`) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `stds_tm g0 / &2` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `(&2 * Tb) / stds_tm g0 <
                 rfs_vscalar (stds_gv g0) ((t:num->real) n) ((x:num->real^3) n)` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2c_vblowup_seq] THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[STDS_GV_TOPSPACE] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`; `s:real`] THEN
      REWRITE_TAC[STDS_GV_TOPSPACE] THEN STRIP_TAC THEN
      USE_THEN "can" (MATCH_MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "tn" (MP_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `Aa:real` THEN USE_THEN "pos" (MP_TAC o SPEC `&1`) THEN
      REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[p2c_local_persist] THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[IN_UNIV] THEN USE_THEN "per" MATCH_MP_TAC THEN
      REWRITE_TAC[OPEN_UNIV] THEN USE_THEN "tn" (MP_TAC o SPEC `n:num`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= a ==> &0 < t - a ==> &0 <= t - b`) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `Tb:real` THEN DISCH_TAC THEN REWRITE_TAC[p2c_vblowup_back] THEN
  X_GEN_TAC `Aa:real` THEN USE_THEN "pos" (MP_TAC o SPEC `Tb:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "tn" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  USE_THEN "per" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[STDS_GV_BALL] THEN REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN
  MATCH_MP_TAC MFD_BALL_OPEN THEN REWRITE_TAC[P2C_EUCLID_FACTS; STDS_RIEM_UNIV_EQ] THEN
  MATCH_MP_TAC STDS_RT_METRIC_FIELD THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MT Thm 12.28 for the maximal standard flow.  For                         *)
(* 0 < eps <= eps1 there is C0 > 1 such that for every C >= C0 there is     *)
(* r > 0 with: every (x,t), 0 <= t < Tm, with R(x,t) >= r^-2 has t > r^2    *)
(* and a canonical neighbourhood in the sense of p2b_canon_L with necks of  *)
(* length 1 + eps.  Proof as MT: point picking (STDS_PICK), the blow-up     *)
(* hypotheses (STDS_BLOWUP_SEQ), a kappa-solution limit (Thm 11.8) and Cor  *)
(* 9.95 give the canonical neighbourhoods along the sequence, a             *)
(* contradiction.  The component alternatives are impossible on R^3.        *)
(* ------------------------------------------------------------------------- *)


(* Riemannian slices of Gs. *)

let STDS_GS_RIEM = prove
 (`!g0 A0 t.
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ &0 <= t /\ t < stds_tm g0
     ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t) /\
         metric_field (:real^3) (stds_gs g0 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC STDS_PARTIAL_RIEM THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `stds_tm g0`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[STDS_RIEM_UNIV_EQ]]);;

let STDS_THM_12_28 = prove
 (`!d:real^4->bool.
     stds_gs_hyps /\ PDE_CURVATURE_TIME_STATEMENT d (:3) /\
     P2C_REQ_SEC_PRESERVED_STATEMENT d /\ P2C_PROP_5_14_STATEMENT d (:real^3) /\
     APX_SC_SPHERE_SEP_STATEMENT (:real^3) /\ P2C_STD_NONCOLL_STATEMENT /\
     P2C_THM_11_8_VIEW_STATEMENT (:real^3) (:real^3) /\
     P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3)
     ==> ?eps1. &0 < eps1 /\
           !eps. &0 < eps /\ eps <= eps1
                 ==> ?C0. &1 < C0 /\
                       !C g0 A0.
                          C0 <= C /\ p3_std_initial g0 A0
                          ==> ?r. &0 < r /\
                                !x t. &0 <= t /\ t < stds_tm g0 /\
                                      inv(r pow 2) <=
                                      mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x
                                      ==> r pow 2 < t /\
                                          p2b_canon_L (stds_gv g0) C eps (&1 + eps) x t`,
  GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `P2C_THM_11_8_VIEW_STATEMENT (:real^3) (:real^3)` THEN
  REWRITE_TAC[P2C_THM_11_8_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T118"))) THEN
  UNDISCH_TAC `P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3)` THEN
  REWRITE_TAC[P2B_COR_9_95_VIEW_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `epsp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C995"))) THEN
  EXISTS_TAC `min eps0 epsp` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "C995" (MP_TAC o SPECL [`eps:real`; `&1 + eps`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C95:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C95"))) THEN
  EXISTS_TAC `C95:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `g0:real^3->real^3^3`; `A0:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `P2C_STD_NONCOLL_STATEMENT` THEN REWRITE_TAC[P2C_STD_NONCOLL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0`;
                             `stds_gs g0`]) THEN
  ASM_REWRITE_TAC[GSYM stds_gv] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)) THEN
  (* the canonical neighbourhoods above some B *)
  SUBGOAL_THEN
   `?B. !x t. &0 <= t /\ t < stds_tm g0 /\ B <= rfs_vscalar (stds_gv g0) t x
              ==> p2b_canon_L (stds_gv g0) C eps (&1 + eps) x t`
  (X_CHOOSE_THEN `B:real` (LABEL_TAC "Bc")) THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\(x:real^3) (t:real). p2b_canon_L (stds_gv g0) C eps (&1 + eps) x t`;
       `\(x:real^3) (t:real). rfs_vscalar (stds_gv g0) t x`; `stds_tm g0`] STDS_PICK)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
      REWRITE_TAC[STDS_GV_SCALAR] THEN
      MATCH_MP_TAC STDS_GS_RBOUND THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num->real^3` (X_CHOOSE_THEN `t:num->real`
      (CONJUNCTS_THEN2 (LABEL_TAC "pk1") (CONJUNCTS_THEN2 (LABEL_TAC "pk2")
       (CONJUNCTS_THEN2 (LABEL_TAC "pk3") (LABEL_TAC "pk4")))))) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `C:real`; `eps:real`; `kappa:real`;
                  `r0:real`; `x:num->real^3`; `t:num->real`] STDS_BLOWUP_SEQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`; `s:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC STDS_CANON_L_IMP THEN EXISTS_TAC `&1 + eps` THEN
      CONJ_TAC THENL
       [USE_THEN "pk4" MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
        USE_THEN "pk1" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN
    (* compact closures of the rescaled balls (complete slices) *)
    SUBGOAL_THEN
     `!A. ?N. !n:num. N <= n
              ==> compact_in (rfs_vtop (stds_gv g0) (t n))
                    (rfs_vtop (stds_gv g0) (t n) closure_of
                     rfs_vball (stds_gv g0) (t n) ((x:num->real^3) n)
                       (A * inv(sqrt(rfs_vscalar (stds_gv g0) (t n) (x n)))))`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "pk1" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
      ASM_SIMP_TAC[STDS_GV_BALL; STDS_GV_PARTS] THEN
      MATCH_MP_TAC RFU_BALL_CLOSURE_COMPACT THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; P2C_EUCLID_FACTS] THEN
      ASM_MESON_TAC[STDS_GS_RIEM; STDS_GS_BASICS];
      ALL_TAC] THEN
    USE_THEN "T118" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `&1`;
                                    `\n:num. stds_gv g0`; `x:num->real^3`; `t:num->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:(real^3)topology`
      (X_CHOOSE_THEN `atlas:((real^3->bool)#(real^3->real^3))->bool`
      (X_CHOOSE_THEN `g:real->real^3->real^3^3` (X_CHOOSE_THEN `xl:real^3`
       STRIP_ASSUME_TAC))))) THEN
    USE_THEN "C95" (MP_TAC o SPECL
      [`C:real`; `\n:num. stds_gv g0`; `(x:num->real^3) o (sub:num->num)`;
       `(t:num->real) o (sub:num->num)`;
       `\n:num. rfs_vscalar (stds_gv g0) ((t:num->real) ((sub:num->num) n))
                                           ((x:num->real^3) (sub n))`;
       `top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
       `g:real->real^3->real^3^3`; `xl:real^3`; `kappa:real`]) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `n:num` THEN
      USE_THEN "pk1" (MP_TAC o SPEC `(sub:num->num) n`) THEN STRIP_TAC THEN
      ASM_SIMP_TAC[STDS_GV_TOPSPACE];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL; o_THM] THEN
    USE_THEN "pk1" (MP_TAC o SPEC `(sub:num->num) N`) THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the radius *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0 / &2`] STDS_GS_RBOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (LABEL_TAC "K1")) THEN
  ABBREV_TAC `M = max (max B (K1 + &1)) (&2 / stds_tm g0)` THEN
  SUBGOAL_THEN `&0 < &2 / stds_tm g0 /\ &0 < M` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      EXPAND_TAC "M" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `sqrt(inv M)` THEN
  SUBGOAL_THEN `sqrt(inv M) pow 2 = inv M` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_INV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_tm g0 / &2 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "K1" (MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `M <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x` THEN
    EXPAND_TAC "M" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `stds_tm g0 / &2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 / stds_tm g0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "M" THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_DIV; REAL_LE_REFL]];
    USE_THEN "Bc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[STDS_GV_SCALAR] THEN
    UNDISCH_TAC `M <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x` THEN
    EXPAND_TAC "M" THEN REAL_ARITH_TAC]);;

(* On R^3 the component alternatives of p2b_canon_L are impossible: the     *)
(* only component is R^3, which is not compact.                              *)

let STDS_EUCLID_NO_COMPACT_COMPONENT = prove
 (`!U:real^3->bool.
     ~(U IN connected_components_of (euclidean:(real^3)topology) /\ compact_in euclidean U)`,
  GEN_TAC THEN
  SUBGOAL_THEN `connected_components_of (euclidean:(real^3)topology) = {(:real^3)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING; P2C_EUCLID_FACTS; UNIV_NOT_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SING; COMPACT_IN_EUCLIDEAN] THEN
  MESON_TAC[COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]);;

let STDS_CANON_L_GV = prove
 (`!g0 C eps L (x:real^3) t.
     &0 <= t /\ t < stds_tm g0 /\ p2b_canon_L (stds_gv g0) C eps L x t
     ==> (?e. rfs_evolving_neck (stds_gv g0) eps x t L e) \/
         (?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) C eps U Y /\
                x IN Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_canon_L (stds_gv g0) C eps L (x:real^3) t` THEN
  ASM_REWRITE_TAC[p2b_canon_L; STDS_GV_PARTS] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `Y:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `rfs_c_component (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) C
                                 (U:real^3->bool)` THEN
    REWRITE_TAC[rfs_c_component] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `U:real^3->bool` STDS_EUCLID_NO_COMPACT_COMPONENT) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `rfs_round_component (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) eps
                                     (U:real^3->bool)` THEN
    REWRITE_TAC[rfs_round_component] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `U:real^3->bool` STDS_EUCLID_NO_COMPACT_COMPONENT) THEN
    ASM_REWRITE_TAC[]]);;

