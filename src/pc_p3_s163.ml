(* ========================================================================= *)
(* Unit pc_p3_s163 (Part 3 proofs): MT Prop 16.3 in the exemption-free form *)
(* (P3_PROP_16_3_STATEMENT, with KL's volume clause p3_comp_vol in the      *)
(* C-component alternative).  A strong                                      *)
(* (C,eps)-canonical neighbourhood with the volume clause gives            *)
(* Vol B(x,R(x)^-1/2) >= kappa R(x)^-3/2 with kappa depending only on C:  *)
(* C-components (P3N_163_CCOMP: the diameter bound and Bishop-Gromov with  *)
(* Ric >= 0), eps-round components (P3N_163_ROUND: closeness to the round  *)
(* metric g1 and Gunther's comparison), caps (P3N_163_CAP: the radius of   *)
(* the cap volume clause by continuity of the ball supremum of R, and      *)
(* Bishop-Gromov) and strong necks (P3N_163_NECK, from pc_p2b_neckbd).     *)
(* Headline P3N_PROP_16_3 : |- !u. P3_PROP_16_3_STATEMENT u.                *)
(* ========================================================================= *)

needs "src/pc_p3_route.ml";;
needs "src/pc_cmp_gunther.ml";;
needs "src/pc_geo_kh.ml";;
needs "src/pc_mfd_transport.ml";;
needs "src/pc_p2b_slice.ml";;
needs "src/pc_p2c_lrestrict.ml";;
needs "src/pc_p2b_neckbd.ml";;
needs "src/pc_p3_c17vol.ml";;
needs "src/pc_p3_s16lim.ml";;
needs "src/pc_p3_s13pinch.ml";;
needs "src/pc_rfa_pinch.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the C-component case.  For a                  *)
(* C-component U (MT Def 9.75) of a compact Hausdorff Riemannian 3-manifold *)
(* with the volume clause Vol U > C^-1 R(x)^(-3/2) (KL Def 69.1(c)), the    *)
(* ball of radius R(x)^(-1/2) has volume >= C^-7 R(x)^(-3/2): it is U when  *)
(* the radius exceeds the diameter bound D0 = C inf(R)^(-1/2) <= C^2 R(x)^  *)
(* (-1/2), and otherwise Bishop-Gromov with Ric >= 0 compares it with the   *)
(* ball of radius D0, which is U.                                           *)
(* ========================================================================= *)

let P3N_COMP_EQ = prove
 (`!top (U:A->bool) x. U IN connected_components_of top /\ x IN U
                       ==> U = connected_component_of top x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[CONNECTED_COMPONENT_OF_EQUIV] THEN SIMP_TAC[]);;

let P3N_COMP_JOINABLE = prove
 (`!top atlas (U:A->bool) x y.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     U IN connected_components_of top /\ x IN U
     ==> (y IN U <=> mfd_joinable (top,atlas) x y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `U = connected_component_of top (x:A)` SUBST1_TAC THENL
   [MATCH_MP_TAC P3N_COMP_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN] THEN ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED_COMPONENT]);;

let P3N_COMPACT_SCALAR_BOUND = prove
 (`!top atlas (g:A->real^N^N) K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?B. !y. y IN K ==> mfd_scalar atlas g y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `euclideanreal`;
                 `mfd_scalar (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)`;
                 `K:A->bool`] IMAGE_COMPACT_IN) THEN
  ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS] THEN
  REWRITE_TAC[GSYM real_compact_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_ABS_LE; REAL_LE_TRANS]);;

(* the arithmetic of the Bishop-Gromov case *)

let P3N_163_CC_ARITH = prove
 (`!v0 v1 rho D C m.
     &0 < m /\ &0 < rho /\ rho < D /\ D <= C pow 2 * rho /\ &1 < C /\
     v0 * (rho pow 3 * m) <= v1 * (D pow 3 * m) /\ inv C * rho pow 3 < v0
     ==> inv(C pow 7) * rho pow 3 <= v1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C pow 6` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv C * rho pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v0 * rho pow 3 <= v1 * D pow 3` ASSUME_TAC THENL
   [MP_TAC(SPECL [`v0 * rho pow 3`; `v1 * D pow 3`; `m:real`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < v1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `v1:real`; `D pow 3`] REAL_LT_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `v0 * rho pow 3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D pow 3 <= C pow 6 * rho pow 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `C pow 6 * rho pow 3 = (C pow 2 * rho) pow 3` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v0 * rho pow 3 <= (v1 * C pow 6) * rho pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v1 * D pow 3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `v0 <= v1 * C pow 6` ASSUME_TAC THENL
   [MP_TAC(SPECL [`v0:real`; `v1 * C pow 6`; `rho pow 3`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(C = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(C pow 7) * rho pow 3 = (inv C * rho pow 3) * inv(C pow 6)` SUBST1_TAC
  THENL [UNDISCH_TAC `~(C = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v0 * inv(C pow 6)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ];
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ]]);;

(* inv(sqrt b) <= C inv(sqrt a) from a <= C^2 b *)

let P3N_INV_SQRT_LE = prove
 (`!a b C. &0 < a /\ &0 < b /\ &0 < C /\ a <= C pow 2 * b
           ==> inv(sqrt b) <= C * inv(sqrt a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt a /\ &0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt a <= C * sqrt b` ASSUME_TAC THENL
   [SUBGOAL_THEN `C * sqrt b = sqrt(C pow 2 * b)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE; POW_2_SQRT]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C * inv(sqrt a) = C / sqrt a` SUBST1_TAC THENL
   [REWRITE_TAC[real_div]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the C-component case itself.                 *)
(* ========================================================================= *)

let P3N_163_CCOMP = prove
 (`!top atlas (g:A->real^3^3) C x U v0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ &1 < C /\ x IN U /\ rfs_c_component (top,atlas) g C U /\
     mfd_has_volume (top,atlas) g U v0 /\
     inv C * inv(sqrt(mfd_scalar atlas g x)) pow 3 < v0
     ==> ?v. mfd_has_volume (top,atlas) g
               (mfd_ball (top,atlas) g x (inv(sqrt(mfd_scalar atlas g x)))) v /\
             inv(C pow 7) * inv(sqrt(mfd_scalar atlas g x)) pow 3 <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
  REWRITE_TAC[rfs_c_component] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun (l,i) -> LABEL_TAC l (el i cs))
      [("ucomp",1); ("ucpt",2); ("upos",4); ("uinf",5); ("udiam",7)]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  (* membership of U is joinability to x *)
  SUBGOAL_THEN `!y:A. y IN U ==> mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y` (LABEL_TAC "jn1") THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                `U:A->bool`; `x:A`; `y:A`] P3N_COMP_JOINABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y ==> y IN U` (LABEL_TAC "jn2") THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                `U:A->bool`; `x:A`; `y:A`] P3N_COMP_JOINABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* scalar curvature bounds on U *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:A->bool`] P3N_COMPACT_SCALAR_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  SUBGOAL_THEN `!y:A. y IN U ==> mfd_scalar atlas (g:A->real^3^3) y <= sup(IMAGE (mfd_scalar atlas g) U)`
  (LABEL_TAC "rsup") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN
    CONJ_TAC THENL [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "uinf" (MP_TAC o REWRITE_RULE[rfs_inf_gt]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y u v. (y:A) IN U /\ ~collinear {vec 0:real^3,u,v}
                        ==> d0 <= mfd_sectional atlas (g:A->real^3^3) y u v` (LABEL_TAC "sec") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:A`; `u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN U ==> &6 * d0 <= mfd_scalar atlas (g:A->real^3^3) y` (LABEL_TAC "r6") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= b ==> &6 * a <= &6 * b`) THEN
      MATCH_MP_TAC P3S_SECMIN_GE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:A topology` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT STRIP_TAC THEN USE_THEN "upos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `R0 <= sup(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                            (g:A->real^3^3)) U)` ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN USE_THEN "rsup" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&6 * d0 <= inf(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                                 (g:A->real^3^3)) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INF THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; USE_THEN "r6" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv C * R0 < d0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `inv C * sup(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                              (g:A->real^3^3)) U)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv C * R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Ri = inf(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                         (g:A->real^3^3)) U)` THEN
  SUBGOAL_THEN `&0 < Ri /\ R0 <= C pow 2 * Ri` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `R0 = C * (inv C * R0)` SUBST1_TAC THENL
     [UNDISCH_TAC `&1 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ri:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= (C - &1) * r ==> r <= C * r`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the radius and the diameter bound *)
  ABBREV_TAC `rho = inv(sqrt R0)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `D0 = C * inv(sqrt Ri)` THEN
  SUBGOAL_THEN `D0 <= C pow 2 * rho` ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN EXPAND_TAC "rho" THEN
    REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P3N_INV_SQRT_LE THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the points of U are at distance < D0 from x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:A->bool`] P2B9S_DIST_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bd:real`) THEN
  SUBGOAL_THEN `!y:A. y IN U ==> mfd_dist (top,atlas) (g:A->real^3^3) x y < D0` (LABEL_TAC "dU") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sup {mfd_dist (top,atlas) (g:A->real^3^3) x y | x IN U /\ y IN U}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [EXISTS_TAC `Bd:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN
        ASM_REWRITE_TAC[]];
      USE_THEN "udiam" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. D0 <= r ==> mfd_ball (top,atlas) (g:A->real^3^3) x r = U` (LABEL_TAC "bU")
  THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN USE_THEN "jn2" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "jn1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `D0:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "dU" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `D0 <= rho` THENL
   [(* the ball is U *)
    EXISTS_TAC `v0:real` THEN
    USE_THEN "bU" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `D0 <= rho`)]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv C * rho pow 3` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`1`; `7`; `C:real`] REAL_POW_MONO) THEN REWRITE_TAC[REAL_POW_1] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC];
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Bishop-Gromov from rho to D0 *)
  SUBGOAL_THEN `&0 < D0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `rho:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v1:real`) THEN
  EXISTS_TAC `v1:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(REWRITE_RULE[CMP_RELVOL_STATEMENT] (ISPECL [`(:A)`; `(:3)`] CMP_RELVOL)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `g:A->real^3^3`; `x:A`; `&0`; `D0:real`; `rho:real`; `D0:real`; `v1:real`; `v0:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN
      USE_THEN "bU" (fun th -> REWRITE_TAC[MATCH_MP th (SPEC `D0:real` REAL_LE_REFL)]) THEN
      DISCH_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_MUL_LZERO] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `y:A`; `&0`; `w:real^3`] CMPZ_MFD_RICCI_SEC_LOWER) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        USE_THEN "upos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "bU" (fun th -> REWRITE_TAC[MATCH_MP th (SPEC `D0:real` REAL_LE_REFL)]) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[REAL_NEG_0] THEN
  ASM_SIMP_TAC[CMP_VMODEL_FLAT; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `!s. &0 <= s ==> measure(ball(vec 0:real^3,s)) =
                                s pow 3 * measure(ball(vec 0:real^3,&1))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `s:real`; `&1`] MEASURE_BALL_SCALING) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; DIMINDEX_3];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC P3N_163_CC_ARITH THEN
  MAP_EVERY EXISTS_TAC [`v0:real`; `D0:real`; `measure(ball(vec 0:real^3,&1))`] THEN
  ASM_REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the eps-round case, part 1.                 *)
(* On a simply connected compact component W where g1 has sectional        *)
(* curvature 1, (W,g1) is the round S^3 (Killing-Hopf), so by Gunther's    *)
(* bound (injectivity radius pi) the g1-ball of radius r <= pi around x has *)
(* volume >= V_1(r).  Balls and volumes of the joinability class of x are  *)
(* those of the whole space (P2CO_CLASS_DIST, P2BC_VOLUME_RESTRICT).       *)
(* ========================================================================= *)

let P3N_CLASS_BALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> mfd_ball (subtopology top {y | mfd_joinable (top,atlas) x y},
                   restrict_atlas atlas {y | mfd_joinable (top,atlas) x y})
                  (restrict_metric atlas {y | mfd_joinable (top,atlas) x y} g) x r =
         mfd_ball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; mfd_ball; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `x:A`; `y:A`] P2CO_CLASS_DIST) THEN
  ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN SIMP_TAC[]);;

let P3N_ROUND_BALL_G1 = prove
 (`!top atlas (g1:A->real^3^3) W x r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g1 /\ W IN connected_components_of top /\
     simply_connected_space (subtopology top W) /\ x IN W /\
     (!y u v. y IN W /\ ~collinear {vec 0,u,v} ==> mfd_sectional atlas g1 y u v = &1) /\
     &0 < r /\ r <= pi
     ==> ?v. mfd_has_volume (top,atlas) g1 (mfd_ball (top,atlas) g1 x r) v /\
             cmp_vmodel (:3) (&1) r <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  (* W is the joinability class of x *)
  SUBGOAL_THEN `W = {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y}`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC P3N_COMP_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y} /\
                closed_in top {y:A | mfd_joinable (top,atlas) x y}` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2CO_CLASS_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* Killing-Hopf on the class *)
  MP_TAC(ISPECL
    [`subtopology top {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y}`;
     `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool)
                     {y:A | mfd_joinable (top,atlas) x y}`;
     `restrict_metric (atlas:((A->bool)#(A->real^3))->bool)
                      {y:A | mfd_joinable (top,atlas) x y} (g1:A->real^3^3)`]
    (REWRITE_RULE[KILLING_HOPF_S3_STATEMENT] KILLING_HOPF_S3_ISOMETRY)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; MFD_JOINABLE_REFL];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`z:A`; `v:real^3`; `w:real^3`] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `{y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y}`;
                     `g1:A->real^3^3`; `z:A`] MFDR_SECTIONAL_SET_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC
        `mfd_sectional (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool)
                                       {y:A | mfd_joinable (top,atlas) x y})
                       (restrict_metric atlas {y:A | mfd_joinable (top,atlas) x y}
                                        (g1:A->real^3^3)) z v w`) THEN
      MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`v:real^3`; `w:real^3`] THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^4->A` (X_CHOOSE_TAC `f':A->real^4`)) THEN
  (* the preimage p of x on the sphere *)
  SUBGOAL_THEN `(x:A) IN topspace (subtopology top
                  {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y})`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; MFD_JOINABLE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(f':A->real^4) x IN sphere(vec 0:real^4,&1) /\ (f:real^4->A) (f' x) = x`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[mfd_isometry]) THEN
    REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_TOPSPACE; homeomorphic_maps] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o check (fun th ->
        try let l = rand(rator(concl th)) in
            fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map" &&
            type_of (rand(concl th)) = `:A->real^4`
        with Failure _ -> false)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `p = (f':A->real^4) x` THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `p:real^4`; `r:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  REWRITE_TAC[KILLING_HOPF_HYPOTHESES_SPHERE3] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN CONJ_TAC THENL
   [(* the volume transported to the class and to the whole space *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                   `x:A`; `r:real`] P3N_CLASS_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL
      [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
       `{y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y}`;
       `mfd_ball (subtopology top {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y},
                  restrict_atlas atlas {y:A | mfd_joinable (top,atlas) x y})
                 (restrict_metric atlas {y:A | mfd_joinable (top,atlas) x y} (g1:A->real^3^3)) x r`;
       `v:real`] P2BC_VOLUME_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P3N_CLASS_BALL] THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
      MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `round3_metric`;
                   `subtopology top {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y}`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool)
                                   {y:A | mfd_joinable (top,atlas) x y}`;
                   `restrict_metric (atlas:((A->bool)#(A->real^3))->bool)
                                    {y:A | mfd_joinable (top,atlas) x y} (g1:A->real^3^3)`;
                   `f:real^4->A`; `f':A->real^4`; `p:real^4`; `r:real`] MTR_ISOMETRY_BALL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[KILLING_HOPF_HYPOTHESES_SPHERE3; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(SUBST1_TAC o REWRITE_RULE[ASSUME `(f:real^4->A) p = x`])] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `round3_metric`;
                   `subtopology top {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y}`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool)
                                   {y:A | mfd_joinable (top,atlas) x y}`;
                   `restrict_metric (atlas:((A->bool)#(A->real^3))->bool)
                                    {y:A | mfd_joinable (top,atlas) x y} (g1:A->real^3^3)`;
                   `f:real^4->A`; `f':A->real^4`;
                   `mfd_ball (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
                             round3_metric p r`; `v:real`] MFD_HAS_VOLUME_ISOMETRY) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[KILLING_HOPF_HYPOTHESES_SPHERE3] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* Gunther on the round sphere *)
  MP_TAC(REWRITE_RULE[CMP_GUNTHER_STATEMENT] (ISPECL [`(:real^4)`; `(:3)`] CMP_GUNTHER)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                        `round3_metric`; `p:real^4`] THEN
  REWRITE_TAC[KILLING_HOPF_HYPOTHESES_SPHERE3; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SQRT_1;
              REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `pi` THEN
    ASM_SIMP_TAC[KILLING_HOPF_HYPOTHESES_SPHERE3; SPHERE3_EXP_BALL_PI];
    MAP_EVERY X_GEN_TAC [`y:real^4`; `e1:real^3`; `e2:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x = &1 ==> x <= &1`) THEN
    MP_TAC KILLING_HOPF_HYPOTHESES_SPHERE3 THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^4) IN mfd_ball (subtopology euclidean (sphere(vec 0:real^4,&1)),
                                         sphere3_atlas) round3_metric p r` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]]);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the eps-round case, part 2.                 *)
(* Volumes of open sets of a compact space; the closeness of q g to g1 in  *)
(* rfs_mclose as quadratic form bounds (1 - e) g1 <= q g <= (1 + e) g1;    *)
(* the final arithmetic.                                                    *)
(* ========================================================================= *)

let P3N_HAS_VOLUME_OPEN_COMPACT = prove
 (`!top atlas (g:A->real^N^N) S.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ open_in top S
     ==> ?v. mfd_has_volume (top,atlas) g S v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `topspace top:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  EXISTS_TAC `mfd_volume (top,atlas) (g:A->real^N^N) S` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `S:A->bool`; `topspace top:A->bool`; `w:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN; OPEN_IN_SUBSET]);;

let P3N_MCLOSE_QF = prove
 (`!top atlas (g:A->real^3^3) g1 q k eps W.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     riemannian_metric atlas g1 /\ &0 < q /\ &0 < eps /\ W SUBSET topspace top /\
     rfs_mclose k eps atlas W g1 (\x. q %% g x)
     ==> ?e. &0 <= e /\ e < eps /\
             !y w. y IN W
                   ==> (&1 - e) * (w dot (g1 y ** w)) <= q * (w dot (g y ** w)) /\
                       q * (w dot (g y ** w)) <= (&1 + e) * (w dot (g1 y ** w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_mclose] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `&0 < eps pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  EXISTS_TAC `sqrt(max d (&0))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `eps = sqrt(eps pow 2)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `y:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\x:A. q %% (g:A->real^3^3) x`; `y:A`] CMPF_LOCAL_METRIC) THEN
  ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`;
                 `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y))`;
                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) (chart_at atlas (y:A))
                               (g1:A->real^3^3)`;
                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) (chart_at atlas (y:A))
                               (\x:A. q %% (g:A->real^3^3) x)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`;
                 `max d (&0)`] P3H_LCK_QF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x <= d ==> x <= max d (&0)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

(* the final arithmetic: lam = q / (1 - e) <= R *)

let P3N_163_RD_ARITH = prove
 (`!V1 v lam R. &0 < V1 /\ &0 < lam /\ lam <= R /\ V1 <= lam * sqrt lam * v
                ==> V1 / &2 * inv(sqrt R) pow 3 <= v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt lam /\ &0 < sqrt R /\ sqrt lam <= sqrt R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt R) pow 3 = inv(R * sqrt R)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_INV] THEN AP_TERM_TAC THEN
    MP_TAC(SPEC `R:real` SQRT_POW_2) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * sqrt lam <= R * sqrt R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam * sqrt lam /\ &0 < R * sqrt R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(v < &0) ==> &0 <= v`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(lam * sqrt lam) * v < (lam * sqrt lam) * &0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `V1 * inv(R * sqrt R) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * sqrt lam * v` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(lam * sqrt lam) * v <= (R * sqrt R) * v` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < V1 * inv(R * sqrt R)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the eps-round case, part 3.                 *)
(* Distances compare inside the joinability class; the model volume is     *)
(* positive; the case itself: with q g eps-close to g1 (sectional          *)
(* curvature 1) on the component U, R(x) in [12q/5, 48q/5] (P2BS_ROUND_   *)
(* SECT_Q), the g1-ball of radius 1/4 lies in the g-ball of radius        *)
(* R(x)^(-1/2) and its g-volume is >= ((1 - e)/q)^(3/2) V_1(1/4).          *)
(* ========================================================================= *)

let P3N_CLASS_DIST_COMPARE = prove
 (`!top atlas (g:A->real^3^3) g' c x y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     riemannian_metric atlas g' /\ &0 < c /\ x IN topspace top /\
     (!z v. mfd_joinable (top,atlas) x z ==> v dot (g' z ** v) <= c * (v dot (g z ** v))) /\
     mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) g' x y <= sqrt c * mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in top {z:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x z}`
  ASSUME_TAC THENL [ASM_SIMP_TAC[P2CO_CLASS_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `x:A`; `y:A`] P2CO_CLASS_DIST) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                 `x:A`; `x:A`; `y:A`] P2CO_CLASS_DIST) THEN
  ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC P3N_DIST_COMPARE THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`z:A`; `v:real^3`] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `{z:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x z}`;
                   `g':A->real^3^3`; `g:A->real^3^3`; `z:A`; `c:real`]
                  P3H_RESTRICT_QF_TRANSFER) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]]);;

let P3N_VMODEL1_POS = prove
 (`!r. &0 < r /\ r <= pi ==> &0 < cmp_vmodel (:3) (&1) r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1`; `pi`] (INST_TYPE [`:3`,`:N`] CMPV_VMODEL_FACTS)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PI_POS] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN
    ASM_REWRITE_TAC[SQRT_1; REAL_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `r:real`]) THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* sectional bounds from the closeness of P2BS_ROUND_SECT_Q *)

let P3N_SEC_Q_BOUNDS = prove
 (`!s q eps. &0 < q /\ eps <= &1 / &40 /\ abs(s / q - &1) <= &24 * eps
             ==> &2 / &5 * q <= s /\ s <= &8 / &5 * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s = q * (s / q)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `t = s / q` THEN
  SUBGOAL_THEN `&2 / &5 <= t /\ t <= &8 / &5` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC]);;

(* the ball inclusion arithmetic: sqrt c * d < R^(-1/2) when c R <= 16, d < 1/4 *)

let P3N_163_RB_ARITH = prove
 (`!c R d. &0 < c /\ &0 < R /\ c * R <= &16 /\ &0 <= d /\ d < &1 / &4
           ==> sqrt c * d < inv(sqrt R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt c /\ &0 < sqrt R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt c * sqrt R <= &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 = sqrt(&16)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt c * (&1 / &4)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ARITH `x * &1 / &4 = x / &4`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &4`] THEN
    SUBGOAL_THEN `inv(sqrt R) * &4 = &4 / sqrt R` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]);;

let P3N_163_ROUND = prove
 (`!top atlas (g:A->real^3^3) eps x U.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ rfs_components_sc top /\
     &0 < eps /\ eps <= &1 / &40 /\ x IN U /\ rfs_round_component (top,atlas) g eps U
     ==> ?v. mfd_has_volume (top,atlas) g
               (mfd_ball (top,atlas) g x (inv(sqrt(mfd_scalar atlas g x)))) v /\
             cmp_vmodel (:3) (&1) (&1 / &4) / &2 *
             inv(sqrt(mfd_scalar atlas g x)) pow 3 <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_round_component] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_round_component"
    with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3`
      STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  (* the g1-ball of radius 1/4 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `U:A->bool`; `x:A`; `&1 / &4`] P3N_ROUND_BALL_G1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `rfs_components_sc (top:A topology)` THEN
      REWRITE_TAC[rfs_components_sc] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC;
      MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `v1:real` STRIP_ASSUME_TAC)] THEN
  (* quadratic forms *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g1:A->real^3^3`; `q:real`; `rfs_kreg eps`; `eps:real`; `U:A->bool`]
                P3N_MCLOSE_QF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  (* the scalar curvature at x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `U:A->bool`; `x:A`; `q:real`; `g1:A->real^3^3`]
                P2BS_ROUND_SECT_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&12 / &5 * q <= mfd_scalar atlas (g:A->real^3^3) x /\
                mfd_scalar atlas g x <= &48 / &5 * q` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!u v. ~collinear {vec 0:real^3,u,v}
                         ==> &2 / &5 * q <= mfd_sectional atlas (g:A->real^3^3) x u v /\
                             mfd_sectional atlas g x u v <= &8 / &5 * q` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P3N_SEC_Q_BOUNDS THEN
      EXISTS_TAC `eps:real` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPEC `&2 / &5 * q`) THEN ASM_SIMP_TAC[] THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o SPEC `&8 / &5 * q`) THEN ASM_SIMP_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `rho = inv(sqrt R)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
  (* the volumes *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `rho:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vB:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `mfd_ball (top,atlas) (g1:A->real^3^3) x (&1 / &4)`]
                P3N_HAS_VOLUME_OPEN_COMPACT) THEN
  ASM_SIMP_TAC[MFD_BALL_OPEN] THEN DISCH_THEN(X_CHOOSE_TAC `vB1:real`) THEN
  EXISTS_TAC `vB:real` THEN ASM_REWRITE_TAC[] THEN
  (* the g1-ball lies in U and in the g-ball *)
  SUBGOAL_THEN `mfd_ball (top,atlas) (g1:A->real^3^3) x (&1 / &4) SUBSET U` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `x:A`; `y:A`] P3N_COMP_JOINABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g1:A->real^3^3) x (&1 / &4) SUBSET
                mfd_ball (top,atlas) g x rho` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sqrt((&1 + e) / q) * mfd_dist (top,atlas) (g1:A->real^3^3) x y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3N_CLASS_DIST_COMPARE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`z:A`; `w:real^3`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:A) IN U` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                       `x:A`; `z:A`] P3N_COMP_JOINABLE) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`z:A`; `w:real^3`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `&1 + e`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ARITH `a / q * b = (a * b) / q`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "rho" THEN MATCH_MP_TAC P3N_163_RB_ARITH THEN
      SUBGOAL_THEN `mfd_dist (top,atlas) (g1:A->real^3^3) x y < &1 / &4 /\
                    &0 <= mfd_dist (top,atlas) g1 x y` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(&1 + e) / q * R = (&1 + e) * (R / q)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&41 / &40) * (&48 / &5)` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the volume comparison *)
  SUBGOAL_THEN `&0 < &1 - e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `lam = q / (&1 - e)` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v1 <= lam * sqrt lam * vB1` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_COMPARE_QF THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g1:A->real^3^3`; `g:A->real^3^3`;
                          `mfd_ball (top,atlas) (g1:A->real^3^3) x (&1 / &4)`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `w:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `&1 + e`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_ARITH `q / a * b = (q * b) / a`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vB1 <= vB` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`;
                   `mfd_ball (top,atlas) (g1:A->real^3^3) x (&1 / &4)`;
                   `mfd_ball (top,atlas) (g:A->real^3^3) x rho`; `vB1:real`; `vB:real`]
                  MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "rho" THEN MATCH_MP_TAC P3N_163_RD_ARITH THEN EXISTS_TAC `lam:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3N_VMODEL1_POS THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
    EXPAND_TAC "lam" THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `R * e <= R * (&1 / &40)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v1:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * sqrt lam * vB1` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]]);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the cap case, part 1.  On a                  *)
(* compact Hausdorff Riemannian manifold the scalar curvature is uniformly  *)
(* continuous for the distance on the joinability class of x, minimizing   *)
(* geodesics give intermediate points, and r |-> sup of R over B(x,r) is   *)
(* continuous for r > 0; so by the intermediate value theorem some radius  *)
(* r <= R(x)^(-1/2) has sup over B(x,r) of R = r^-2 (the radius of the cap *)
(* volume clause, MT Def 9.73).                                             *)
(* ========================================================================= *)

(* Leaf arithmetic: drop the quantified assumptions (ASM_REAL_ARITH_TAC can *)
(* fail in their presence), then ASM_REAL_ARITH_TAC.                        *)

let P3N_LEAF_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) || is_exists(concl th) then ALL_TAC else NO_TAC)) THEN
  ASM_REAL_ARITH_TAC;;

let P3N_SCALAR_UNIF = prove
 (`!top atlas (g:A->real^3^3) x.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ x IN topspace top
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !z w. mfd_joinable (top,atlas) x z /\ mfd_joinable (top,atlas) x w /\
                           mfd_dist (top,atlas) g z w < d
                           ==> mfd_scalar atlas g z < mfd_scalar atlas g w + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfd_metric (top,atlas) (g:A->real^3^3) x`; `real_euclidean_metric`;
                 `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)`]
                CONTINUOUS_IMP_UNIFORMLY_CONTINUOUS_MAP) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] MFD_MTOPOLOGY) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] MFD_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_SIMP_TAC[P2CO_CLASS_CLOSED];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[uniformly_continuous_map; REAL_EUCLIDEAN_METRIC; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs(b - a) < e ==> a < b + e`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3N_GEO_INTERMEDIATE = prove
 (`!top atlas (g:A->real^N^N) x w t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ mfd_joinable (top,atlas) x w /\ &0 <= t /\ t <= &1
     ==> ?u. mfd_joinable (top,atlas) x u /\ mfd_joinable (top,atlas) u w /\
             mfd_dist (top,atlas) g x u <= t * mfd_dist (top,atlas) g x w /\
             mfd_dist (top,atlas) g u w <= (&1 - t) * mfd_dist (top,atlas) g x w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `w:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_SIMP_TAC[MFD_COMPACT_IMP_COMPLETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  SUBGOAL_THEN `&1 IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_exp_dom (top,atlas) (g:A->real^N^N) x = (:real^N)` THEN
    REWRITE_TAC[EXTENSION; mfd_exp_dom; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real) IN (J:real->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `is_realinterval(J:real->bool)` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`; `t:real`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gam:real->A) (&1) = w` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_exp (top,atlas) (g:A->real^N^N) x v = w` THEN
    ASM_REWRITE_TAC[mfd_exp];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(t - &0) = t /\ abs(&1 - t) = &1 - t` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `(gam:real->A) t` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `J:real->bool`; `&0`; `t:real`] GEOH_GEO_SEG_DIST) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `J:real->bool`; `t:real`; `&1`] GEOH_GEO_SEG_DIST) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `J:real->bool`; `t:real`; `&0`] MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* the sup of R over a ball about x: bounds and approximation *)

let P3N_SUPBALL_FACTS = prove
 (`!top atlas (g:A->real^3^3) x r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ x IN topspace top /\ &0 < r
     ==> (!z. z IN mfd_ball (top,atlas) g x r
              ==> mfd_scalar atlas g z <=
                  sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g x r))) /\
         (!c. (!z. z IN mfd_ball (top,atlas) g x r ==> mfd_scalar atlas g z <= c)
              ==> sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g x r)) <= c) /\
         (!c. c < sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g x r))
              ==> ?z. z IN mfd_ball (top,atlas) g x r /\ c < mfd_scalar atlas g z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`] P3N_COMPACT_SCALAR_BOUND) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) x r SUBSET topspace top` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3))
                       (mfd_ball (top,atlas) g x r) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b. !y. y IN IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                      (g:A->real^3^3)) (mfd_ball (top,atlas) g x r)
                         ==> y <= b` ASSUME_TAC THENL
   [EXISTS_TAC `B:real` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3))
                          (mfd_ball (top,atlas) g x r)`; `c:real`] SUP_APPROACH) THEN
    ASM_REWRITE_TAC[EXISTS_IN_IMAGE]]);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the cap case, part 2.  The                   *)
(* function r |-> sup of R over B(x,r) is continuous at every r > 0: from  *)
(* the left by the sup approximation, from the right by the uniform        *)
(* continuity of R and the intermediate points of minimizing geodesics.    *)
(* ========================================================================= *)

let P3N_SUPBALL_CONT = prove
 (`!top atlas (g:A->real^3^3) x r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ x IN topspace top /\ &0 < r
     ==> (\s. sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g x s)))
         real_continuous (atreal r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_continuous_atreal] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `r:real`] P3N_SUPBALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "le_r")
    (CONJUNCTS_THEN2 (LABEL_TAC "sup_r") (LABEL_TAC "app_r"))) THEN
  ABBREV_TAC `Sr = sup(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                         (g:A->real^3^3)) (mfd_ball (top,atlas) g x r))` THEN
  USE_THEN "app_r" (MP_TAC o SPEC `Sr - e`) THEN
  ANTS_TAC THENL [P3N_LEAF_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mfd_ball; IN_ELIM_THM] o check (fun th ->
    concl th = `(z:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x r`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] P3N_SCALAR_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [P3N_LEAF_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  ABBREV_TAC `m = min eta r` THEN
  SUBGOAL_THEN `&0 < m /\ m <= eta /\ m <= r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN P3N_LEAF_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (r - mfd_dist (top,atlas) (g:A->real^3^3) x z) (m / &4)` THEN
  CONJ_TAC THENL [P3N_LEAF_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [P3N_LEAF_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `s:real`] P3N_SUPBALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "le_s")
    (CONJUNCTS_THEN2 (LABEL_TAC "sup_s") (K ALL_TAC))) THEN
  ABBREV_TAC `Ss = sup(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                         (g:A->real^3^3)) (mfd_ball (top,atlas) g x s))` THEN
  ASM_CASES_TAC `s <= r` THENL
   [SUBGOAL_THEN `Ss <= Sr` ASSUME_TAC THENL
     [USE_THEN "sup_s" MATCH_MP_TAC THEN X_GEN_TAC `w:A` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "le_r" MATCH_MP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN P3N_LEAF_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z <= Ss` ASSUME_TAC THENL
     [USE_THEN "le_s" MATCH_MP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN P3N_LEAF_ARITH_TAC;
      ALL_TAC] THEN
    P3N_LEAF_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Sr <= Ss` ASSUME_TAC THENL
   [USE_THEN "sup_r" MATCH_MP_TAC THEN X_GEN_TAC `w:A` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "le_s" MATCH_MP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN P3N_LEAF_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Ss <= Sr + e / &2` ASSUME_TAC THENL
   [USE_THEN "sup_s" MATCH_MP_TAC THEN X_GEN_TAC `w:A` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `mfd_dist (top,atlas) (g:A->real^3^3) x w < r` THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 < e ==> a <= b + e / &2`) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "le_r" MATCH_MP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^3^3) x w` THEN
    SUBGOAL_THEN `r <= D /\ D < s /\ &0 < D` STRIP_ASSUME_TAC THENL
     [P3N_LEAF_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `w:A`; `(r - m / &4) / D`]
                  P3N_GEO_INTERMEDIATE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN P3N_LEAF_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN P3N_LEAF_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r - m / &4) / D * D = r - m / &4 /\
                  (&1 - (r - m / &4) / D) * D = D - (r - m / &4)`
    (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `~(D = &0)` MP_TAC THENL [P3N_LEAF_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    USE_THEN "uc" (MP_TAC o SPECL [`w:A`; `u:A`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `w:A`; `u:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN P3N_LEAF_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) u <= Sr` MP_TAC THENL
     [USE_THEN "le_r" MATCH_MP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN P3N_LEAF_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  P3N_LEAF_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the cap case, part 3.  The                   *)
(* radius of the cap volume clause exists (intermediate value theorem for   *)
(* r^2 sup R over B(x,r) between r0 = min(R(x)^-1/2, B^-1/2) and           *)
(* R(x)^-1/2); with the curvature ratio bound of the cap it is >= (C R(x))^ *)
(* (-1/2), so B(x,R(x)^-1/2) has volume >= C^-3 R(x)^(-3/2).                *)
(* ========================================================================= *)

let P3N_CAP_RADIUS = prove
 (`!top atlas (g:A->real^3^3) x.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ x IN topspace top /\ &0 < mfd_scalar atlas g x
     ==> ?r. &0 < r /\ r <= inv(sqrt(mfd_scalar atlas g x)) /\
             sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g x r)) = inv(r pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`] P3N_COMPACT_SCALAR_BOUND) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `R0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `r1 = inv(sqrt R0)` THEN
  ABBREV_TAC `r0 = min r1 (inv(sqrt B))` THEN
  SUBGOAL_THEN `&0 < r1 /\ &0 < r0 /\ r0 <= r1 /\ r0 <= inv(sqrt B)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "r1"] THEN
    SUBGOAL_THEN `&0 < inv(sqrt R0) /\ &0 < inv(sqrt B)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. s pow 2 * sup(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                                       (g:A->real^3^3))
                                         (mfd_ball (top,atlas) g x s))`;
                 `r0:real`; `r1:real`; `&1`] REAL_IVT_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN REWRITE_TAC[REAL_CONTINUOUS_AT_ID];
        MATCH_MP_TAC P3N_SUPBALL_CONT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      (* the value at r0 is <= 1 *)
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x:A`; `r0:real`] P3N_SUPBALL_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `B:real` o CONJUNCT1 o CONJUNCT2) THEN ANTS_TAC THENL
       [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        DISCH_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r0 pow 2 * B` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(sqrt B) pow 2 * B` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_INV] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `x = &1 ==> x <= &1`) THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
      (* the value at r1 is >= 1 *)
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x:A`; `r1:real`] P3N_SUPBALL_FACTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r1 pow 2 * R0` THEN CONJ_TAC THENL
       [EXPAND_TAC "r1" THEN REWRITE_TAC[REAL_POW_INV] THEN
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `x = &1 ==> &1 <= x`) THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `r pow 2 * sup(IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                                 (g:A->real^3^3))
                                   (mfd_ball (top,atlas) g x r)) = &1` THEN
    UNDISCH_TAC `&0 < r pow 2` THEN CONV_TAC REAL_FIELD]);;

(* the arithmetic of the cap case *)

let P3N_163_CAP_ARITH = prove
 (`!C R rs v. &1 < C /\ &0 < R /\ &0 < rs /\ inv(rs pow 2) <= C * R /\
              inv C * rs pow 3 <= v
              ==> inv(C pow 3) * inv(sqrt R) pow 3 <= v`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `rho = inv(sqrt R)` THEN
  SUBGOAL_THEN `&0 < rho /\ rho pow 2 = inv R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho pow 2 <= C * rs pow 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < rs pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= (C * R) * rs pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `&1 = inv(rs pow 2) * rs pow 2` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `C * rs pow 2 = inv R * ((C * R) * rs pow 2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x * &1 <= y ==> x <= y`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho pow 3 <= C pow 2 * rs pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(rho pow 3) pow 2 = (rho pow 2) pow 3 /\
                  (C pow 2 * rs pow 3) pow 2 = C pow 4 * (rs pow 2) pow 3` (fun th -> REWRITE_TAC[th])
    THENL [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C * rs pow 2) pow 3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC];
        MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv C * rs pow 3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv C * rs pow 3 = inv(C pow 3) * (C pow 2 * rs pow 3)` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(C = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the cap case itself.  For x in               *)
(* the core Y of a (C,eps)-cap U, the radius rs of the volume clause has   *)
(* rs^-2 = sup of R over B(x,rs) <= C R(x) (the curvature ratio bound on   *)
(* U), so B(x,R(x)^-1/2) has volume >= C^-3 R(x)^(-3/2).                    *)
(* ========================================================================= *)

let P3N_CAP_Y_SUBSET = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y ==> Y SUBSET U /\ U SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_SUBSET] THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let P3N_163_CAP = prove
 (`!top atlas (g:A->real^3^3) C eps x U Y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ &1 < C /\ &0 < mfd_scalar atlas g x /\
     rfs_cap (top,atlas) g C eps U Y /\ x IN Y
     ==> ?v. mfd_has_volume (top,atlas) g
               (mfd_ball (top,atlas) g x (inv(sqrt(mfd_scalar atlas g x)))) v /\
             inv(C pow 3) * inv(sqrt(mfd_scalar atlas g x)) pow 3 <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] P3N_CAP_Y_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN U /\ x IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun (l,i) -> LABEL_TAC l (el i cs)) [("ratio",5); ("ballc",7)]) THEN
  (* the radius of the clause *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] P3N_CAP_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rs:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`] P3N_COMPACT_SCALAR_BOUND) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) x rs SUBSET topspace top` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  USE_THEN "ballc" (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL [`x:A`; `rs:real`]))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `B:real`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `vs:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) x rs SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of mfd_ball (top,atlas) (g:A->real^3^3) x rs` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  (* the ratio bound: R <= C R0 on the ball *)
  USE_THEN "ratio" (MP_TAC o REWRITE_RULE[rfs_sup_lt]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z:A. z IN mfd_ball (top,atlas) (g:A->real^3^3) x rs ==> mfd_scalar atlas g z <= C * R0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z / R0 <= d1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`z:A`; `x:A`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `mfd_ball (top,atlas) (g:A->real^3^3) x rs SUBSET U`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `d1 * R0 <= C * R0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(rs pow 2) <= C * R0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term (fun t -> t = `inv(rs pow 2)`)) (concl th) && is_eq(concl th))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `rs:real`] P3N_SUPBALL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv C * rs pow 3 <= vs` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rs pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d * rs pow 3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      UNDISCH_TAC `d <= vs / rs pow 3` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  (* the ball of radius R0^(-1/2) *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `inv(sqrt R0)`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3N_163_CAP_ARITH THEN EXISTS_TAC `rs:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `vs:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `mfd_ball (top,atlas) (g:A->real^3^3) x rs`;
                 `mfd_ball (top,atlas) (g:A->real^3^3) x (inv(sqrt R0))`;
                 `vs:real`; `v:real`] MFD_HAS_VOLUME_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the neck case.  At the centre                *)
(* x of a strong eps-neck, |Rm|(x) <= K1 R(x) (P2BN_EVNECK_RM at s = 0), so *)
(* the ball of radius R(x)^-1/2 has volume >= pi/750 min(R(x)^-1/2,        *)
(* (K1 R(x))^-1/2)^3 (P2BN_NECK_BALL_VOLUME, pc_p2b_neckbd), which is       *)
(* kN R(x)^(-3/2) with kN = pi/750 min(1, K1^-1/2)^3.                       *)
(* ========================================================================= *)

let P3N_NECK_KN_ARITH = prove
 (`!K1 R. &0 < K1 /\ &0 < R
          ==> (pi / &750 * min (&1) (inv(sqrt K1)) pow 3) * inv(sqrt R) pow 3 <=
              pi / &750 * min (inv(sqrt R)) (inv(sqrt(K1 * R))) pow 3`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_INV_MUL] THEN
  ABBREV_TAC `a = inv(sqrt K1)` THEN ABBREV_TAC `c = inv(sqrt R)` THEN
  SUBGOAL_THEN `&0 < a /\ &0 < c` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "c"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;

let P3N_163_NECK = prove
 (`?epsN kN. &0 < epsN /\ &0 < kN /\
     !TM AT (G:real->A->real^3^3) eps x t e.
        &0 < eps /\ eps <= epsN /\ hausdorff_space (TM t) /\ compact_space (TM t) /\
        riemannian_metric (AT t) (G t) /\ rfs_strong_neck (TM,AT,G) eps x t e
        ==> ?v. mfd_has_volume (TM t,AT t) (G t)
                  (mfd_ball (TM t,AT t) (G t) x (inv(sqrt(mfd_scalar (AT t) (G t) x)))) v /\
                kN * inv(sqrt(mfd_scalar (AT t) (G t) x)) pow 3 <= v`,
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm"))
    (INST_TYPE [`:A`,`:A`] P2BN_EVNECK_RM) THEN
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bv"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_BALL_VOLUME) THEN
  EXISTS_TAC `min eps1 (&1 / &4)` THEN
  EXISTS_TAC `pi / &750 * min (&1) (inv(sqrt K1)) pow 3` THEN
  SUBGOAL_THEN `&0 < inv(sqrt K1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < eps1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&0 < inv(sqrt K1)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `eps:real`; `x:A`; `t:real`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_evolving_neck (TM:real->A topology,AT,G) eps (x:A) t (&1) e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                         ((G:real->A->real^3^3) t) eps (x:A) e` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_evolving_neck (TM:real->A topology,AT,G) eps (x:A) t (&1) e` THEN
    REWRITE_TAC[rfs_evolving_neck] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck" with Failure _ -> false)) THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= min eps1 (&1 / &4)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* |Rm| at the centre *)
  SUBGOAL_THEN
   `mfd_rm_norm ((AT:real->((A->bool)#(A->real^3))->bool) t) ((G:real->A->real^3^3) t) (x:A)
    <= K1 * mfd_scalar (AT t) (G t) x`
  ASSUME_TAC THENL
   [USE_THEN "rm" (MP_TAC o SPECL [`(TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
                                     G:real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`;
                                   `&1`; `e:real^3->A`; `&0`]) THEN
    REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar; real_div; REAL_MUL_LZERO;
                REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `eps <= &1 / &4` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                              ((G:real->A->real^3^3) t) (x:A)` THEN
  SUBGOAL_THEN `&0 < inv(sqrt R0) /\ &0 < K1 * R0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in ((TM:real->A topology) t)
      (TM t closure_of mfd_ball (TM t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                                ((G:real->A->real^3^3) t) (x:A) (inv(sqrt R0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]; ALL_TAC] THEN
  USE_THEN "bv" (MP_TAC o SPECL [`(TM:real->A topology) t`;
                                 `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                                 `(G:real->A->real^3^3) t`; `eps:real`; `x:A`; `e:real^3->A`;
                                 `inv(sqrt R0)`; `K1 * R0`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pi / &750 * min (inv(sqrt R0)) (inv(sqrt(K1 * R0))) pow 3` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3N_NECK_KN_ARITH THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Prop 16.3, exemption-free: the assembly.  The four                      *)
(* alternatives of a strong (C,eps)-canonical neighbourhood with KL's       *)
(* volume clause (p3_strong_canonv): necks (P3N_163_NECK, from             *)
(* P2BN_EVNECK_RM and P2BN_NECK_BALL_VOLUME of pc_p2b_neckbd), caps        *)
(* (P3N_163_CAP), C-components (P3N_163_CCOMP) and eps-round components    *)
(* (P3N_163_ROUND), with kappa the least of the four constants.            *)
(* ========================================================================= *)

let P3N_PROP_16_3 = prove
 (`!u:A->bool. P3_PROP_16_3_STATEMENT u`,
  GEN_TAC THEN
  X_CHOOSE_THEN `epsN:real` (X_CHOOSE_THEN `kN:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "neck"))))
    (INST_TYPE [`:A`,`:A`] P3N_163_NECK) THEN
  REWRITE_TAC[P3_PROP_16_3_STATEMENT] THEN
  EXISTS_TAC `min epsN (&1 / &40)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `C:real` THEN DISCH_TAC THEN
  ABBREV_TAC `V1 = cmp_vmodel (:3) (&1) (&1 / &4)` THEN
  SUBGOAL_THEN `&0 < V1` ASSUME_TAC THENL
   [EXPAND_TAC "V1" THEN MATCH_MP_TAC P3N_VMODEL1_POS THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `kap = min (min kN (inv(C pow 7))) (min (V1 / &2) (inv(C pow 3)))` THEN
  EXISTS_TAC `kap:real` THEN CONJ_TAC THENL
   [EXPAND_TAC "kap" THEN
    SUBGOAL_THEN `&0 < inv(C pow 7) /\ &0 < inv(C pow 3)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `TM:real->A topology`;
                       `AT:real->((A->bool)#(A->real^3))->bool`; `G:real->A->real^3^3`;
                       `x:A`; `t:real`] THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar; rfs_vball] THEN STRIP_TAC THEN
  ABBREV_TAC `R0 = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                               ((G:real->A->real^3^3) t) (x:A)` THEN
  SUBGOAL_THEN `&0 <= inv(sqrt R0) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k1. kap <= k1 /\
         (?v. mfd_has_volume ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                ((G:real->A->real^3^3) t)
                (mfd_ball (TM t,AT t) (G t) (x:A) (inv(sqrt R0))) v /\
              k1 * inv(sqrt R0) pow 3 <= v)
         ==> ?v. mfd_has_volume (TM t,AT t) (G t) (mfd_ball (TM t,AT t) (G t) x (inv(sqrt R0))) v /\
                 kap * inv(sqrt R0) pow 3 <= v`
  (LABEL_TAC "mono") THENL
   [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k1 * inv(sqrt R0) pow 3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `U:A->bool` MP_TAC o REWRITE_RULE[p3_canonv_at] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p3_canonv_at"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[p3_strong_canonv; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
  STRIP_TAC THEN USE_THEN "mono" MATCH_MP_TAC THENL
   [(* a strong neck *)
    EXISTS_TAC `kN:real` THEN CONJ_TAC THENL [EXPAND_TAC "kap" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "R0" THEN USE_THEN "neck" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `e:real^3->A`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `eps <= min epsN (&1 / &40)` THEN REAL_ARITH_TAC;
    (* a cap *)
    EXISTS_TAC `inv(C pow 3)` THEN CONJ_TAC THENL [EXPAND_TAC "kap" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "R0" THEN MATCH_MP_TAC P3N_163_CAP THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `U:A->bool`; `Y:A->bool`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    (* a C-component *)
    EXISTS_TAC `inv(C pow 7)` THEN CONJ_TAC THENL [EXPAND_TAC "kap" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `p3_comp_vol (TM:real->A topology,AT,G) C (x:A) t U` THEN
    REWRITE_TAC[p3_comp_vol; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "R0" THEN MATCH_MP_TAC P3N_163_CCOMP THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `v0:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    (* an eps-round component *)
    EXISTS_TAC `V1 / &2` THEN CONJ_TAC THENL [EXPAND_TAC "kap" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "R0" THEN EXPAND_TAC "V1" THEN MATCH_MP_TAC P3N_163_ROUND THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `U:A->bool`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

