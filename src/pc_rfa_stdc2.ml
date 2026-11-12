(* ========================================================================= *)
(* Unit pc_rfa_stdc2: the Part 3 obligation R14,                            *)
(*   RFA_P3_STD_C2_BOUND |- P2_THM_12_5_STATEMENT /\ P2_THM_12_32_STATEMENT  *)
(*                          /\ P2_PROP_12_31_STATEMENT                      *)
(*                          ==> P3_STD_C2_BOUND_STATEMENT.                  *)
(* On every standard flow G (p3_std_flow g0 1 G), uniformly in G:           *)
(* - for 0 < s < 1 every point has a (C',eps)-canonical neighbourhood       *)
(*   (Thm 12.32), so abs(grad R) <= Cd R^(3/2) and                          *)
(*   abs(Lap R + 2 abs Ric^2) <= Cd R^2 (P2C_CANON_DERIV);                  *)
(* - short times: R <= Rb on [0,T1] by Lemma 11.2 forward from the initial *)
(*   slice (P2C_LEMMA_11_2_DB on the regular flow view,                     *)
(*   P2C_FLOW_VIEW_REGULAR), abs Rm bounded by positivity (Thm 12.5) and    *)
(*   pinching, and Shi with initial data (RFA_P2_THM_3_29) with the bounded *)
(*   geometry of g0 (P2CN_STD_RMD_BOUND) bounds abs(nabla^l Rm) absolutely; *)
(* - later times: Lemma 11.2 backward from (y,t) gives R <= 4 R(y) on a     *)
(*   parabolic ball of size R(y)^(-1/2), so abs Rm <= K R(y), and scaled    *)
(*   Shi (RFA_C2_SHI_SCALED) gives abs(nabla^l Rm)^2 <= Cl R(y)^(l+2);       *)
(* - R >= c (Prop 12.31) and R(y) <= 2 C R(x) on U (RFA_C2_RATIO) give the  *)
(*   normalized bound (RFA_C2_NORMALIZE).                                   *)
(* ========================================================================= *)

needs "src/pc_rfa_c2base.ml";;
needs "src/pc_p2c_stdgeom.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Basic facts on standard flows and the identity atlas of                   *)
(* real^3, and the derivative bounds at every point of a slice 0 < s < 1    *)
(* (Thm 12.32: caps, and evolving necks, which contain slice necks;          *)
(* P2C_CANON_DERIV with the constant Cd = max C' 2).                         *)
(* ------------------------------------------------------------------------- *)

let RFA_STD_BASICS = prove
 (`!g0 (G:real->real^3->real^3^3).
     p3_std_flow g0 (&1) G
     ==> ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\
         G (&0) = g0 /\
         smooth_manifold_atlas (euclidean:(real^3)topology) (open_set_atlas (:real^3)) /\
         hausdorff_space (euclidean:(real^3)topology) /\
         topspace (euclidean:(real^3)topology) = (:real^3) /\
         (!t. &0 <= t /\ t < &1
              ==> riemannian_metric (open_set_atlas (:real^3)) (G t) /\
                  mfd_complete (euclidean,open_set_atlas (:real^3)) (G t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_std_flow; p3_partial_std] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                 (G:real->real^3->real^3^3)` THEN
  REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [UNDISCH_TAC `t = &0` THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RFA_STD_CANON_DERIV = prove
 (`P2_THM_12_32_STATEMENT
   ==> ?eps0. &0 < eps0 /\
         !g0 A0 eps.
           p3_std_initial g0 A0 /\ &0 < eps /\ eps <= eps0
           ==> ?Cd. &2 <= Cd /\
                 !G s z. p3_std_flow g0 (&1) G /\ &0 < s /\ s < &1
                   ==> &0 < mfd_scalar (open_set_atlas (:real^3)) (G s) z /\
                       sqrt(rfs_scalar_grad2 (open_set_atlas (:real^3)) (G s) z) <=
                       Cd * mfd_scalar (open_set_atlas (:real^3)) (G s) z *
                       sqrt(mfd_scalar (open_set_atlas (:real^3)) (G s) z) /\
                       abs(rfs_scalar_lap (open_set_atlas (:real^3)) (G s) z +
                           &2 * rfs_ric_norm2 (open_set_atlas (:real^3)) (G s) z) <=
                       Cd * mfd_scalar (open_set_atlas (:real^3)) (G s) z pow 2`,
  REWRITE_TAC[P2_THM_12_32_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t1232"))) THEN
  MP_TAC(ISPEC `(:real^3)` P2C_CANON_DERIV) THEN REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
  EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `eps:real`] THEN STRIP_TAC THEN
  USE_THEN "t1232" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "can"))) THEN
  EXISTS_TAC `max C1 (&2)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `s:real`; `z:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3))
                      ((G:real->real^3->real^3^3) s) C1 eps z U`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "can" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `z:real^3`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfs_canonical_nbhd; rfs_flow_view; rfs_evolving_neck] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE] THEN STRIP_TAC THENL
     [EXISTS_TAC `U:real^3->bool` THEN DISJ2_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps)` THEN DISJ1_TAC THEN
      EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps)` THEN DISJ1_TAC THEN
      EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "cd" (MP_TAC o SPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
    `(G:real->real^3->real^3^3) s`; `C1:real`; `eps:real`; `z:real^3`; `U:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The derivative bounds of canonical neighbourhoods on every                *)
(* slice 0 < s < 1 (rfa_std_dbounds g0 Cd, from RFA_STD_CANON_DERIV), the    *)
(* bound abs R(g0) <= D (bounded geometry of g0, RFA_FRAME3 and              *)
(* RFA_LSECTIONAL_LRM_BOUND), and Lemma 11.2 forward from the initial slice *)
(* (P2C_LEMMA_11_2_DB with r0^-2 = 2 D on the regular flow view): R <= 6 D   *)
(* for 0 <= s <= 1 / (48 Cd D).                                              *)
(* ------------------------------------------------------------------------- *)

let rfa_std_dbounds = new_definition
 `rfa_std_dbounds (g0:real^3->real^3^3) (Cd:real) <=>
    !G s z. p3_std_flow g0 (&1) G /\ &0 < s /\ s < &1
            ==> &0 < mfd_scalar (open_set_atlas (:real^3)) (G s) z /\
                sqrt(rfs_scalar_grad2 (open_set_atlas (:real^3)) (G s) z) <=
                Cd * mfd_scalar (open_set_atlas (:real^3)) (G s) z *
                sqrt(mfd_scalar (open_set_atlas (:real^3)) (G s) z) /\
                abs(rfs_scalar_lap (open_set_atlas (:real^3)) (G s) z +
                    &2 * rfs_ric_norm2 (open_set_atlas (:real^3)) (G s) z) <=
                Cd * mfd_scalar (open_set_atlas (:real^3)) (G s) z pow 2`;;

let RFA_STD_DBOUNDS = prove
 (`P2_THM_12_32_STATEMENT
   ==> ?eps0. &0 < eps0 /\
         !g0 A0 eps.
           p3_std_initial g0 A0 /\ &0 < eps /\ eps <= eps0
           ==> ?Cd. &2 <= Cd /\ rfa_std_dbounds g0 Cd`,
  REWRITE_TAC[rfa_std_dbounds; RFA_STD_CANON_DERIV]);;

let RFA_STD_DUP = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> ?D. &1 <= D /\
                   !x. abs(mfd_scalar (open_set_atlas (:real^3)) g0 x) <= D`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP P2CN_STD_RMD_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  EXISTS_TAC `max (&1) (&6 * sqrt C0)` THEN REWRITE_TAC[REAL_MAX_MAX; REAL_LE_MAX] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN X_GEN_TAC `x:real^3` THEN
  DISJ2_TAC THEN
  SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR; OPEN_UNIV; IN_UNIV] THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3, basis 1, basis 2}` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_NONCOLLINEAR_BASIS THEN REWRITE_TAC[DIMINDEX_3; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `x:real^3`;
                 `basis 1:real^3`; `basis 2:real^3`] RFA_FRAME3) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `w1:real^3`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (lhs(concl th)))) THEN
  SUBGOAL_THEN `sqrt(lrm_deriv_norm2 0 g0 (x:real^3)) <= sqrt C0` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `x:real^3`; `u1:real^3`; `v1:real^3`]
                RFA_LSECTIONAL_LRM_BOUND) THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `x:real^3`; `u1:real^3`; `w1:real^3`]
                RFA_LSECTIONAL_LRM_BOUND) THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `x:real^3`; `v1:real^3`; `w1:real^3`]
                RFA_LSECTIONAL_LRM_BOUND) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN ASM_REAL_ARITH_TAC);;

let RFA_STD_FORWARD_R = prove
 (`!g0 A0 Cd D (G:real->real^3->real^3^3) s z.
     p3_std_initial g0 A0 /\ &2 <= Cd /\ rfa_std_dbounds g0 Cd /\ &1 <= D /\
     (!x. mfd_scalar (open_set_atlas (:real^3)) g0 x <= D) /\
     p3_std_flow g0 (&1) G /\ &0 < s /\ s <= inv(&48 * Cd * D)
     ==> mfd_scalar (open_set_atlas (:real^3)) (G s) z <= &6 * D`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "db") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(&48 * Cd * D) < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_LT_1 THEN
    SUBGOAL_THEN `&2 * &1 <= Cd * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  ABBREV_TAC `V = rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                {s | &0 <= s /\ s < &1} (G:real->real^3->real^3^3)` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->(real^3)topology)#
                                    (real->((real^3->bool)#(real^3->real^3))->bool)#
                                    (real->real^3->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MP_TAC(ISPEC `(:real^3)` P2C_FLOW_VIEW_REGULAR) THEN
    REWRITE_TAC[P2C_FLOW_VIEW_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!t. rfs_vatlas (V:(real->(real^3)topology)#
                      (real->((real^3->bool)#(real^3->real^3))->bool)#
                      (real->real^3->real^3^3)) t = open_set_atlas (:real^3)) /\
    (!t. rfs_vmetric V t = G t) /\
    (!t. rfs_vtop V t = if t IN {s | &0 <= s /\ s < &1} then euclidean
                        else discrete_topology {}) /\
    (!t x. rfs_vscalar V t x = mfd_scalar (open_set_atlas (:real^3)) (G t) x) /\
    (!t x r. rfs_vball V t x r = mfd_ball (rfs_vtop V t,open_set_atlas (:real^3)) (G t) x r)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
    REWRITE_TAC[rfs_flow_view; rfs_vscalar; rfs_vball; rfs_vtop];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vtop (V:(real->(real^3)topology)#
                            (real->((real^3->bool)#(real^3->real^3))->bool)#
                            (real->real^3->real^3^3)) (&0) = euclidean /\
                rfs_vtop V s = euclidean` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * D /\ &0 < sqrt(&2 * D) /\ inv(inv(sqrt(&2 * D)) pow 2) = &2 * D`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_POW_INV; REAL_INV_INV; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `rr = inv(&2 * Cd * sqrt(&2 * D))` THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (open_set_atlas (:real^3)) (g0:real^3->real^3^3) z <= D`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (V:(real->(real^3)topology)#
                                (real->((real^3->bool)#(real^3->real^3))->bool)#
                                (real->real^3->real^3^3))
                  (mfd_ball (euclidean,open_set_atlas (:real^3)) (g0:real^3->real^3^3) z rr)
                  (&0) s` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[P2CF_FLOW_PERSISTS] THEN X_GEN_TAC `u:real` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `u IN {s | &0 <= s /\ s < &1}` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo (euclidean:(real^3)topology) (open_set_atlas (:real^3))
                  (mfd_ball (euclidean,open_set_atlas (:real^3)) (g0:real^3->real^3^3) z rr)
                  (euclidean:(real^3)topology) (open_set_atlas (:real^3))
                  (mfd_ball (euclidean,open_set_atlas (:real^3)) g0 z rr)
                  (\y:real^3. y) (\y. y)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL
      [`mfd_ball (euclidean,open_set_atlas (:real^3)) (g0:real^3->real^3^3) z rr`;
       `&0`; `s:real`] o el 4 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^3)` P2C_LEMMA_11_2_DB) THEN REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
       (real->real^3->real^3^3)`;
    `Cd:real`; `inv(sqrt(&2 * D))`; `z:real^3`; `&0`; `s:real`; `rr:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `min (&0) s = &0 /\ max (&0) s = s` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `t = &0` THENL
       [UNDISCH_TAC `&2 * D <= mfd_scalar (open_set_atlas (:real^3))
                                ((G:real->real^3->real^3^3) t) x` THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `D:real`)) (concl th) &&
          not (can (find_term (fun t -> t = `G:real->real^3->real^3^3`)) (concl th)))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "db" (MP_TAC o REWRITE_RULE[rfa_std_dbounds]) THEN
      DISCH_THEN(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `t:real`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[IN_UNIV];
      SUBGOAL_THEN `max (mfd_scalar (open_set_atlas (:real^3)) (g0:real^3->real^3^3) z)
                        (&2 * D) = &2 * D` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LE_REFL]];
      REWRITE_TAC[REAL_SUB_RZERO] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&48 * Cd * D)` THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < b ==> &0 < max (&0) a + b`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `&16 * Cd * (max (&0) (mfd_scalar (open_set_atlas (:real^3))
                       (g0:real^3->real^3^3) z) + &2 * D) <= &16 * Cd * (&3 * D)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `z:real^3`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_SIMP_TAC[MFD_CENTRE_IN_BALL; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Short times.  The slices of a standard flow have sec >= 0                 *)
(* (Thm 12.5 for t > 0, Def 12.1 at t = 0), so abs Rm <= 2 R + 2 exp 4; on  *)
(* [0,T1), T1 = 1/(48 Cd D), R <= 6 D (RFA_STD_FORWARD_R), and Shi with     *)
(* initial data (RFA_P2_THM_3_29, l = 2, r = 1) with the bounded geometry of *)
(* g0 (P2CN_STD_RMD_BOUND) bounds abs(nabla^l Rm)^2, l <= 2, by Cs.          *)
(* ------------------------------------------------------------------------- *)

let RFA_STD_NONNEG = prove
 (`!g0 A0 (G:real->real^3->real^3^3) t.
     P2_THM_12_5_STATEMENT /\ p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G /\
     &0 <= t /\ t < &1
     ==> !x u v. ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (G t) x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[p3_std_initial];
    ALL_TAC] THEN
  UNDISCH_TAC `P2_THM_12_5_STATEMENT` THEN REWRITE_TAC[P2_THM_12_5_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `G:real->real^3->real^3^3`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let RFA_STD_RM = prove
 (`!g0 A0 (G:real->real^3->real^3^3) t x.
     P2_THM_12_5_STATEMENT /\ p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G /\
     &0 <= t /\ t < &1
     ==> mfd_rm_norm (open_set_atlas (:real^3)) (G t) x <=
         &2 * mfd_scalar (open_set_atlas (:real^3)) (G t) x + &2 * exp(&4)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_C2_NONNEG_RM THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
  ASM_SIMP_TAC[IN_UNIV] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `t:real`]
                RFA_STD_NONNEG) THEN
  ASM_SIMP_TAC[]);;

let RFA_STD_SHORT_R6 = prove
 (`!g0 A0 Cd D (G:real->real^3->real^3^3) s y.
     p3_std_initial g0 A0 /\ &2 <= Cd /\ rfa_std_dbounds g0 Cd /\ &1 <= D /\
     (!x. abs(mfd_scalar (open_set_atlas (:real^3)) g0 x) <= D) /\
     p3_std_flow g0 (&1) G /\ &0 <= s /\ s < inv(&48 * Cd * D)
     ==> mfd_scalar (open_set_atlas (:real^3)) (G s) y <= &6 * D`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ab") STRIP_ASSUME_TAC))))) THEN
  ASM_CASES_TAC `s = &0` THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ab" (MP_TAC o SPEC `y:real^3`) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RFA_STD_FORWARD_R THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `Cd:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN USE_THEN "ab" (MP_TAC o SPEC `w:real^3`) THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

let RFA_STD_SHORT_RMD = prove
 (`!g0 A0 Cd.
     P2_THM_12_5_STATEMENT /\ p3_std_initial g0 A0 /\ &2 <= Cd /\ rfa_std_dbounds g0 Cd
     ==> ?T1 Cs. &0 < T1 /\ T1 < &1 /\ &0 < Cs /\
                 !G t z l. p3_std_flow g0 (&1) G /\ &0 <= t /\ t < T1 /\ l <= 2
                           ==> lrm_deriv_norm2 l ((G:real->real^3->real^3^3) t) z <= Cs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC o MATCH_MP RFA_STD_DUP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2CN_STD_RMD_BOUND) THEN DISCH_THEN(fun th ->
    X_CHOOSE_TAC `K0:real` (SPEC `0` th) THEN X_CHOOSE_TAC `K1:real` (SPEC `1` th) THEN
    X_CHOOSE_TAC `K2:real` (SPEC `2` th)) THEN
  ABBREV_TAC `T1 = inv(&48 * Cd * D)` THEN
  ABBREV_TAC `Kb = max (&12 * D + &2 * exp(&4)) (max K0 (max K1 K2))` THEN
  SUBGOAL_THEN `&0 < T1 /\ T1 < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN
      SUBGOAL_THEN `&2 * &1 <= Cd * D` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Kb /\ &12 * D + &2 * exp(&4) <= Kb /\ K0 <= Kb /\ K1 <= Kb /\ K2 <= Kb`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^3)` RFA_P2_THM_3_29) THEN REWRITE_TAC[P2_THM_3_29_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`2`; `Kb:real`; `&1`; `T1:real`]) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "shi")) THEN
  MAP_EVERY EXISTS_TAC [`T1:real`; `max Cl (&1)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `z:real^3`; `l:num`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s y. &0 <= s /\ s < T1
                      ==> mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s) y
                          <= &6 * D` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_STD_SHORT_R6 THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `Cd:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `T1:real`;
    `G:real->real^3->real^3^3`; `z:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[IN_UNIV] THEN
      CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th)))
      THEN REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s) y +
                  &2 * exp(&4)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_STD_RM THEN MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^3`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun t -> t = `&6 * D`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`j:num`; `y:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[P2CN_OPEN_UNIV_CONV] THEN
      SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `t:real`; `z:real^3`]) THEN
  REWRITE_TAC[P2CN_OPEN_UNIV_CONV] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `(G:real->real^3->real^3^3) (&0)`; `z:real^3`; `&1 / &2`]
                  MFD_CENTRE_IN_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th)))
      THEN REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Later times t >= T1.  With q = R(y,t) and                                 *)
(* Dt = min (1/(32 Cd q)) (T1/2), Lemma 11.2 backward from (y,t)             *)
(* (P2C_LEMMA_11_2_DB, r0^-2 = q, r' = 1/(2 Cd sqrt q)) gives R <= 4 q on    *)
(* the parabolic ball, so abs Rm <= (8 + 2 exp 4 / c) q there (R >= c), and  *)
(* scaled Shi (RFA_C2_SHI_SCALED, q Dt >= min (1/(32 Cd)) (c T1/2)) gives    *)
(* abs(nabla^l Rm)^2 <= Cl q^(l+2) at (y,t).                                 *)
(* ------------------------------------------------------------------------- *)

let RFA_STD_BACK_R = prove
 (`!g0 Cd T1 (G:real->real^3->real^3^3) t y.
     &2 <= Cd /\ rfa_std_dbounds g0 Cd /\ &0 < T1 /\ T1 < &1 /\
     p3_std_flow g0 (&1) G /\ T1 <= t /\ t < &1
     ==> !s w. t - min (inv(&32 * Cd * mfd_scalar (open_set_atlas (:real^3)) (G t) y))
                        (T1 / &2) < s /\ s <= t /\
               w IN mfd_ball (euclidean,open_set_atlas (:real^3)) (G t) y
                      (inv(&2 * Cd) / sqrt(mfd_scalar (open_set_atlas (:real^3)) (G t) y))
               ==> mfd_scalar (open_set_atlas (:real^3)) (G s) w <=
                   &4 * mfd_scalar (open_set_atlas (:real^3)) (G t) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "db") STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `q = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) y` THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN USE_THEN "db" (MP_TAC o REWRITE_RULE[rfa_std_dbounds]) THEN
    DISCH_THEN(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `t:real`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Dt = min (inv(&32 * Cd * q)) (T1 / &2)` THEN
  SUBGOAL_THEN `&0 < Dt /\ Dt <= inv(&32 * Cd * q) /\ Dt <= T1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Dt" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt q /\ inv(inv(sqrt q) pow 2) = q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_POW_INV; REAL_INV_INV; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `rr = inv(&2 * Cd) / sqrt q` THEN
  SUBGOAL_THEN `&0 < rr /\ inv(&2 * Cd * sqrt q) = rr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  ABBREV_TAC `V = rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                {s | &0 <= s /\ s < &1} (G:real->real^3->real^3^3)` THEN
  SUBGOAL_THEN `p2c_regular_view (V:(real->(real^3)topology)#
                                    (real->((real^3->bool)#(real^3->real^3))->bool)#
                                    (real->real^3->real^3^3))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MP_TAC(ISPEC `(:real^3)` P2C_FLOW_VIEW_REGULAR) THEN
    REWRITE_TAC[P2C_FLOW_VIEW_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!t. rfs_vatlas (V:(real->(real^3)topology)#
                      (real->((real^3->bool)#(real^3->real^3))->bool)#
                      (real->real^3->real^3^3)) t = open_set_atlas (:real^3)) /\
    (!t. rfs_vmetric V t = G t) /\
    (!t. rfs_vtop V t = if t IN {s | &0 <= s /\ s < &1} then euclidean
                        else discrete_topology {}) /\
    (!t x. rfs_vscalar V t x = mfd_scalar (open_set_atlas (:real^3)) (G t) x) /\
    (!t x r. rfs_vball V t x r = mfd_ball (rfs_vtop V t,open_set_atlas (:real^3)) (G t) x r)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
    REWRITE_TAC[rfs_flow_view; rfs_vscalar; rfs_vball; rfs_vtop];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vtop (V:(real->(real^3)topology)#
                            (real->((real^3->bool)#(real^3->real^3))->bool)#
                            (real->real^3->real^3^3)) t = euclidean` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (V:(real->(real^3)topology)#
                                (real->((real^3->bool)#(real^3->real^3))->bool)#
                                (real->real^3->real^3^3))
                  (mfd_ball (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) y rr)
                  (t - Dt) t` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[P2CF_FLOW_PERSISTS] THEN X_GEN_TAC `u:real` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `u IN {s | &0 <= s /\ s < &1}` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^3)` P2C_LEMMA_11_2_DB) THEN REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
       (real->real^3->real^3^3)`;
    `Cd:real`; `inv(sqrt q)`; `y:real^3`; `t:real`; `t - Dt`; `rr:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `min t (t - Dt) = t - Dt /\ max t (t - Dt) = t /\ ~(t < t - Dt) /\
                max q q = q /\ max (&0) q + q = &2 * q /\ abs(t - Dt - t) = Dt`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real`] THEN STRIP_TAC THEN
      USE_THEN "db" (MP_TAC o REWRITE_RULE[rfa_std_dbounds]) THEN
      DISCH_THEN(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `s:real`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[IN_UNIV];
      ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&32 * Cd * q)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&16 * Cd * &2 * q = &32 * Cd * q` (fun th -> REWRITE_TAC[th; REAL_LE_REFL])
      THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `w:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_STD_LATE_RMD = prove
 (`!g0 A0 Cd T1 c.
     P2_THM_12_5_STATEMENT /\ p3_std_initial g0 A0 /\ &2 <= Cd /\ rfa_std_dbounds g0 Cd /\
     &0 < T1 /\ T1 < &1 /\ &0 < c /\
     (!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1
              ==> c <= mfd_scalar (open_set_atlas (:real^3)) (G t) x)
     ==> !l. ?Cl. &0 < Cl /\
               !G t y. p3_std_flow g0 (&1) G /\ T1 <= t /\ t < &1
                       ==> lrm_deriv_norm2 l ((G:real->real^3->real^3^3) t) y <=
                           Cl * mfd_scalar (open_set_atlas (:real^3)) (G t) y pow (l + 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "db")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lower")))))))) THEN
  X_GEN_TAC `l:num` THEN
  ABBREV_TAC `K = &8 + (&2 * exp(&4)) / c` THEN
  ABBREV_TAC `tau = min (inv(&32 * Cd)) (c * T1 / &2)` THEN
  SUBGOAL_THEN `&0 < K /\ &0 < tau /\ &0 < inv(&2 * Cd) /\
                tau <= inv(&32 * Cd) /\ tau <= c * T1 / &2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "tau"] THEN REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &8 + x`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`l:num`; `K:real`; `inv(&2 * Cd)`; `tau:real`]
               (INST_TYPE [`:real^3`,`:A`] RFA_C2_SHI_SCALED)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shi"))) THEN
  EXISTS_TAC `Cl:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `Cd:real`; `T1:real`; `G:real->real^3->real^3^3`;
                 `t:real`; `y:real^3`] RFA_STD_BACK_R) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "back") THEN
  ABBREV_TAC `q = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) y` THEN
  SUBGOAL_THEN `c <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN USE_THEN "lower" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Dt = min (inv(&32 * Cd * q)) (T1 / &2)` THEN
  SUBGOAL_THEN `&0 < Dt /\ Dt <= T1 / &2 /\ tau <= q * Dt` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Dt" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "Dt" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `Dt = inv(&32 * Cd * q) \/ Dt = T1 / &2` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "Dt" THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `q * inv(&32 * Cd * q) = inv(&32 * Cd)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&2 <= Cd` THEN CONV_TAC REAL_FIELD;
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `c * T1 / &2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt q` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `t - Dt`; `t:real`;
    `G:real->real^3->real^3^3`; `y:real^3`; `q:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV; REAL_ARITH `t - (t - Dt) = Dt`] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[IN_UNIV] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th)))
      THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `w:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s) w +
                  &2 * exp(&4)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_STD_RM THEN MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s) w <=
                    &4 * q` MP_TAC THENL
       [USE_THEN "back" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `!a. &0 <= a ==> a <= a / c * q` (MP_TAC o SPEC `&2 * exp(&4)`) THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a / c * c` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ANTS_TAC THENL [MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "K" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN REWRITE_TAC[P2CN_OPEN_UNIV_CONV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(G:real->real^3->real^3^3) t`; `y:real^3`;
                 `(inv(&2 * Cd) / &2) / sqrt q`] MFD_CENTRE_IN_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The headline R14.  For y in U and l <= 2: at t < T1 the                   *)
(* absolute bound Cs with R(x) >= c; at t >= T1 the bound Cl R(y)^(l+2)      *)
(* with R(y) <= 2 C R(x) (RFA_C2_RATIO); RFA_C2_NORMALIZE.                   *)
(* ------------------------------------------------------------------------- *)

let RFA_STD_POW_ARITH1 = prove
 (`!c R Cs l. &0 < c /\ c <= R /\ &0 <= Cs /\ l <= 2
              ==> Cs <= (Cs * max (&1) (inv c) pow 4) * R pow (l + 2)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `M = max (&1) (inv c)` THEN
  SUBGOAL_THEN `&1 <= M /\ inv c <= M` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= M * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv c * c` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= M pow 4 * R pow (l + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M pow (l + 2) * R pow (l + 2)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let RFA_STD_POW_ARITH2 = prove
 (`!a b C Cl l. &0 <= a /\ a <= &2 * C * b /\ &1 < C /\ &0 <= Cl /\ l <= 2
                ==> Cl * a pow (l + 2) <= (Cl * (&2 * C) pow 4) * b pow (l + 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * C * b) pow (l + 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x. &0 <= x /\ x <= &2 * C * b /\ &1 < C /\
                                 (b < &0 ==> &2 * C * b < &0) ==> &0 <= b`) THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC(REAL_ARITH `&0 < x * --b ==> x * b < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * C * b) pow (l + 2) = (&2 * C) pow (l + 2) * b pow (l + 2)`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM REAL_POW_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]]);;

let RFA_P3_STD_C2_BOUND = prove
 (`P2_THM_12_5_STATEMENT /\ P2_THM_12_32_STATEMENT /\ P2_PROP_12_31_STATEMENT
   ==> P3_STD_C2_BOUND_STATEMENT`,
  STRIP_TAC THEN REWRITE_TAC[P3_STD_C2_BOUND_STATEMENT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_STD_DBOUNDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dbs"))) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ratio"))
    (INST_TYPE [`:real^3`,`:A`] RFA_C2_RATIO) THEN
  EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN
  STRIP_TAC THEN
  USE_THEN "dbs" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cd:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `Cd:real`] RFA_STD_SHORT_RMD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` (X_CHOOSE_THEN `Cs:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "short")))))) THEN
  UNDISCH_TAC `P2_PROP_12_31_STATEMENT` THEN REWRITE_TAC[P2_PROP_12_31_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1231"))) THEN
  SUBGOAL_THEN `!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1
                        ==> c <= mfd_scalar (open_set_atlas (:real^3))
                                   ((G:real->real^3->real^3^3) t) x` (LABEL_TAC "lower") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / (&1 - t)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "c1231" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `Cd:real`; `T1:real`; `c:real`]
                RFA_STD_LATE_RMD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "lower" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    X_CHOOSE_THEN `L0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l0")) (SPEC `0` th) THEN
    X_CHOOSE_THEN `L1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l1")) (SPEC `1` th) THEN
    X_CHOOSE_THEN `L2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l2")) (SPEC `2` th)) THEN
  ABBREV_TAC `Lm = max L0 (max L1 L2)` THEN
  SUBGOAL_THEN `&0 < Lm /\ L0 <= Lm /\ L1 <= Lm /\ L2 <= Lm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Lm" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!G t y l. p3_std_flow g0 (&1) G /\ T1 <= t /\ t < &1 /\ l <= 2
                          ==> lrm_deriv_norm2 l ((G:real->real^3->real^3^3) t) y <=
                              Lm * mfd_scalar (open_set_atlas (:real^3)) (G t) y pow (l + 2)`
  (LABEL_TAC "late") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= mfd_scalar (open_set_atlas (:real^3))
                          ((G:real->real^3->real^3^3) t) y pow (l + 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN USE_THEN "lower" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `l = 0 \/ l = 1 \/ l = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [REMOVE_THEN "l0" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `t:real`; `y:real^3`]);
      REMOVE_THEN "l1" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `t:real`; `y:real^3`]);
      REMOVE_THEN "l2" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `t:real`; `y:real^3`])] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `max (max Cs (&0) * max (&1) (inv c) pow 4) (Lm * (&2 * C) pow 4)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < b ==> &0 < max a b`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `x:real^3`; `U:real^3->bool`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`y:real^3`; `l:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`] RFA_STD_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ratio" (MP_TAC o SPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
    `(G:real->real^3->real^3^3) t`; `C:real`; `eps:real`; `x:real^3`; `U:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC RFA_C2_NORMALIZE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
  ASM_REWRITE_TAC[IN_UNIV; P2CN_OPEN_UNIV_CONV] THEN
  ABBREV_TAC `Rx = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) x` THEN
  SUBGOAL_THEN `c <= Rx` ASSUME_TAC THENL
   [EXPAND_TAC "Rx" THEN USE_THEN "lower" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Rx pow (l + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t < T1` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(max Cs (&0) * max (&1) (inv c) pow 4) * Rx pow (l + 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `max Cs (&0)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max b (&0)`) THEN
        USE_THEN "short" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFA_STD_POW_ARITH1 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Lm * (&2 * C) pow 4) * Rx pow (l + 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Lm * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) y
                     pow (l + 2)` THEN
    CONJ_TAC THENL
     [USE_THEN "late" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_STD_POW_ARITH2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      USE_THEN "lower" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

