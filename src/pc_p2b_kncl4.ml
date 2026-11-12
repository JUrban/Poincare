(* ========================================================================= *)
(* Unit pc_p2b_kncl4: piece (d) of COR_9_94_L (MT Cor 9.88 in the length-L   *)
(* form), the case split and the route theorem KNCL_ROUTE |- !w.             *)
(* P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT w, from KNCL_ROUTE_CAPC (the  *)
(* route from P2B_KNCL_CAPC_STATEMENT) and P2BCC_KNCL_CAPC (pc_p2b_kncapc).  *)
(* Positive curvature at time 0: the soul cap of pc_p2b_kncl2 with the       *)
(* constants of P2B_KNCL_CAPC_STATEMENT (proved in pc_p2b_kncapc); the       *)
(* one-to-one cylinder model: KNCL_M1_CANON; the Z/2 quotient:               *)
(* RFA_P2B_KNCL_TWISTED_CANON (pc_rfa_ktw).                                  *)
(* ========================================================================= *)

needs "src/pc_p2b_kncl2.ml";;
needs "src/pc_p2b_kncapcreq.ml";;
needs "src/pc_p2b_kncapc.ml";;
needs "src/pc_rfa_ktw.ml";;
needs "src/pc_p2b_c994.ml";;
needs "src/pc_cmp_myers.ml";;
needs "src/pc_cmp_bg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A complete noncompact connected slice is not round.  Same content as      *)
(* P2AS85_NOT_ROUND (pc_p2a_s85a); proved independently via                  *)
(* CMP_MYERS_DIAMETER_RIC (loading pc_p2a_s85a would add 22 files).          *)
(* Constant curvature k > 0 bounds Ric below by 2k g >= k g, so all of the   *)
(* space lies in one closed ball, which is compact by completeness.          *)
(* ------------------------------------------------------------------------- *)

let KNCL_NOT_ROUND = prove
 (`!top atlas (g:B->real^3^3).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ ~compact_space top
     ==> ~p2b_round (top,atlas) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2b_round] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `topspace (top:B topology) = {}` THENL
   [UNDISCH_TAC `~compact_space (top:B topology)` THEN
    ASM_REWRITE_TAC[compact_space; COMPACT_IN_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:B` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN
   `!z w. z IN topspace top
          ==> k * (w dot ((g:B->real^3^3) z ** w)) <= mfd_ricci atlas g z w w`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:B`; `w:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `z:B`; `k:real`; `w:real^3`]
                  CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `&0 <= w dot ((g:B->real^3^3) z ** w)` MP_TAC THENL
     [ASM_CASES_TAC `w:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `z:B`] RIEMANNIAN_METRIC_POS) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SPEC_TAC(`w dot ((g:B->real^3^3) z ** w)`,`q:real`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= k * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace top = mfd_cball (top,atlas) (g:B->real^3^3) x0 (&2 + &4 / k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) x0 y` ASSUME_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `k:real`; `&1`; `x0:B`; `y:B`]
                    CMP_MYERS_DIAMETER_RIC) THEN
      ASM_REWRITE_TAC[REAL_LT_01; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC;
      STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~compact_space (top:B topology)` THEN REWRITE_TAC[compact_space] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `topspace (top:B topology)`)) THEN
  UNDISCH_TAC `mfd_complete (top,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
  REWRITE_TAC[mfd_complete] THEN DISCH_THEN(MP_TAC o SPECL [`x0:B`; `&2 + &4 / k`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The positively curved case.  The soul p (CMP_R5_SOUL) is no               *)
(* strong neck centre ((c) part 1), so (b) applies at p for eps (length L)   *)
(* and for eps/K1 (length 1); the soul cap of KNCL_SOUL_CAP with the radius *)
(* max D D0 is a (C,eps)-cap by P2B_KNCL_CAPC_STATEMENT (instance given as  *)
(* a hypothesis); points of the D-ball lie in its core, the others are     *)
(* centres of evolving eps-necks of length L.                               *)
(* ------------------------------------------------------------------------- *)

let KNCL_PINCH_MONO = prove
 (`!a b R s. &0 < R /\ &0 < a /\ a <= b /\ inv a * R < s /\ s < a * R
             ==> inv b * R < s /\ s < b * R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv a * R` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `a * R` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;

let KNCL_CASE_P = prove
 (`!eps L K1 D D1 D0 D01 Ccap kappa0 C71 ec0 kappa top atlas (g:real->B->real^3^3) x.
     &0 < eps /\
     eps <= &1 / &100 /\
     eps <= ec0 /\
     &4 <= K1 /\
     &1 < D /\
     &1 < D1 /\
     &1 < D0 /\
     &1 < D01 /\
     &1 < Ccap /\
     &0 < kappa0 /\
     &0 < C71 /\
     &1 <= L /\
     (!top atlas (g:B->real^3^3) eps z (e:real^3->B).
       &0 < eps /\ eps <= &1 / &2 /\ riemannian_metric atlas g /\
       rfs_neck (top,atlas) g (eps / K1) z e
       ==> rfs_neck (top,atlas) g eps (e(exp(inv(sqrt(&2) * eps)) % basis 1))
                    (e o (\w. exp(inv(sqrt(&2) * eps)) % w)) /\
           rfs_neck (top,atlas) g eps (e(exp(&2 * inv(sqrt(&2) * eps)) % basis 1))
                    (e o (\w. exp(&2 * inv(sqrt(&2) * eps)) % w)) /\
           IMAGE (e o (\w. exp(inv(sqrt(&2) * eps)) % w)) (rfs_neck_dom eps) =
             IMAGE e (annulus (&1) (exp(&2 * inv(sqrt(&2) * eps)))) /\
           IMAGE (e o (\w. exp(&2 * inv(sqrt(&2) * eps)) % w)) (rfs_neck_dom eps) =
             IMAGE e (annulus (exp(inv(sqrt(&2) * eps)))
                              (exp(&3 * inv(sqrt(&2) * eps))))) /\
     (!top atlas (g:B->real^3^3) z (e:real^3->B) y.
       riemannian_metric atlas g /\ rfs_neck (top,atlas) g (eps / K1) z e /\
       y IN rfs_neck_dom (eps / K1)
       ==> mfd_scalar atlas g z / &2 <= mfd_scalar atlas g (e y) /\
           mfd_scalar atlas g (e y) <= &3 / &2 * mfd_scalar atlas g z) /\
     (!eps top atlas (g:B->real^3^3) p. &0 < eps /\ eps <= ec0 /\ hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\ (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) ==> (!z e. rfs_neck (top,atlas) g eps z e ==> ~(p IN IMAGE e (rfs_neck_dom (&3 / &2 * eps)))) /\ (!z e. rfs_neck (top,atlas) g eps z e /\ ~(p IN IMAGE e (rfs_neck_dom eps)) /\ apx_separates top (IMAGE e (sphere(vec 0,&1))) p (e(&4 / &3 % basis 1)) ==> ?b f f'. mfd_ball_chart top atlas b /\ sphere_diffeo f f' /\ p IN IMAGE b (ball(vec 0,&1)) /\ IMAGE b (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1)) /\ (!y. y IN annulus (&1) (&2) ==> b y = e(radial_ext f y)))) /\
     (!kappa top atlas (g:real->B->real^3^3) p. p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ ~compact_space top /\ (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\ p IN topspace top /\ ~(?e. rfs_strong_neck (p2b_kview (top,atlas) g) eps p (&0) e) ==> (!x. x IN topspace top /\ ~(x IN mfd_ball (top,atlas) (g(&0)) p (D * inv(sqrt(mfd_scalar atlas (g(&0)) p)))) ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) L e) /\ (!x u v. x IN mfd_ball (top,atlas) (g(&0)) p (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\ ~collinear {vec 0,u,v} ==> inv D1 * mfd_scalar atlas (g(&0)) p < mfd_sectional atlas (g(&0)) x u v /\ mfd_sectional atlas (g(&0)) x u v < D1 * mfd_scalar atlas (g(&0)) p)) /\
     (!kappa top atlas (g:real->B->real^3^3) p. p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ ~compact_space top /\ (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\ p IN topspace top /\ ~(?e. rfs_strong_neck (p2b_kview (top,atlas) g) (eps / K1) p (&0) e) ==> (!x. x IN topspace top /\ ~(x IN mfd_ball (top,atlas) (g(&0)) p (D0 * inv(sqrt(mfd_scalar atlas (g(&0)) p)))) ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) (eps / K1) x (&0) (&1) e) /\ (!x u v. x IN mfd_ball (top,atlas) (g(&0)) p (D0 * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\ ~collinear {vec 0,u,v} ==> inv D01 * mfd_scalar atlas (g(&0)) p < mfd_sectional atlas (g(&0)) x u v /\ mfd_sectional atlas (g(&0)) x u v < D01 * mfd_scalar atlas (g(&0)) p)) /\
     (!top atlas (g:real->B->real^3^3) p U Y z3 (e3:real^3->B) w0. p2b_kappa_solution kappa0 (top,atlas) g /\ ~compact_space top /\ (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\ (!x. x IN topspace top ==> sqrt(rfs_scalar_grad2 atlas (g(&0)) x) <= C71 * mfd_scalar atlas (g(&0)) x * sqrt(mfd_scalar atlas (g(&0)) x) /\ abs(rfs_scalar_lap atlas (g(&0)) x + &2 * rfs_ric_norm2 atlas (g(&0)) x) <= C71 * mfd_scalar atlas (g(&0)) x pow 2) /\ p IN topspace top /\ &0 < mfd_scalar atlas (g(&0)) p /\ (!x u v. x IN mfd_ball (top,atlas) (g(&0)) p ((max D D0) * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\ ~collinear {vec 0,u,v} ==> inv (max D1 D01) * mfd_scalar atlas (g(&0)) p < mfd_sectional atlas (g(&0)) x u v /\ mfd_sectional atlas (g(&0)) x u v < (max D1 D01) * mfd_scalar atlas (g(&0)) p) /\ (?b e e' z z' f f'. mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\ Y = IMAGE b (ball(vec 0,&1)) /\ rfs_neck (top,atlas) (g(&0)) eps z e /\ IMAGE e (rfs_neck_dom eps) = U DIFF IMAGE b (cball(vec 0,&1)) /\ rfs_neck (top,atlas) (g(&0)) eps z' e' /\ IMAGE e' (rfs_neck_dom eps) SUBSET U /\ IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\ sphere_diffeo f f' /\ (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) /\ open_in top U /\ Y SUBSET U /\ mfd_ball (top,atlas) (g(&0)) p ((max D D0) * inv(sqrt(mfd_scalar atlas (g(&0)) p))) SUBSET Y /\ rfs_neck (top,atlas) (g(&0)) (eps / K1) z3 e3 /\ U SUBSET mfd_ball (top,atlas) (g(&0)) p ((max D D0) * inv(sqrt(mfd_scalar atlas (g(&0)) p))) UNION IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) /\ IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) SUBSET U /\ w0 IN apx_slab (--inv(eps / K1)) (&3 * inv eps) /\ e3 w0 IN mfd_ball (top,atlas) (g(&0)) p ((max D D0) * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\ (!y. y IN IMAGE e3 (rfs_neck_dom (eps / K1)) ==> mfd_scalar atlas (g(&0)) z3 / &2 <= mfd_scalar atlas (g(&0)) y /\ mfd_scalar atlas (g(&0)) y <= &3 / &2 * mfd_scalar atlas (g(&0)) z3) /\ (!y q. y IN Y /\ q IN topspace top /\ ~(q IN U) ==> ?s. s IN IMAGE e3 (rfs_neck_dom (eps / K1)) /\ mfd_joinable (top,atlas) y s /\ mfd_dist (top,atlas) (g(&0)) y s + sqrt(&1 - eps / K1) * inv(sqrt(mfd_scalar atlas (g(&0)) z3)) * (&2 * inv eps) <= mfd_dist (top,atlas) (g(&0)) y q) ==> rfs_cap (top,atlas) (g(&0)) Ccap eps U Y) /\
     (!kappa top atlas (g:real->B->real^3^3).
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
       ~p2b_round (top,atlas) (g(&0))
       ==> p2b_kappa_solution kappa0 (top,atlas) g) /\
     (!kappa top atlas (g:real->B->real^3^3) x t.
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
       x IN topspace top /\ t <= &0
       ==> sqrt(rfs_scalar_grad2 atlas (g t) x) <=
           C71 * mfd_scalar atlas (g t) x * sqrt(mfd_scalar atlas (g t) x) /\
           abs(rfs_scalar_lap atlas (g t) x + &2 * rfs_ric_norm2 atlas (g t) x) <=
           C71 * mfd_scalar atlas (g t) x pow 2) /\
     p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3) /\
     p2b_ksep top atlas /\
     ~compact_space (top:B topology) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\
     (x:B) IN topspace top
     ==> p2b_canon_L (p2b_kview (top,atlas) g) Ccap eps L x (&0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> EVERY (map2 (fun s t -> if s = "" then ASSUME_TAC t else LABEL_TAC s t)
    [""; ""; ""; ""; ""; ""; ""; ""; ""; ""; ""; ""; "pair"; "nsc"; "c"; "bL"; "b1"; "cap"; "k0"; "d71"; "ksol"; "ksep"; "ncpt"; "secpos"; "xin"] (CONJUNCTS th))) THEN
  USE_THEN "ksol" (fun th -> let r = MATCH_MP KNCL_KSOL_RIEM th in
    STRIP_ASSUME_TAC r THEN MP_TAC(SPEC `&0` (funpow 4 CONJUNCT2 r))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_sphere_sep top (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [USE_THEN "ksep" (MP_TAC o REWRITE_RULE[p2b_ksep]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps / K1 /\ eps / K1 <= eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= K1 ==> &0 < K1`] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e * &1 <= e * K ==> e <= e * K`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the soul *)
  MP_TAC(SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `(g:real->B->real^3^3)(&0)`]
    (REWRITE_RULE[CMP_R5_SOUL_STATEMENT] (ISPEC `UNIV:B->bool` CMP_R5_SOUL))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `p:B` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3)(&0)) p` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "secpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* (c) at eps and at eps / K1 *)
  USE_THEN "c" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3)(&0)`; `p:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1e") (LABEL_TAC "c2e"))] THEN
  USE_THEN "c" (MP_TAC o SPECL [`eps / K1`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3)(&0)`; `p:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c10") (K ALL_TAC))] THEN
  (* p is no strong neck centre *)
  SUBGOAL_THEN `!e1. &0 < e1 /\
                     (!z e. rfs_neck (top,atlas) ((g:real->B->real^3^3)(&0)) e1 z e
                            ==> ~(p IN IMAGE e (rfs_neck_dom (&3 / &2 * e1))))
                     ==> ~(?e. rfs_strong_neck (p2b_kview (top,atlas) g) e1 p (&0) e)`
  (LABEL_TAC "nostrong") THENL
   [X_GEN_TAC `e1:real` THEN STRIP_TAC THEN
    REWRITE_TAC[rfs_strong_neck] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->B` (ASSUME_TAC o CONJUNCT1 o MATCH_MP P2BL_KVIEW_NECK0)) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `rfs_neck (top,atlas) ((g:real->B->real^3^3)(&0)) e1 p e`) o
      check (fun th -> is_forall(concl th))) THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) ((g:real->B->real^3^3)(&0)) e1 p e` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(SPEC `&3 / &2 * e1` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(p:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  (* (b) at eps, L and at eps / K1, 1 *)
  USE_THEN "bL" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "nostrong" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nL") (LABEL_TAC "pL"))] THEN
  USE_THEN "b1" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "nostrong" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n1") (LABEL_TAC "p1"))] THEN
  ABBREV_TAC `rho = inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3)(&0)) p))` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the soul cap *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `eps:real`; `K1:real`; `p:B`; `max D D0`]
                KNCL_SOUL_CAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:B`; `e:real^3->B`] THEN DISCH_TAC THEN
      USE_THEN "pair" MATCH_MP_TAC THEN EXISTS_TAC `z:B` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:B` THEN STRIP_TAC THEN
      USE_THEN "n1" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN DISJ2_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `max D D0 * rho` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `e:real^3->B` (fun th -> EXISTS_TAC `e:real^3->B` THEN
          MP_TAC(CONJUNCT1(MATCH_MP P2BL_KVIEW_NECK0 th)) THEN SIMP_TAC[]))]];
    DISCH_THEN(X_CHOOSE_THEN `U:B->bool` (X_CHOOSE_THEN `Y:B->bool` (X_CHOOSE_THEN `z3:B`
      (X_CHOOSE_THEN `e3:real^3->B` (X_CHOOSE_THEN `w0:real^3` (LABEL_TAC "sc"))))))] THEN
  (* kappa0, not round *)
  SUBGOAL_THEN `~p2b_round (top,atlas) ((g:real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC KNCL_NOT_ROUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "k0" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the cap constants *)
  USE_THEN "sc" (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  USE_THEN "cap" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`; `e3:real^3->B`;
    `w0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [X_GEN_TAC `y:B` THEN DISCH_TAC THEN USE_THEN "d71" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      MAP_EVERY X_GEN_TAC [`y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `y IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) p (D * rho) \/
        y IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) p (D0 * rho)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) p
                               (max D D0 * rho)` THEN
        REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN SIMP_TAC[];
        SUBGOAL_THEN
         `inv D1 * mfd_scalar atlas ((g:real->B->real^3^3)(&0)) p <
          mfd_sectional atlas (g(&0)) y u v /\
          mfd_sectional atlas (g(&0)) y u v < D1 * mfd_scalar atlas (g(&0)) p`
        ASSUME_TAC THENL [USE_THEN "pL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC KNCL_PINCH_MONO THEN EXISTS_TAC `D1:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN
         `inv D01 * mfd_scalar atlas ((g:real->B->real^3^3)(&0)) p <
          mfd_sectional atlas (g(&0)) y u v /\
          mfd_sectional atlas (g(&0)) y u v < D01 * mfd_scalar atlas (g(&0)) p`
        ASSUME_TAC THENL [USE_THEN "p1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC KNCL_PINCH_MONO THEN EXISTS_TAC `D01:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "nsc" MATCH_MP_TAC THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  (* the canonical neighbourhood *)
  REWRITE_TAC[p2b_canon_L; P2B_KVIEW_SLICE0] THEN
  ASM_CASES_TAC `(x:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) p (D * rho)` THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`U:B->bool`; `Y:B->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) p
                    (max D D0 * inv(sqrt(mfd_scalar atlas (g(&0)) p))) SUBSET Y`)) THEN
    REWRITE_TAC[ASSUME `inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3)(&0)) p)) = rho`] THEN
    UNDISCH_TAC `(x:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) p (D * rho)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `D * rho` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    DISJ1_TAC THEN USE_THEN "nL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The route of piece (d).  eps2 = min(eb2, ec0, et2, eN, 1/100)             *)
(* with eb2 of (b), ec0 of (c), et2 of the twisted model, eN of             *)
(* KNCL_NECK_SCALAR; for eps, L: (b) at (eps, L) gives D, D1, (b) at        *)
(* (eps/K1, 1) gives D0, D01, the cap constants give Ccap for the radius    *)
(* max D D0 and the pinching max D1 D01, the twisted model gives Ctw, and   *)
(* C0 = max Ccap Ctw (P2BC94_CANON_L_MONO_C).  Cases by (a): positive       *)
(* curvature (KNCL_CASE_P), the one-to-one model (KNCL_M1_CANON) and the     *)
(* Z/2 quotient (RFA_P2B_KNCL_TWISTED_CANON).                                *)
(* ------------------------------------------------------------------------- *)

let KNCL_ROUTE_CAPC = prove
 (`!w:B->bool.
     P2B_KNCL_CAPC_STATEMENT w ==> P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT w`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "capc0") THEN
  REWRITE_TAC[P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a0") (CONJUNCTS_THEN2 (LABEL_TAC "b0")
    (CONJUNCTS_THEN2 (LABEL_TAC "c0") (CONJUNCTS_THEN2 (LABEL_TAC "h0")
    (CONJUNCTS_THEN2 (LABEL_TAC "k00") (LABEL_TAC "d710")))))) THEN
  USE_THEN "capc0" (LABEL_TAC "capc" o REWRITE_RULE[P2B_KNCL_CAPC_STATEMENT]) THEN
  USE_THEN "a0" (LABEL_TAC "a" o REWRITE_RULE[P2B_PROP_9_83K_STATEMENT]) THEN
  USE_THEN "b0" (X_CHOOSE_THEN `eb2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b")) o
    REWRITE_RULE[P2B_PROP_9_85L_STATEMENT]) THEN
  USE_THEN "c0" (X_CHOOSE_THEN `ec0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")) o
    REWRITE_RULE[P2B_SOUL_TOPOLOGY_STATEMENT]) THEN
  USE_THEN "k00" (X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k0")) o
    REWRITE_RULE[P2B_PROP_9_58_STATEMENT]) THEN
  USE_THEN "d710" (X_CHOOSE_THEN `C71:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d71")) o
    REWRITE_RULE[P2B_COR_9_71_STATEMENT]) THEN
  MP_TAC(ISPEC `UNIV:B->bool` RFA_P2B_KNCL_TWISTED_CANON) THEN
  REWRITE_TAC[P2B_KNCL_TWISTED_CANON_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `et2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tw"))) THEN
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pair"))
    (INST_TYPE [`:B`,`:A`] KNCL_NECK_PAIR) THEN
  X_CHOOSE_THEN `eN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nscg"))
    (INST_TYPE [`:B`,`:A`] KNCL_NECK_SCALAR) THEN
  REWRITE_TAC[P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT] THEN
  EXISTS_TAC `min (min (min eb2 ec0) (min et2 eN)) (&1 / &100)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eb2 /\ eps <= ec0 /\ eps <= et2 /\ eps <= eN /\ eps <= &1 / &100`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps / K1 /\ eps / K1 <= eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= K1 ==> &0 < K1`] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e * &1 <= e * K ==> e <= e * K`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the constants *)
  USE_THEN "b" (MP_TAC o SPECL [`eps:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `D1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bL"))))) THEN
  USE_THEN "b" (MP_TAC o SPECL [`eps / K1`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D01:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b1"))))) THEN
  USE_THEN "capc" (MP_TAC o SPECL [`eps:real`; `K1:real`; `max D D0`; `max D1 D01`;
                                   `kappa0:real`; `C71:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ccap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cap"))) THEN
  USE_THEN "tw" (MP_TAC o SPECL [`eps:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ctw:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "twc"))) THEN
  EXISTS_TAC `max Ccap Ctw` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `x:B`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP KNCL_KSOL_RIEM) THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas (p2b_kview (top,atlas) g) (&0))
                      (rfs_vmetric (p2b_kview (top,atlas) (g:real->B->real^3^3)) (&0))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
    FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      kncl_has `(g:real->B->real^3^3) t` th)) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "a" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* positive curvature *)
    MATCH_MP_TAC P2BC94_CANON_L_MONO_C THEN EXISTS_TAC `Ccap:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC KNCL_CASE_P THEN
    MAP_EVERY EXISTS_TAC [`K1:real`; `D:real`; `D1:real`; `D0:real`; `D01:real`;
                          `kappa0:real`; `C71:real`; `ec0:real`; `kappa:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `g':B->real^3^3`; `z:B`; `e:real^3->B`; `y:real^3`] THEN
    STRIP_TAC THEN USE_THEN "nscg" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `eps / K1`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    (* the cylinder models *)
    UNDISCH_TAC `p2b_cyl_model (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_cyl_model] THEN
    DISCH_THEN(X_CHOOSE_THEN `pp:real^3->B` (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC)) THENL
     [MATCH_MP_TAC KNCL_M1_CANON THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `pp:real^3->B`; `lam:real`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> MP_TAC(check (fun th -> is_forall(concl th) &&
        kncl_has `riemannian_metric atlas ((g:real->B->real^3^3) t)` th) th)) THEN MESON_TAC[];
      MATCH_MP_TAC P2BC94_CANON_L_MONO_C THEN EXISTS_TAC `Ctw:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "twc" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`pp:real^3->B`; `lam:real`] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> MP_TAC(check (fun th -> is_forall(concl th) &&
        kncl_has `riemannian_metric atlas ((g:real->B->real^3^3) t)` th) th)) THEN MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem of piece (d), with the cap constants of                  *)
(* P2BCC_KNCL_CAPC (pc_p2b_kncapc).                                          *)
(* ------------------------------------------------------------------------- *)

let KNCL_ROUTE = prove
 (`!w:B->bool. P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT w`,
  GEN_TAC THEN MATCH_MP_TAC KNCL_ROUTE_CAPC THEN REWRITE_TAC[P2BCC_KNCL_CAPC]);;

