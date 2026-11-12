(* ========================================================================= *)
(* Unit pc_p2b_canonv (Part 2B): the canonv parts of MT Cor 9.95 for         *)
(* histories (statements in pc_p2b_defs) and the route of                    *)
(* P2_COR_9_95_STATEMENT, which Part 3 uses.  The canonv form adds to the    *)
(* C-component alternative the volume clause Vol U > C^-1 R(x)^(-3/2) (as in *)
(* KL Def 69.1(c); MT Prop 17.1 needs it, since it uses kappa-noncollapsing  *)
(* without the positive-curvature exemption).                                *)
(* Headlines:                                                                *)
(*   P2BCV_CANON_MONO_C_V      |- !u. P2B_CANON_MONO_C_V_STATEMENT u         *)
(*   P2BCV_KSOL_NONCOMPACT_CANON (COR_9_94_L at L = 1)                       *)
(*   P2BCV_KSOL_COMPACT_CANON_V  (COR_9_94_L and the kappa0 of Prop 9.58)    *)
(*   P2BCV_COR_9_94_KSEP_V       (P2B_COR_9_94_V_FROM_PARTS)                  *)
(*   P2BCV_LIMIT_TRANSFER_V    |- !u w. P2B_LIMIT_TRANSFER_V_STATEMENT u w   *)
(*   P2BCV_COR_9_95            |- !u w. COR_9_94_L w /\ PROP_9_58 w          *)
(*                                  ==> P2_COR_9_95_STATEMENT u w            *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_p2b_kreq.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2b_scalpos.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p2b_979.ml";;
needs "src/pc_p2b_cscale.ml";;
needs "src/pc_p2b_cap.ml";;
needs "src/pc_p2b_slice.ml";;
needs "src/pc_p2a_flow.ml";;
needs "src/pc_p2a_l965.ml";;
needs "src/pc_p2b_ksolcyl.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_grg_dist.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_apx_event.ml";;
needs "src/pc_p3_iface.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Monotonicity in C, length-1 necks, the noncompact case.                   *)
(* ========================================================================= *)

(* P2BCV.C1 Monotonicity in C of the canonv form; length-1 evolving necks   *)
(* are strong necks; the noncompact case of Cor 9.94 from COR_9_94_L.       *)

let P2BCV_COMP_VOL_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C C' x t U.
     &0 < C /\ C <= C' /\ &0 <= rfs_vscalar V t x /\ p3_comp_vol V C x t U
     ==> p3_comp_vol V C' x t U`,
  REWRITE_TAC[p3_comp_vol] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `inv C * inv(sqrt(rfs_vscalar V t (x:A))) pow 3` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_POW_LE; REAL_LE_INV_EQ; SQRT_POS_LE]);;

let P2BCV_CANON_MONO_C_V = prove
 (`!u:A->bool. P2B_CANON_MONO_C_V_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2B_CANON_MONO_C_V_STATEMENT; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `C':real`; `eps:real`; `x:A`;
                       `t:real`] THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; p3_canonv_at; p3_strong_canonv] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN
   `!U Y. rfs_cap ((TM:real->A topology) t,AT t) (G t) C eps U Y /\ (x:A) IN Y
          ==> rfs_cap (TM t,AT t) (G t) C' eps U Y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_RFS_CAP_MONO_C THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U. (x:A) IN U /\ rfs_c_component ((TM:real->A topology) t,AT t) (G t) C U /\
        p3_comp_vol (TM,AT,G) C x t U
        ==> rfs_c_component (TM t,AT t) (G t) C' U /\ p3_comp_vol (TM,AT,G) C' x t U`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2B_RFS_C_COMPONENT_MONO_C THEN
      MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BCV_COMP_VOL_MONO THEN EXISTS_TAC `C:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[rfs_vscalar] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `(TM:real->A topology) t` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_c_component] o
        check (fun th -> can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "rfs_c_component")) (concl th) && not(is_forall(concl th)))) THEN
      DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1(CONJUNCT2 th)) THEN
        ASSUME_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let P2BCV_CANON_L1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t.
     p2b_canon_L V C eps (&1) x t ==> p3_canon_at V C eps x t`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `eps:real`; `x:A`; `t:real`] THEN
  REWRITE_TAC[p2b_canon_L; p3_canon_at; rfs_strong_canonical; rfs_strong_neck;
              rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  MESON_TAC[]);;

let P2BCV_KSOL_NONCOMPACT_CANON = prove
 (`!w:B->bool. P2B_COR_9_94_L_STATEMENT w ==> P2B_KSOL_NONCOMPACT_CANON_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_94_L_STATEMENT; P2B_KSOL_NONCOMPACT_CANON_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps2:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "c" (MP_TAC o SPECL [`eps:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C0:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BCV_CANON_L1 THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ========================================================================= *)
(* The volume clause of a kappa0-noncollapsed C-component.                   *)
(* ========================================================================= *)

(* P2BCV.C2 The volume clause of a C-component of a compact class solution  *)
(* that is kappa0-noncollapsed: at the radius r = (C0 R(x))^(-1/2) the       *)
(* curvature is at most r^-2 on the backward parabolic ball (abs Rm <=      *)
(* R(0)/2 <= S/2 <= C0 R(x) / 12 with S the sup of R(0) and R(x) >= 6 S/C0  *)
(* by the sectional lower bound of the C-component), so Vol B(x,r) >=       *)
(* kappa0 r^3, and the arithmetic gives Vol U > C1^-1 R(x)^(-3/2) with      *)
(* C1 = C0 + C0^2 / kappa0.                                                 *)

let P2BCV_COMP_VOL_ARITH = prove
 (`!kappa0 C0 R v.
     &0 < kappa0 /\ &1 < C0 /\ &0 < R /\ kappa0 * inv(sqrt(C0 * R)) pow 3 <= v
     ==> inv(C0 + C0 pow 2 * inv kappa0) * inv(sqrt R) pow 3 < v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C0 /\ &0 <= C0` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt C0 /\ &0 < sqrt R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt C0 <= C0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(C0 * R)) = inv(sqrt C0) * inv(sqrt R)` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_INV_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(C0 pow 2) <= inv(sqrt C0) pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt C0 pow 3 = C0 * sqrt C0` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 = 2 + 1`; REAL_POW_ADD; REAL_POW_1] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a = inv(sqrt C0)` THEN ABBREV_TAC `p = inv(sqrt R)` THEN
  SUBGOAL_THEN `&0 < p pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C0 pow 2 * inv kappa0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV; REAL_ARITH `&1 < C0 ==> &0 < C0`];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(C0 + C0 pow 2 * inv kappa0) < kappa0 * inv(C0 pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `kappa0 * inv(C0 pow 2) = inv(C0 pow 2 * inv kappa0)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `kappa0 * (a * p) pow 3` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(kappa0 * inv(C0 pow 2)) * p pow 3` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* P2BCV.C3 The volume clause of a C0-component of a compact class solution *)
(* that is kappa0-noncollapsed, with the constant C0 + C0^2 / kappa0.       *)

let P2BCV_COMP_VOL_KAPPA0 = prove
 (`!kappa0 C0 top atlas (g:real->B->real^3^3) x U.
     &0 < kappa0 /\ &1 < C0 /\ p2b_kappa_solution kappa0 (top,atlas) g /\
     compact_space top /\ x IN U /\ rfs_c_component (top,atlas) (g(&0)) C0 U
     ==> p3_comp_vol (p2b_kview (top,atlas) g) (C0 + C0 pow 2 * inv kappa0) x (&0) U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_c_component] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_c_component"
    with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "cc")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "sp") (CONJUNCTS_THEN2 (LABEL_TAC "inf") (K ALL_TAC))))))) THEN
  (* U is the whole space *)
  SUBGOAL_THEN `U = topspace (top:B topology)` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `connected_components_of (top:B topology) = {topspace top}` ASSUME_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "cc" (MP_TAC o REWRITE_RULE
      [ASSUME `connected_components_of (top:B topology) = {topspace top}`; IN_SING]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) (&0))` THEN
  ABBREV_TAC `S = sup(IMAGE (R:B->real) (topspace top))` THEN
  (* R bounded by S *)
  SUBGOAL_THEN `!y. y IN topspace top ==> (R:B->real) y <= S` ASSUME_TAC THENL
   [UNDISCH_TAC `!t. t <= &0 ==> ?K. !x. x IN topspace top
                                       ==> mfd_rm_norm atlas ((g:real->B->real^3^3) t) x <= K` THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
    MP_TAC(ISPEC `IMAGE (R:B->real) (topspace top)` SUP) THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [EXISTS_TAC `&6 * K` THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) (&0)`; `y:B`] P2AU_MFD_SCALAR_ABS_3) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:B` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `K:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* R(x) > 6 S / C0 *)
  SUBGOAL_THEN `&0 < (R:B->real) x /\ &6 * (inv C0 * S) < R x` STRIP_ASSUME_TAC THENL
   [USE_THEN "inf" (MP_TAC o REWRITE_RULE[rfs_inf_gt]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `x:B`; `d:real`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ANTS_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `x:B`] P2B_MFD_SCALAR_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sp" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the radius *)
  ABBREV_TAC `r = inv(sqrt(C0 * (R:B->real) x))` THEN
  SUBGOAL_THEN `&0 < C0 * (R:B->real) x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ inv(r pow 2) = C0 * (R:B->real) x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT; REAL_POW_INV; REAL_INV_INV;
                                     SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the curvature bound on the parabolic ball *)
  SUBGOAL_THEN `!s y. s <= &0 /\ y IN topspace top
                      ==> mfd_rm_norm atlas ((g:real->B->real^3^3) s) y <= C0 * (R:B->real) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`UNIV:B->bool`; `kappa0:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                   `s:real`; `y:B`] P2AL65_KSOL_RM_LE0) THEN
    ASM_REWRITE_TAC[P2BKC_KSOL_DRDT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:B` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `S:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&6 * S < C0 * (R:B->real) x` ASSUME_TAC THENL
     [SUBGOAL_THEN `&6 * S = C0 * (&6 * (inv C0 * S))` SUBST1_TAC THENL
       [SUBGOAL_THEN `C0 * inv C0 = &1` MP_TAC THENL
         [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_RING;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* kappa0-noncollapsing at (x,0) at radius r *)
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
    try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) =
        "rfs_kappa_noncollapsed" with Failure _ -> false)) THEN
  REWRITE_TAC[rfs_flow_view; rfs_kappa_noncollapsed] THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `x:B`; `r:real`]) THEN
  REWRITE_TAC[rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `zb:B`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(zb:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) x r` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  (* the volume of U = M *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `topspace top:B->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  SUBGOAL_THEN `v <= w` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `(g:real->B->real^3^3) (&0)`;
                          `mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) x r`;
                          `topspace top:B->bool`; `v:real`; `w:real`] MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  REWRITE_TAC[p3_comp_vol; p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric;
              rfs_vscalar; IN_ELIM_THM; REAL_LE_REFL] THEN
  EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BCV_COMP_VOL_ARITH THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "r" THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The compact case and COR_9_94_KSEP_V.                                     *)
(* ========================================================================= *)

(* P2BCV.C4 From the plain form to the canonv form with a larger constant,  *)
(* the C-component case supplied separately; a round compact slice of a     *)
(* class solution is an eps-round component; the compact case of Cor 9.94   *)
(* in canonv form.                                                           *)

let P2BCV_CANON_TO_CANONV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C C1 eps x t.
     &1 < C /\ C <= C1 /\ p3_canon_at V C eps x t /\
     (!U. x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U
          ==> p3_canonv_at V C1 eps x t)
     ==> p3_canonv_at V C1 eps x t`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `C1:real`; `eps:real`; `x:A`;
                       `t:real`] THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; p3_canon_at; rfs_strong_canonical] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `U:A->bool`) (LABEL_TAC "cc")))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC))) THENL
   [REWRITE_TAC[p3_canonv_at; p3_strong_canonv; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p3_canonv_at; p3_strong_canonv; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN DISJ1_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B_RFS_CAP_MONO_C THEN MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "cc" MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p3_canonv_at; p3_strong_canonv; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]]);;

let P2BCV_ROUND_COMPONENT = prove
 (`!kappa top atlas (g:real->B->real^3^3) eps.
     p2b_kappa_solution kappa (top,atlas) g /\ compact_space top /\ &0 < eps /\
     p2b_round (top,atlas) (g(&0))
     ==> rfs_round_component (top,atlas) (g(&0)) eps (topspace top)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  UNDISCH_TAC `p2b_round (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
  REWRITE_TAC[p2b_round] THEN DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[rfs_round_component] THEN ASM_REWRITE_TAC[GSYM compact_space] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `connected_components_of (top:B topology) = {topspace top}` SUBST1_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real`; `\y:B. k %% (g:real->B->real^3^3) (&0) y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `k:real`; `x:B`; `u:real^3`; `v:real^3`]
                  RFA_MFD_SECTIONAL_CMUL) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ];
    REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `&0` THEN
    ASM_SIMP_TAC[REAL_POW_LT; P2BL_LCK_DIST2_REFL; REAL_LE_REFL]]);;

(* P2BCV.C5 The compact case of Cor 9.94 in canonv form, from COR_9_94_L   *)
(* (at L = 1, constant C0) and the universal kappa0 of Prop 9.58: necks,   *)
(* caps and round components pass unchanged (caps with the larger          *)
(* constant); a C0-component is an eps-round component when g(0) is round, *)
(* else a (C0 + C0^2/kappa0)-component with the volume clause.             *)

let P2BCV_KSOL_COMPACT_CANON_V = prove
 (`!w:B->bool. P2B_COR_9_94_L_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w
               ==> P2B_KSOL_COMPACT_CANON_V_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_94_L_STATEMENT; P2B_PROP_9_58_STATEMENT;
                           P2B_KSOL_COMPACT_CANON_V_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `epsp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")))
    (X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k0")))) THEN
  EXISTS_TAC `epsp:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "c" (MP_TAC o SPECL [`eps:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))) THEN
  SUBGOAL_THEN `&0 < C0 pow 2 * inv kappa0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV; REAL_ARITH `&1 < C0 ==> &0 < C0`];
    ALL_TAC] THEN
  EXISTS_TAC `C0 + C0 pow 2 * inv kappa0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `x:B`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC P2BCV_CANON_TO_CANONV THEN EXISTS_TAC `C0:real` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2BCV_CANON_L1 THEN USE_THEN "c0" MATCH_MP_TAC THEN
    EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `U:B->bool` THEN REWRITE_TAC[P2B_KVIEW_SLICE0] THEN STRIP_TAC THEN
    ASM_CASES_TAC `p2b_round (top,atlas) ((g:real->B->real^3^3) (&0))` THENL
     [REWRITE_TAC[p3_canonv_at; p3_strong_canonv; P2B_KVIEW_SLICE0] THEN
      EXISTS_TAC `topspace top:B->bool` THEN REPEAT DISJ2_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BCV_ROUND_COMPONENT THEN
      EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
      USE_THEN "k0" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                     `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:real->B->real^3^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      REWRITE_TAC[p3_canonv_at; p3_strong_canonv; P2B_KVIEW_SLICE0] THEN
      EXISTS_TAC `U:B->bool` THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2B_RFS_C_COMPONENT_MONO_C THEN
        MAP_EVERY EXISTS_TAC [`C0:real`; `x:B`] THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[P2B_KSOL_SLICE0]];
        MATCH_MP_TAC P2BCV_COMP_VOL_KAPPA0 THEN ASM_REWRITE_TAC[]]]]);;

let P2BCV_COR_9_94_KSEP_V = prove
 (`!w:B->bool. P2B_COR_9_94_L_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w
               ==> P2B_COR_9_94_KSEP_V_STATEMENT w`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2B_COR_9_94_V_FROM_PARTS THEN
  ASM_SIMP_TAC[P2BCV_KSOL_NONCOMPACT_CANON; P2BCV_KSOL_COMPACT_CANON_V; P2BCV_CANON_MONO_C_V]);;

(* ========================================================================= *)
(* The C-component case of the canonv transfer.                              *)
(* ========================================================================= *)

(* P2BCV.C6 Arithmetic of the volume transfer: with sqrt R(x_n) >= s r q    *)
(* (s^2 = 1 - d, r = sqrt R, q = sqrt Q) and Vol(U, g(0)) <= (q/s)^3        *)
(* Vol(U_n), the strict inequality Vol U > C^-1 R^(-3/2) of the limit, kept *)
(* with the margin 1 - 4d, passes to U_n.                                   *)

let P2BCV_VOL_CORE_ARITH = prove
 (`!C r q s z v0 vn d.
     &0 < C /\ &0 < r /\ &0 < q /\ &0 < s /\ &0 <= d /\ d <= &1 / &8 /\
     s pow 2 = &1 - d /\
     inv C * inv r pow 3 < v0 * (&1 - &4 * d) /\ s * r * q <= z /\
     v0 <= (q pow 3 / s pow 3) * vn
     ==> inv C * inv z pow 3 < vn`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s * r * q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv C /\ &0 < inv r pow 3 /\ &0 < inv s pow 3 * inv q pow 3`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT; REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < v0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 * (&1 - &4 * d) < v0 * (&1 - &4 * d)` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `inv C * inv r pow 3` THEN ASM_SIMP_TAC[REAL_LT_MUL];
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_ARITH `d <= &1 / &8 ==> &0 < &1 - &4 * d`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - &4 * d <= s pow 6` ASSUME_TAC THENL
   [SUBGOAL_THEN `s pow 6 = (&1 - d) pow 3` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `6 = 2 * 3`; GSYM REAL_POW_POW] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `d pow 2 <= d` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= d * (&1 + &3 * d - d pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - d) pow 3 = (&1 - &4 * d) + d * (&1 + &3 * d - d pow 2)`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv z pow 3 <= inv s pow 3 * inv r pow 3 * inv q pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `v0 * s pow 3 * inv q pow 3 <= vn` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < s pow 3 * inv q pow 3` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_LT_INV]; ALL_TAC] THEN
    SUBGOAL_THEN `vn = ((q pow 3 / s pow 3) * vn) * (s pow 3 * inv q pow 3)` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(s pow 3 = &0) /\ ~(q pow 3 = &0)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(inv C * inv r pow 3) * (inv s pow 3 * inv q pow 3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv C * (inv s pow 3 * inv r pow 3 * inv q pow 3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `(v0 * (&1 - &4 * d)) * (inv s pow 3 * inv q pow 3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v0 * s pow 3 * inv q pow 3` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `v0 * s pow 3 * inv q pow 3 = (v0 * s pow 6) * (inv s pow 3 * inv q pow 3)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(s = &0)` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* P2BCV.C7 A C-component of the limit with the volume clause gives, along  *)
(* the sequence, C-components with the volume clause: P2BL_CCOMP_LIMIT's    *)
(* argument (P2BL_STATIC_DATA at the scale R0 = R(xl) and the openness     *)
(* "D") with a smaller closeness delta1, the pullback quadratic forms       *)
(* within d of g(0) (P2B9S_PB_QF), Vol(U) <= (Q/(1-d))^(3/2) Vol(U_n)       *)
(* (P2BC_VOLUME_PB_COMPARE), R_n(x_n) >= (1-d) R0 Q (P2B9S_CCOMP_TARGET_    *)
(* POINT) and P2BCV_VOL_CORE_ARITH.                                          *)

let P2BCV_VSCALAR = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     rfs_vscalar V t x = mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) x`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric]);;

let P2BCV_D_CHOICE = prove
 (`!a v0. &0 < a /\ a < v0
          ==> &0 < (&1 - a / v0) / &8 /\ (&1 - a / v0) / &8 <= &1 / &8 /\
              a < v0 * (&1 - &4 * ((&1 - a / v0) / &8))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < v0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a / v0 /\ a / v0 < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  SUBGOAL_THEN `v0 * (&1 - &4 * ((&1 - a / v0) / &8)) = (v0 + a) / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < v0` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]);;

(* P2BCV.C8 One step of the volume transfer: a diffeomorphism psi of U onto *)
(* a compact set of a stage, with the pullback of Qn gn C^k-close to g0 at  *)
(* the scale R0 = R(xl) (closeness delta1 <= d, eta, 1/4), gives            *)
(* Vol(psi U, gn) > C^-1 R_n(psi xl)^(-3/2) from Vol(U, g0) = v0 and the    *)
(* margin v0 (1 - 4d).                                                       *)

let P2BCV_VOL_STEP = prove
 (`!top atlas (g0:B->real^3^3) top' atlas' (gn:A->real^3^3) U psi psi' C R0 Qn K0 d eta
    delta1 dd v0 xl.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     hausdorff_space top' /\ riemannian_metric atlas g0 /\ riemannian_metric atlas' gn /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
     compact_in top' (IMAGE psi U) /\ xl IN U /\
     &1 < C /\ &0 < R0 /\ mfd_scalar atlas g0 xl = R0 /\ &0 < Qn /\
     &0 < d /\ d <= &1 / &8 /\ inv C * inv(sqrt R0) pow 3 < v0 * (&1 - &4 * d) /\
     mfd_has_volume (top,atlas) g0 U v0 /\
     (!s (G0:real^3->real^3^3) G y.
         metric_field s G0 /\ metric_field s G /\ y IN s /\
         lrm_deriv_norm2 0 G0 y <= K0 /\ lrm_deriv_norm2 1 G0 y <= K0 /\
         lrm_deriv_norm2 2 G0 y <= K0 /\ lck_dist2 4 G0 G y < eta pow 2
         ==> abs(lscalar G y - lscalar G0 y) <= d /\
             (!u v. ~collinear {vec 0,u,v}
                    ==> abs(lsectional G y u v - lsectional G0 y u v) <= d) /\
             abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= d /\
             abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= d /\
             abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= d) /\
     rfa_rmd2 0 atlas (\z. R0 %% g0 z) xl <= K0 /\ rfa_rmd2 1 atlas (\z. R0 %% g0 z) xl <= K0 /\
     rfa_rmd2 2 atlas (\z. R0 %% g0 z) xl <= K0 /\
     &0 < delta1 /\ delta1 <= eta /\ delta1 <= &1 / &4 /\ delta1 <= d /\ dd < delta1 pow 2 /\
     (!y. y IN U
          ==> lck_dist2 (rfs_kreg delta1) (metric_local atlas (chart_at atlas y) (\z. R0 %% g0 z))
                (metric_local atlas (chart_at atlas y)
                   (\z. R0 %% mfd_pullback_metric atlas atlas' psi (\w. Qn %% gn w) z))
                (SND(chart_at atlas y) y) <= dd)
     ==> ?vn. mfd_has_volume (top',atlas') gn (IMAGE psi U) vn /\
              inv C * inv(sqrt(mfd_scalar atlas' gn (psi xl))) pow 3 < vn`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "stab")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lck")))))))))))))))))))))))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas' (\w. Qn %% (gn:A->real^3^3) w)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(psi:B->A) xl IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':A topology`; `IMAGE (psi:B->A) U`] COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `(a:A) IN s ==> s SUBSET t ==> a IN t`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the scalar curvature at psi xl *)
  SUBGOAL_THEN `(&1 - d) * R0 * Qn <= mfd_scalar atlas' (gn:A->real^3^3) ((psi:B->A) (xl:B))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                   `\w. Qn %% (gn:A->real^3^3) w`; `U:B->bool`; `IMAGE (psi:B->A) U`;
                   `psi:B->A`; `psi':A->B`; `R0:real`; `K0:real`; `d:real`; `eta:real`;
                   `dd:real`; `delta1:real`; `xl:B`] P2B9S_CCOMP_TARGET_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "lck" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                   `gn:A->real^3^3`; `Qn:real`; `(psi:B->A) xl`] P2BCS_SCALAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_ABS_BOUNDS; REAL_LE_SUB_RADD; REAL_LE_LDIV_EQ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(&1 - d) * R0 * Qn = (R0 - d * R0) * Qn` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(mfd_scalar atlas' (gn:A->real^3^3) ((psi:B->A) (xl:B)) / Qn) * Qn` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the quadratic forms on U *)
  SUBGOAL_THEN
   `!y w. y IN U
          ==> w dot ((g0:B->real^3^3) y ** w) <=
              (Qn / (&1 - d)) *
              (w dot (mfd_pullback_metric atlas atlas' (psi:B->A) (gn:A->real^3^3) y ** w))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                   `\w. Qn %% (gn:A->real^3^3) w`; `U:B->bool`; `IMAGE (psi:B->A) U`;
                   `psi:B->A`; `psi':A->B`; `R0:real`; `rfs_kreg delta1`; `dd:real`; `y:B`]
                  P2B9S_PB_QF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "lck" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
    REWRITE_TAC[P2B9_PULLBACK_METRIC_CMUL; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    ABBREV_TAC `a = w dot (mfd_pullback_metric atlas atlas' (psi:B->A) (gn:A->real^3^3) y ** w)` THEN
    ABBREV_TAC `b = w dot ((g0:B->real^3^3) y ** w)` THEN
    SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN ASM_CASES_TAC `w:real^3 = vec 0` THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN
        REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                     `y:B`] RIEMANNIAN_METRIC_POS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o
                    GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
          try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_diffeo"
          with Failure _ -> false)) THEN
        ASM SET_TAC[];
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt dd <= d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta1 pow 2` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt dd * b <= d * b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - d) * b <= Qn * a` ASSUME_TAC THENL
     [UNDISCH_TAC `abs(Qn * a - b) <= sqrt dd * b` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Qn / (&1 - d)) * a = (Qn * a) / (&1 - d)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the volumes *)
  MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `gn:A->real^3^3`;
                 `IMAGE (psi:B->A) U`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vn:real`) THEN
  EXISTS_TAC `vn:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &1 - d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `gn:A->real^3^3`;
                 `U:B->bool`; `IMAGE (psi:B->A) U`; `psi:B->A`; `psi':A->B`; `U:B->bool`;
                 `v0:real`; `vn:real`; `Qn / (&1 - d)`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  (* the arithmetic *)
  MATCH_MP_TAC P2BCV_VOL_CORE_ARITH THEN
  MAP_EVERY EXISTS_TAC [`sqrt R0`; `sqrt Qn`; `sqrt(&1 - d)`; `v0:real`; `d:real`] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; REAL_ARITH `&1 < C ==> &0 < C`] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LT_IMP_LE; REAL_LE_MUL] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `vn:real`)) (concl th) &&
    can (find_term (fun t -> t = `v0:real`)) (concl th) && not(is_forall(concl th)))) THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> v0 <= a ==> v0 <= b`) THEN
  SUBGOAL_THEN `sqrt(Qn / (&1 - d)) = sqrt Qn / sqrt(&1 - d)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt Qn /\ &0 < sqrt(&1 - d)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `Qn = sqrt Qn pow 2 /\ &1 - d = sqrt(&1 - d) pow 2` MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [CONJUNCT1 th] THEN
                       GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [CONJUNCT2 th]) THEN
  UNDISCH_TAC `&0 < sqrt(&1 - d)` THEN CONV_TAC REAL_FIELD);;

(* P2BCV.C9 The C-component case of the canonv transfer.                    *)

let P2BCV_CCOMP_LIMIT_V = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl kappa C U.
     p2bl_vslices V x t /\
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl) /\
     p2b_kappa_solution kappa (top,atlas) g /\
     rfs_c_component (top,atlas) (g (&0)) C U /\ xl IN U /\ &1 < C /\
     p3_comp_vol (p2b_kview (top,atlas) g) C xl (&0) U /\
     (?delta. &0 < delta /\
        !top' atlas' (g':A->real^3^3) psi psi'.
           smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
           mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
           IMAGE psi U IN connected_components_of top' /\
           rfs_mclose (rfs_kreg delta) delta atlas U
             (\y. mfd_scalar atlas (g (&0)) xl %% g (&0) y)
             (\y. mfd_scalar atlas (g (&0)) xl %% mfd_pullback_metric atlas atlas' psi g' y)
           ==> rfs_c_component (top',atlas') g' C (IMAGE psi U))
     ==> ?N. !n. N <= n
                 ==> ?U'. x n IN U' /\
                          rfs_c_component (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                                          (rfs_vmetric (V n) (t n)) C U' /\
                          p3_comp_vol (V n) C (x n) (t n) U'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cv")
      (X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))))))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BL_VSLICES_SLICES) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `C:real`; `U:B->bool`; `xl:B`]
                P2B_C_COMPONENT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) IN connected_components_of top /\ compact_in top U /\
                open_in top U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_c_component (top,atlas) ((g:real->B->real^3^3) (&0)) C U` THEN
    REWRITE_TAC[rfs_c_component] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
    EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the limit volume and the margin *)
  USE_THEN "cv" (MP_TAC o REWRITE_RULE[p3_comp_vol; p2b_kview; rfs_flow_view; rfs_vtop;
                                       rfs_vatlas; rfs_vmetric; rfs_vscalar; IN_ELIM_THM;
                                       REAL_LE_REFL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R0 = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` THEN
  MP_TAC(SPECL [`inv C * inv(sqrt R0) pow 3`; `v0:real`] P2BCV_D_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT; SQRT_POS_LT; REAL_ARITH `&1 < C ==> &0 < C`];
    ALL_TAC] THEN
  ABBREV_TAC `d = (&1 - (inv C * inv(sqrt R0) pow 3) / v0) / &8` THEN STRIP_TAC THEN
  (* the curvature constants at xl *)
  ABBREV_TAC `K0 = abs(rfa_rmd2 0 atlas (\z. R0 %% (g:real->B->real^3^3) (&0) z) xl) +
                   abs(rfa_rmd2 1 atlas (\z. R0 %% g (&0) z) xl) +
                   abs(rfa_rmd2 2 atlas (\z. R0 %% g (&0) z) xl)` THEN
  SUBGOAL_THEN
   `rfa_rmd2 0 atlas (\z. R0 %% (g:real->B->real^3^3) (&0) z) xl <= K0 /\
    rfa_rmd2 1 atlas (\z. R0 %% g (&0) z) xl <= K0 /\
    rfa_rmd2 2 atlas (\z. R0 %% g (&0) z) xl <= K0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "K0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`K0:real`; `d:real`] (MATCH_MP P2B9S_LRG_D P2B_REQ_LRG_DERIV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))) THEN
  ABBREV_TAC `delta1 = min (min delta (&1 / &4)) (min eta d)` THEN
  SUBGOAL_THEN `&0 < delta1 /\ delta1 <= delta /\ delta1 <= &1 / &4 /\ delta1 <= eta /\
                delta1 <= d`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "delta1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `U:B->bool`; `U:B->bool`;
                 `delta1:real`; `R0:real`]
                P2BL_STATIC_DATA) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_mclose")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) (LABEL_TAC "mc")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `n:num`; `(Q:num->real) n`] P2BL_VSLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE ((phi:num->B->A) n) U IN
                connected_components_of (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_COMPONENT_IMAGE) THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the C-component, from the openness with delta1 <= delta *)
  SUBGOAL_THEN
   `rfs_c_component (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n),
                     rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) C
                    (IMAGE ((phi:num->B->A) n) U)`
  ASSUME_TAC THENL
   [USE_THEN "D" (MP_TAC o SPECL
     [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
      `\z. (Q:num->real) n %% rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) z`;
      `(phi:num->B->A) n`; `psi:A->B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL
       [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (&0)`;
        `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
        `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
        `\z. (Q:num->real) n %% rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) z`;
        `U:B->bool`; `IMAGE ((phi:num->B->A) n) U`; `(phi:num->B->A) n`; `psi:A->B`;
        `R0:real`; `delta1:real`; `delta:real`] P2BS_MCLOSE_MONO) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                   `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                   `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                   `C:real`; `IMAGE ((phi:num->B->A) n) U`; `(Q:num->real) n`]
                  P2BCS_CCOMP_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE ((phi:num->B->A) n) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(x:num->A) n = (phi:num->B->A) n xl` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the volume clause *)
  USE_THEN "mc" (MP_TAC o REWRITE_RULE[rfs_mclose]) THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lck"))) THEN
  REWRITE_TAC[p3_comp_vol; P2BCV_VSCALAR] THEN
  SUBGOAL_THEN `(x:num->A) n = (phi:num->B->A) n xl` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BCV_VOL_STEP THEN
  MAP_EVERY EXISTS_TAC
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (&0)`;
    `psi:A->B`; `R0:real`; `(Q:num->real) n`; `K0:real`; `d:real`; `eta:real`;
    `delta1:real`; `dd:real`; `v0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `rfs_c_component (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n),
                     rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) C
                    (IMAGE ((phi:num->B->A) n) U)` THEN
  REWRITE_TAC[rfs_c_component] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The canonv transfer and the route of Cor 9.95.                            *)
(* ========================================================================= *)

(* P2BCV.C10 The transfer in canonv form: the plain argument of           *)
(* P2BL_LIMIT_TRANSFER_FROM_PARTS (text copied from pc_p2b_ltr and adapted: *)
(* the canonv alternatives, the C-component case through                    *)
(* P2BCV_CCOMP_LIMIT_V with the volume clause).                             *)

let P2BCV_CANONV_AT_PARTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) C eps x t.
     (?e. rfs_strong_neck V eps x t e) \/
     (?U Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps U Y /\ x IN Y) \/
     (?U. x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U /\
          p3_comp_vol V C x t U) \/
     (?U. x IN U /\
          rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)
     ==> p3_canonv_at V C eps x t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p3_canonv_at; p3_strong_canonv] THEN
  ASM_MESON_TAC[]);;

let P2BCV_LIMIT_TRANSFER_V_FROM_PARTS = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_PROP_9_79_OPEN_TYPED_STATEMENT w u /\ P2B_NECK_OPEN_STATEMENT w u /\
     P2B_KSOL_NECK_EXTEND_Q_STATEMENT w
     ==> P2B_LIMIT_TRANSFER_V_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED_STATEMENT; P2B_NECK_OPEN_STATEMENT;
              P2B_KSOL_NECK_EXTEND_Q_STATEMENT; P2B_LIMIT_TRANSFER_V_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps0c:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TC"))))
      (CONJUNCTS_THEN2 (LABEL_TAC "TCC") (LABEL_TAC "TR"))))
    (CONJUNCTS_THEN2 (LABEL_TAC "NO") (LABEL_TAC "NE"))) THEN
  EXISTS_TAC `min eps0c (&1 / &40)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:num->(A)rfs_history`; `x:num->A`;
                       `t:num->real`; `Q:num->real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `xl:B`; `kappa:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `p2bl_vslices (\n. rfs_view ((hs:num->(A)rfs_history) n)) x t` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_HIST_VSLICES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SIMP_RULE[P2BL_KVIEW_ACCESS; REAL_LE_REFL] o
    REWRITE_RULE[p3_strong_canonv] o REWRITE_RULE[p3_canonv_at] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p3_canonv_at"
                     with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->bool` (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC)) THENL
   [(* strong neck *)
    REMOVE_THEN "NE" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                      `atlas:((B->bool)#(B->real^3))->bool`;
                                      `g:real->B->real^3^3`; `eps:real`; `xl:B`;
                                      `e:real^3->B`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `eps:real`; `a:real`; `e:real^3->B`;
                   `\(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t':real) (z:A).
                      ?e'. rfs_strong_neck V' eps z t' (e':real^3->A)`] P2BL_NECK_LIMIT) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "NO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BCV_CANONV_AT_PARTS THEN ASM_REWRITE_TAC[];
    (* cap *)
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`]
                  P2BL_CAP_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BL_CAP_CLOSURE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                            `(g:real->B->real^3^3) (&0)`; `C:real`; `eps:real`;
                            `Y:B->bool`; `xl:B`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BCV_CANONV_AT_PARTS THEN ASM_REWRITE_TAC[];
    (* C-component *)
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `C:real`; `U:B->bool`] P2BCV_CCOMP_LIMIT_V) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TCC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BCV_CANONV_AT_PARTS THEN ASM_REWRITE_TAC[];
    (* round component *)
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `eps:real`; `U:B->bool`] P2BL_ROUND_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC P2BL_ROUND_SCALAR_POS THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `eps:real`; `U:B->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BCV_CANONV_AT_PARTS THEN ASM_REWRITE_TAC[]]);;

let P2BCV_LIMIT_TRANSFER_V = prove
 (`!(u:A->bool) (w:B->bool). P2B_LIMIT_TRANSFER_V_STATEMENT u w`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2BCV_LIMIT_TRANSFER_V_FROM_PARTS THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED; P2B_NECK_OPEN; P2B_KSOL_NECK_EXTEND_Q]);;

(* P2BCV.C11 MT Cor 9.95 in canonv form for histories (used in Part 3) from  *)
(* COR_9_94_L and Prop 9.58, through P2B_COR_9_95_FROM_PARTS.                *)

let P2BCV_COR_9_95 = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_COR_9_94_L_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w ==> P2_COR_9_95_STATEMENT u w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2B_COR_9_95_FROM_PARTS THEN
  ASM_SIMP_TAC[P2BCV_COR_9_94_KSEP_V; P2BCV_CANON_MONO_C_V; P2BCV_LIMIT_TRANSFER_V;
               P2B_SEP_LIMIT; P2B_LORIENT_LIMIT]);;

