(* ========================================================================= *)
(* Unit pc_p2b_p946: MT Prop 9.46 in route form,                             *)
(* P2BX2_P946_ROUTE |- !w:B->bool. P2B_PROP_9_46_ROUTE_STATEMENT w.          *)
(* The parts:                                                                *)
(*   pc_p2b_p946s  soliton calculus, Hamilton identity, f proper;            *)
(*   pc_p2b_p946f  flows of vector fields with an escape function;           *)
(*   pc_p2b_p946g  the soliton flow G and the hypotheses of X2s for it;      *)
(*   pc_p2b_p946c  Claim 9.51 (the limit at infinity has R = 1);             *)
(*   pc_p2b_p946h  far level sets: the contradiction with area < 8 pi;       *)
(*   pc_p2b_p946i  necks and level spheres of area about 8 pi.               *)
(* ========================================================================= *)

needs "src/pc_p2b_p946i.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The standing hypotheses p2bx46_hyp of the parts, and the                  *)
(* bounds 0 < R <= 6 K, from the hypotheses of P2B_PROP_9_46_STATEMENT.     *)
(* ========================================================================= *)

let P2BX46_946_HYP = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ &0 <= K /\
     (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= K) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v)
     ==> p2bx46_hyp top atlas g f K /\
         (!x. x IN topspace top
              ==> &0 < mfd_scalar atlas g x /\ mfd_scalar atlas g x <= &6 * K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> &0 < mfd_scalar atlas (g:A->real^3^3) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y w. y IN topspace top
          ==> abs(mfd_ricci atlas (g:A->real^3^3) y w w) <= &2 * K * (w dot (g y ** w))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `w:real^3`] P2AP_MFD_RICCI_ABS) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `w:real^3`] P2AP_QFORM_NONNEG) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * mfd_rm_norm atlas (g:A->real^3^3) y * (w dot (g y ** w))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bx46_hyp; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `w:real^3 = vec 0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `w:real^3`] o check (fun th ->
        can (find_term (fun t -> t = `abs:real->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[DOT_LZERO; REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P2BX46_MFD_RIC_POS THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(mfd_ricci atlas (g:A->real^3^3) y w w)` THEN
    ASM_SIMP_TAC[REAL_ABS_LE];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`] P2AU_MFD_SCALAR_ABS_3) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_rm_norm atlas (g:A->real^3^3) x <= K` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The assembly (MT pp. 209-216).  With K1 = max K 0:                        *)
(* p2bx46_hyp, Hamilton's identity R + |grad f|^2 - f = C, f proper and the *)
(* bound |2 Ric(grad f, w)| <= C1 |w|.  Points pp at infinity with          *)
(* R(pp k) -> L = limsup of R at infinity (P2BX46_SOL_POINTS).  X2s for the  *)
(* flow p2bx46_Gl (1/2) and Claim 9.51 give L = 1; X2s for the soliton flow  *)
(* p2bx46_G gives the cylinder limit at the points pp, hence necks at       *)
(* arbitrarily large f (P2BX46_FAR_NECKS), hence level spheres of area at   *)
(* most 8 pi + delta (P2BX46_I_OUTPUT), against P2BX46_FAR_SPHERES_CONTRA.  *)
(* The hypothesis P2B_REQ_RFA_HARNACK_STATEMENT of the route is not needed: *)
(* dR/dt >= 0 along the soliton flows follows from (9.21) (pc_p2b_p946g).   *)
(* ========================================================================= *)

let P2BX46_P946_MAIN = prove
 (`!w:A->bool. P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT w ==> P2B_PROP_9_46_STATEMENT w`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "x2s") THEN REWRITE_TAC[P2B_PROP_9_46_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `f:A->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?K1. &0 <= K1 /\ !x. x IN topspace top ==> mfd_rm_norm atlas (g:A->real^3^3) x <= K1`
  (X_CHOOSE_THEN `K1:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `max K (&0)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `a <= K ==> a <= max K (&0)`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K1:real`] P2BX46_946_HYP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`] P2BX46_MFD_HAMILTON_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "ham"))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K1:real`] P2BX46_F_PROPER) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `p2bx46_hyp top atlas (g:A->real^3^3) f K1` THEN
    REWRITE_TAC[p2bx46_hyp] THEN MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K1:real`; `K1:real`] P2BX46_RIC_GRADF_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC)] THEN
  (* the points at infinity *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K1:real`; `&6 * K1`] P2BX46_SOL_POINTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:num->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `((\k. mfd_scalar atlas (g:A->real^3^3) (pp k)) ---> L) sequentially /\
    (!e. &0 < e
         ==> ?S. compact_in top S /\
                 !x. x IN topspace top /\ ~(x IN S) ==> mfd_scalar atlas g x <= L + e)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!x. x IN topspace top
          ==> mfd_scalar atlas (p2bx46_G top atlas (g:A->real^3^3) f (--(&1))) x =
              mfd_scalar atlas g x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_SOL_SCALAR_M1 THEN
      EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\k. mfd_scalar atlas (g:A->real^3^3) ((pp:num->A) k)) =
        (\k. mfd_scalar atlas (p2bx46_G top atlas g f (--(&1))) (pp k))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!e. &0 < e
            ==> ?S. compact_in top S /\
                    !x. x IN topspace top /\ ~(x IN S)
                        ==> mfd_scalar atlas (p2bx46_G top atlas (g:A->real^3^3) f (--(&1))) x
                            <= L + e` THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* Claim 9.51: L = 1 *)
  SUBGOAL_THEN `L = &1` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `f:A->real`; `K1:real`; `inv(&2)`; `K1:real`]
      P2BX46_GL_X2S_HYPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `f:A->real`; `K1:real`; `inv(&2)`; `pp:num->A`; `L:real`]
      P2BX46_GL_POINTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
    USE_THEN "x2s" (MP_TAC o REWRITE_RULE[P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL
      [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
       `p2bx46_Gl top atlas (g:A->real^3^3) f (inv(&2))`; `K1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `pp:num->A`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':A topology`
      (X_CHOOSE_THEN `atlas':((A->bool)#(A->real^3))->bool`
        (X_CHOOSE_THEN `g':real->A->real^3^3` (X_CHOOSE_THEN `xl:A`
          (X_CHOOSE_THEN `W:num->A->bool` (X_CHOOSE_THEN `phi:num->A->A`
            STRIP_ASSUME_TAC))))))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `K1:real`; `pp:num->A`; `L:real`; `sub:num->num`;
                   `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                   `g':real->A->real^3^3`; `xl:A`; `W:num->A->bool`; `phi:num->A->A`]
      P2BX46_CLAIM_951) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  (* X2s for the soliton flow at the points pp: necks far out *)
  MP_TAC(ISPECL [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real`; `K1:real`; `K1:real`] P2BX46_SOL_X2S_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "x2s" (MP_TAC o REWRITE_RULE[P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `p2bx46_G top atlas (g:A->real^3^3) f`; `K1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `pp:num->A`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':A topology`
    (X_CHOOSE_THEN `atlas':((A->bool)#(A->real^3))->bool`
      (X_CHOOSE_THEN `g':real->A->real^3^3` (X_CHOOSE_THEN `xl:A`
        (X_CHOOSE_THEN `W:num->A->bool` (X_CHOOSE_THEN `phi:num->A->A`
          STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K1:real`; `pp:num->A`; `sub:num->num`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                 `g':real->A->real^3^3`; `xl:A`; `W:num->A->bool`; `phi:num->A->A`]
    P2BX46_FAR_NECKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* level spheres of area about 8 pi far out *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K1:real`; `C:real`; `&6 * K1`; `C1:real`] P2BX46_I_OUTPUT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[p2bx46_ngrad] THEN
    USE_THEN "ham" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(p:A) IN topspace top`))) THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K1:real`; `C:real`; `&6 * K1`] P2BX46_FAR_SPHERES_CONTRA) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

(* The route: P2B_REQ_RFA_HARNACK_STATEMENT is not used. *)

let P2BX2_P946_ROUTE = prove
 (`!w:B->bool. P2B_PROP_9_46_ROUTE_STATEMENT w`,
  REWRITE_TAC[P2B_PROP_9_46_ROUTE_STATEMENT] THEN MESON_TAC[P2BX46_P946_MAIN]);;

