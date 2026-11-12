(* ========================================================================= *)
(* pc_p2b_t911 (Part 2B): the route of MT Thm 9.11 without the             *)
(* classification (MT pp. 185-188, 198-203):                                *)
(*   P2B_THM_9_11_ROUTE |- !w. P2B_THM_9_11_ROUTE_STATEMENT w               *)
(* (pc_p2b_chainstmts), from FL4, Cor 9.10, Prop 9.20, the leaf            *)
(* SOLITON_FROM_LINF, KSOL_DRDT, ANCIENT_COMPACT and P2C_PROP_5_14; the    *)
(* core P2B11_THM_9_11_CORE takes the corrected leaf                         *)
(* P2B_SOLITON_FROM_LINF_FIX, as does the route statement (the original leaf *)
(* implies it, P2B_SOLITON_FROM_LINF_ORIG_IMP_FIX).                          *)
(*                                                                           *)
(*  T1 tau k = k + 1, q k with l(q k, tau k) <= 3/2 (FL4: P2B11_FL4_SEQ).    *)
(*  T2 abs Rm <= CM / t on g(-t)-balls about q of radius A sqrt t at the     *)
(*     times -(1 - s) t (Cor 9.10: P2B11_CURV_BOUND); the hypotheses of     *)
(*     ANCIENT_COMPACT for the flows shifted to -tau k (P2B11_ANCIENT_HYPS). *)
(*  T3 the backward limit, its joinable class and the slice limit at 0 of   *)
(*     the kviews at the base times -tau k (P2B11_BACK_LIMIT).               *)
(*  T4 the forward extension to s < 1 by P2C_PROP_5_14 with the same W and   *)
(*     phi (P2B11_FWD_HYPS, P2B11_FWD_LIMIT); the limit data p2b11_flim      *)
(*     (P2B11_FLIM_EXISTS).                                                   *)
(*  T5 sec >= 0, R nondecreasing in s, dR/ds >= 0, complete slices for       *)
(*     s <= 0, kappa-noncollapsing, Ricci flow on (a,1).                      *)
(*  T6 completeness for 0 <= s < 1: on the g'(s)-ball of radius D about xl, *)
(*     R <= 3 (2 + 2D)^2 / (1 - s)^3 (the transferred Cor 9.16,              *)
(*     P2B11_FLIM_RBALL); hence sec <= K at all times in [0,s] there,        *)
(*     g'(0) <= exp(4 K s) g'(s) along short curves (P2B11_METRIC_FWD), and  *)
(*     closed g'(s)-balls lie in compact g'(0)-balls                          *)
(*     (P2B11_FLIM_COMPLETE_FWD).                                             *)
(*  T7 Prop 9.20 on the limit, the leaf, p2b_ancflow0 and the assembly.      *)
(* P2B11_P3_SLICE and P2B11_SLICE_TO_FLOW0 are in pc_p2b_limbridge.         *)
(* ========================================================================= *)

needs "src/pc_p2b_x0.ml";;
needs "src/pc_p2b_limbridge.ml";;
needs "src/pc_lim_dist.ml";;
needs "src/pc_lim_back.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_lim_curv.ml";;
needs "src/pc_p2b_gaussreq.ml";;
needs "src/pc_p2b_c914.ml";;
needs "src/pc_cmp_pull.ml";;

prioritize_real();;
type_invention_error := true;;

(* T911.B1 Reduced length and curvature bounds on balls of the base slice.  *)

(* sqrt(l) grows at most linearly (Cor 9.10 part 2): on the ball of g(-t)   *)
(* of radius A sqrt t about a point q with l(q) <= 3/2, l <= (2 + A)^2.      *)

let P2B11_LX_BALL = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p t q A y.
     P2B_COR_9_10_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ &0 < t /\ q IN topspace top /\
     p2b_klx (top,atlas) g p t q <= &3 / &2 /\ &0 <= A /\
     y IN mfd_ball (top,atlas) (g(--t)) q (A * sqrt t)
     ==> y IN topspace top /\ p2b_klx (top,atlas) g p t y <= (&2 + A) pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cor") (CONJUNCTS_THEN2 (LABEL_TAC "ks")
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(--t)) q (A * sqrt t)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ASM_REWRITE_TAC[]] THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(--t))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3)(--t)) q y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "cor" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`] o
    REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2") ASSUME_TAC)) THEN
  ABBREV_TAC `L = p2b_klx (top,atlas) (g:real->B->real^3^3) p t y` THEN
  ABBREV_TAC `L0 = p2b_klx (top,atlas) (g:real->B->real^3^3) p t q` THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->B->real^3^3)(--t)) q y` THEN
  SUBGOAL_THEN `&0 <= L /\ &0 <= L0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "L" THEN USE_THEN "c1" (MP_TAC o SPECL [`t:real`; `y:B`]);
      EXPAND_TAC "L0" THEN USE_THEN "c1" (MP_TAC o SPECL [`t:real`; `q:B`])] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt L <= sqrt L0 + sqrt(&3 / (&4 * t)) * d` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "L0"; "d"] THEN USE_THEN "c2" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt L0 <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3 / (&4 * t)) * d <= A` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt(&3 / (&4 * t))` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&3 / (&4 * t)) * (A * sqrt t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&3 / (&4 * t)) * (A * sqrt t) = A * sqrt(&3 / &4)` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `s * (A * r) = A * (s * r)`] THEN
      REWRITE_TAC[GSYM SQRT_MUL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt L <= &2 + A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L = sqrt L pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]);;

(* The curvature bound on such a ball at the times -(1 - s) t, a <= s <= b  *)
(* < 1 (Cor 9.10 parts 1 and 3, abs Rm <= R/2 for sec >= 0).                *)

let P2B11_CURV_BOUND = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p t q A a b s y.
     P2B_COR_9_10_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ &0 < t /\ q IN topspace top /\
     p2b_klx (top,atlas) g p t q <= &3 / &2 /\ &0 <= A /\ b < &1 /\ a <= s /\ s <= b /\
     y IN mfd_ball (top,atlas) (g(--t)) q (A * sqrt t)
     ==> mfd_rm_norm atlas (g(--t + s * t)) y <=
         (&3 / &2 * (inv((&1 - b) pow 2) + abs(&1 - a)) * (&2 + A) pow 2 / (&1 - b)) / t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `t:real`; `q:B`; `A:real`; `y:B`] P2B11_LX_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`] o
    REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
    (LABEL_TAC "c3"))) THEN
  ABBREV_TAC `t' = (&1 - s) * t` THEN
  SUBGOAL_THEN `&0 < t' /\ --t + s * t = --t'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `L = p2b_klx (top,atlas) (g:real->B->real^3^3) p t y` THEN
  ABBREV_TAC `L' = p2b_klx (top,atlas) (g:real->B->real^3^3) p t' y` THEN
  ABBREV_TAC `M = inv((&1 - b) pow 2) + abs(&1 - a)` THEN
  SUBGOAL_THEN `&0 <= L /\ &0 <= L' /\
                mfd_scalar atlas ((g:real->B->real^3^3)(--t')) y <= &3 * L' / t'`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "L'"] THEN
    USE_THEN "c1" (MP_TAC o SPECL [`t:real`; `y:B`]) THEN
    USE_THEN "c1" (MP_TAC o SPECL [`t':real`; `y:B`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - b /\ &1 - b <= &1 - s /\ &1 - s <= &1 - a /\ &0 < &1 - a`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L' <= M * L` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= s` THENL
     [SUBGOAL_THEN `t' pow 2 * L' <= t pow 2 * L` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["L"; "L'"] THEN
        USE_THEN "c3" (MP_TAC o SPECL [`y:B`; `t':real`; `t:real`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN EXPAND_TAC "t'" THEN
          REWRITE_TAC[REAL_ARITH `(&1 - s) * t <= t <=> &0 <= s * t`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `L' <= inv((&1 - s) pow 2) * L` ASSUME_TAC THENL
       [UNDISCH_TAC `t' pow 2 * L' <= t pow 2 * L` THEN EXPAND_TAC "t'" THEN
        REWRITE_TAC[REAL_POW_MUL] THEN
        SUBGOAL_THEN `&0 < (&1 - s) pow 2 /\ &0 < t pow 2` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `(&1 - s) pow 2 * L' <= L` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `t pow 2` THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `(&1 - s) pow 2` THEN
        ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((&1 - s) pow 2) * L` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "M" THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN
      REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `t * L' <= t' * L` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["L"; "L'"] THEN
        USE_THEN "c3" (MP_TAC o SPECL [`y:B`; `t:real`; `t':real`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN EXPAND_TAC "t'" THEN
          REWRITE_TAC[REAL_ARITH `t <= (&1 - s) * t <=> &0 <= --s * t`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `L' <= (&1 - s) * L` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t * L' <= t' * L` THEN EXPAND_TAC "t'" THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - s) * L` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "M" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ y <= z ==> y <= x + z`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_rm_norm atlas ((g:real->B->real^3^3)(--t')) y <=
                mfd_scalar atlas (g(--t')) y / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(MATCH_MP P2B_KSOL_BASIC
      (ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`)))))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L' / t' <= (M * (&2 + A) pow 2) / ((&1 - b) * t)` ASSUME_TAC THENL
   [SUBGOAL_THEN `L' <= M * (&2 + A) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * L` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= M * (&2 + A) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(M * (&2 + A) pow 2) * inv t'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "t'" THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3)(--t')) y / &2` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&3 * ((M * (&2 + A) pow 2) / ((&1 - b) * t))) / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= y ==> x / &2 <= y / &2`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * L' / t'` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    REAL_ARITH_TAC]);;

(* T911.B2 Points of reduced length at most 3/2 at every backward time      *)
(* (FL4 on the view of [-2 tau, 0]), and the sequences tau k = k + 1, q k.  *)

let P2B11_FL4_POINT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p tau.
     P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ &0 < tau
     ==> ?q. q IN topspace top /\ p2b_klx (top,atlas) g p tau q <= &3 / &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[P2A_FLOW_THM_7_10_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `--(&2 * tau)`; `&0`; `g:real->B->real^3^3`; `p:B`; `tau:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_KSOL_CBFLOW THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`) THEN
      REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[p2b_klx; DIMINDEX_3] THEN MESON_TAC[]]);;

let P2B11_FL4_SEQ = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p.
     P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top
     ==> ?(tau:num->real) (q:num->B).
                 (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
                 (!k. q k IN topspace top /\
                      p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `\k:num. &k + &1` THEN
  SUBGOAL_THEN `?q:num->B. !k. q k IN topspace top /\
                  p2b_klx (top,atlas) (g:real->B->real^3^3) p (&k + &1) (q k) <= &3 / &2`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN MATCH_MP_TAC P2B11_FL4_POINT THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `q:num->B` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `M:real` THEN
  MP_TAC(SPEC `M:real` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&N <= &k` MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* T911.B3 The hypotheses of ANCIENT_COMPACT for the flows shifted to the   *)
(* base times -tau k and rescaled by Q k = inv(tau k) at the points q k.    *)

let P2B11_ANCIENT_HYPS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B).
     P2B_COR_9_10_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ (!k. &0 < tau k) /\
     (!k. q k IN topspace top /\ p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2)
     ==> (!k. hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (\t. g(--(tau k) + t))) /\
              (!t. t <= &0 ==> mfd_complete (top,atlas) (g(--(tau k) + t))) /\
              q k IN topspace top /\ &0 < inv(tau k)) /\
         (!A a. &0 < A /\ a < &0
                ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                                   y IN mfd_ball (top,atlas) (g(--(tau k) + &0)) (q k)
                                          (A * inv(sqrt(inv(tau k))))
                                   ==> mfd_rm_norm atlas (g(--(tau k) + s / inv(tau k))) y <=
                                       CA * inv(tau k)) /\
         (?r0 kappa' N. &0 < r0 /\ &0 < kappa' /\
            !k. N <= k
                ==> ?v. mfd_has_volume (top,atlas) (g(--(tau k) + &0))
                          (mfd_ball (top,atlas) (g(--(tau k) + &0)) (q k)
                             (r0 * inv(sqrt(inv(tau k))))) v /\
                        kappa' * (r0 * inv(sqrt(inv(tau k)))) pow 3 <= v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cor") (CONJUNCTS_THEN2 (LABEL_TAC "ks")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tau") (LABEL_TAC "q"))))) THEN
  USE_THEN "ks" (MP_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto")
    (CONJUNCTS_THEN2 (LABEL_TAC "comp") (CONJUNCTS_THEN2 (LABEL_TAC "sec") (LABEL_TAC "bd"))))) THEN
  USE_THEN "ks" (MP_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!k. inv(sqrt(inv((tau:num->real) k))) = sqrt(tau k) /\
                    !s. s / inv(tau k) = s * tau k` (LABEL_TAC "simp") THENL
   [GEN_TAC THEN REWRITE_TAC[SQRT_INV; REAL_INV_INV; real_div]; ALL_TAC] THEN
  USE_THEN "simp" (fun th -> REWRITE_TAC[th; REAL_ADD_RID]) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
     [X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX0_FLOW_UPTO_SHIFT THEN
      MAP_EVERY EXISTS_TAC [`--((tau:num->real) k) + a - &1`; `&0`] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "upto" (MP_TAC o SPEC `--((tau:num->real) k) + a - &1`) THEN
        ANTS_TAC THENL
         [USE_THEN "tau" (MP_TAC o SPEC `k:num`) THEN ASM_REAL_ARITH_TAC;
          SIMP_TAC[rfs_flow_upto]];
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        USE_THEN "tau" (MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "comp" MATCH_MP_TAC THEN
      USE_THEN "tau" (MP_TAC o SPEC `k:num`) THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`A:real`; `a:real`] THEN STRIP_TAC THEN
    EXISTS_TAC `&3 / &2 * (inv((&1 - &0) pow 2) + abs(&1 - a)) * (&2 + A) pow 2 / (&1 - &0)` THEN
    EXISTS_TAC `0` THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y:B`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC P2B11_CURV_BOUND THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`; `p:B`; `(q:num->B) k`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "q" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&1 / &8`; `kappa:real`; `0`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&0 < kappa` (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "ks" (MP_TAC o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `tk = (tau:num->real) k` THEN
  SUBGOAL_THEN `&0 < tk` ASSUME_TAC THENL
   [EXPAND_TAC "tk" THEN USE_THEN "tau" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  ABBREV_TAC `r = &1 / &8 * sqrt tk` THEN
  SUBGOAL_THEN `&0 < r /\ r pow 2 = tk / &64 /\ r <= &1 * sqrt tk` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    SUBGOAL_THEN `&0 < sqrt tk` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--tk <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`) THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
  REWRITE_TAC[rfs_flow_view] THEN REWRITE_TAC[rfs_kappa_noncollapsed] THEN
  DISCH_THEN(MP_TAC o SPECL [`--tk:real`; `(q:num->B) k`; `r:real`]) THEN
  REWRITE_TAC[rfs_flow_view; rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM] THEN
  USE_THEN "q" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&3 / &2 * (inv((&1 - &0) pow 2) + abs(&1 - --(&1))) * (&2 + &1) pow 2 /
                 (&1 - &0)) / tk` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `s = --tk + ((s + tk) / tk) * tk` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < tk` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC P2B11_CURV_BOUND THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`; `p:B`; `(q:num->B) k`] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [EXPAND_TAC "tk" THEN USE_THEN "q" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (--tk)) ((q:num->B) k) r` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv(tk / &64) = &64 / tk` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < tk` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    MESON_TAC[]]);;

(* T911.B4 The backward limit: ANCIENT_COMPACT, the joinable class of xl,   *)
(* and the slice limit at time 0 for the kviews at the base times -tau k.  *)

(* P2B11_P3_SLICE (a flow limit on (-Tl,0] gives the slice limit at time  *)
(* 0) is in pc_p2b_limbridge.                                              *)

(* Slice limits only see the slices of the views at the base times. *)

let P2B11_SLICE_CONG = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    V' x t t' Q (top:B topology) atlas g0 xl W phi.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!k. rfs_vtop (V' k) (t' k) = rfs_vtop (V k) (t k) /\
          rfs_vatlas (V' k) (t' k) = rfs_vatlas (V k) (t k) /\
          rfs_vmetric (V' k) (t' k) = rfs_vmetric (V k) (t k))
     ==> p2c_slice_limit_with V' x t' Q (top,atlas) g0 xl W phi`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[p2c_slice_limit_with] THEN ASM_REWRITE_TAC[]);;

(* The backward limit. *)

let P2B11_BACK_LIMIT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B).
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ (!k. &0 < tau k) /\
     (!k. q k IN topspace top /\ p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2)
     ==> ?sub (top':B topology) atlas' g0 xl W phi.
            p3_subseq sub /\
            p2c_slice_limit_with (\k. p2b_kview (top,atlas) g) (q o sub)
                                 (\k. --(tau(sub k))) (\k. inv(tau(sub k)))
                                 (top',atlas') g0 xl W phi /\
            connected_space top' /\ mfd_complete (top',atlas') g0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "AC") (CONJUNCTS_THEN2 (LABEL_TAC "cor")
    (CONJUNCTS_THEN2 (LABEL_TAC "ks") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "tau") (LABEL_TAC "q")))))) THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `tau:num->real`; `q:num->B`] P2B11_ANCIENT_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "hyps")] THEN
  USE_THEN "AC" (MP_TAC o REWRITE_RULE[P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. (top:B topology)`; `\k:num. (atlas:((B->bool)#(B->real^3))->bool)`;
    `\k:num t. (g:real->B->real^3^3) (--((tau:num->real) k) + t)`; `q:num->B`;
    `\k. inv((tau:num->real) k)`]) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [USE_THEN "hyps" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top1:B topology`
    (X_CHOOSE_THEN `atlas1:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g1:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim1")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem1") (LABEL_TAC "comp1"))))))))) THEN
  USE_THEN "lim1" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(LABEL_TAC "lim") THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top1:B topology) (atlas1:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o REWRITE_RULE[p3_flow_limit]) THEN SIMP_TAC[]; ALL_TAC] THEN
  (* the shifted views are regular *)
  MP_TAC(ISPECL
   [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0}
                           (\t. (g:real->B->real^3^3) (--((tau:num->real) (sub k)) + t))`;
    `(q:num->B) o (sub:num->num)`; `\k:num. &0`;
    `(\k. inv((tau:num->real) k)) o (sub:num->num)`;
    `top1:B topology`; `atlas1:((B->bool)#(B->real^3))->bool`; `g1:real->B->real^3^3`;
    `xl:B`; `&1`] P2CO_P3_FLOW_RESTRICT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; USE_THEN "lim" ACCEPT_TAC] THEN
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `{t:real | t <= &0}`;
                   `\t. (g:real->B->real^3^3) (--((tau:num->real) (sub(n:num))) + t)`]
                  P2BX0_VIEW_REGULAR) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "tau" (MP_TAC o SPEC `(sub:num->num) n`) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rlim") ASSUME_TAC)] THEN
  USE_THEN "rlim" (MP_TAC o MATCH_MP P2B11_P3_SLICE) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (LABEL_TAC "sl"))) THEN
  MAP_EVERY EXISTS_TAC
   [`sub:num->num`;
    `subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_metric atlas1
       {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
       ((g1:real->B->real^3^3) (&0))`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2B11_SLICE_CONG THEN
    MAP_EVERY EXISTS_TAC
     [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0}
                             (\t. (g:real->B->real^3^3) (--((tau:num->real) (sub k)) + t))`;
      `\k:num. &0`] THEN
    CONJ_TAC THENL
     [USE_THEN "sl" (MP_TAC o BETA_RULE) THEN
      SUBGOAL_THEN `(\k. inv((tau:num->real) k)) o (sub:num->num) = (\k. inv(tau(sub k)))`
      (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[FUN_EQ_THM; o_THM];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[p2b_kview; P2BX0_VIEW_FACTS; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID] THEN
    SUBGOAL_THEN `--((tau:num->real) ((sub:num->num) k)) <= &0` (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "tau" (MP_TAC o SPEC `(sub:num->num) k`) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P2CO_CLASS_COMPLETE THEN ASM_REWRITE_TAC[]]);;

(* T911.B5 The kviews of a kappa-solution are regular views; a slice limit  *)
(* is a flow limit on J = {0}.                                               *)

let P2B11_KVIEW_REGULAR = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> p2c_regular_view (p2b_kview (top,atlas) g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "upto"))))) THEN
  SUBGOAL_THEN `!a. a < &0 ==> ricci_flow_on (top,atlas) a (&0) (g:real->B->real^3^3)`
  (LABEL_TAC "rfo") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "upto" (MP_TAC o C MP (ASSUME `a < &0`) o SPEC `a:real`) THEN
    SIMP_TAC[rfs_flow_upto];
    ALL_TAC] THEN
  REWRITE_TAC[p2b_kview] THEN MATCH_MP_TAC P2CF_FLOW_VIEW_REGULAR_GEN THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `b = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a - &1`; `&0`] THEN
      CONJ_TAC THENL
       [USE_THEN "rfo" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CF_RFO_FROM THEN MAP_EVERY EXISTS_TAC [`a - &1`; `&0`] THEN
    CONJ_TAC THENL
     [USE_THEN "rfo" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* P2B11_SLICE_TO_FLOW0 (a slice limit is a flow limit on J = {0}) is in    *)
(* pc_p2b_limbridge.                                                        *)

(* T911.B6 A Ricci flow on every (a,b), b < 1, is a Ricci flow on (a,1).    *)

let P2B11_RFO_TO_ONE = prove
 (`!top atlas (g:real->A->real^N^N) a.
     a < &1 /\ (!b. a < b /\ b < &1 ==> ricci_flow_on (top,atlas) a b g)
     ==> ricci_flow_on (top,atlas) a (&1) g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rf")) THEN
  SUBGOAL_THEN `!t. a < t /\ t < &1 ==> ricci_flow_on (top,atlas) a ((t + &1) / &2)
                                        (g:real->A->real^N^N)` (LABEL_TAC "rft") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [USE_THEN "rf" (MP_TAC o SPEC `(a + &1) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ricci_flow_on]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ricci_flow_on] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rft" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ricci_flow_on]] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      SUBGOAL_THEN `?U phi. c = (U:A->bool,phi:A->real^N)` STRIP_ASSUME_TAC THENL
       [MESON_TAC[PAIR]; ALL_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN
      ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `interval(lift a,lift((drop u + &1) / &2)) PCROSS
                IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      SUBGOAL_THEN `?U phi. c = (U:A->bool,phi:A->real^N)` STRIP_ASSUME_TAC THENL
       [MESON_TAC[PAIR]; ALL_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN
      ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "rft" (MP_TAC o SPEC `drop u`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ricci_flow_on]] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "rft" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ricci_flow_on]] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* T911.B7 Forward metric comparison: if the sectional curvatures at x are  *)
(* at most K on [s0,s1], then g(s0) <= exp(4 K (s1 - s0)) g(s1) at x        *)
(* (dg/dt = -2 Ric >= -4 K g in dimension 3; exp(4 K t) v.g(t)v increases). *)

let P2B11_METRIC_FWD = prove
 (`!top atlas (g:real->A->real^3^3) a b s0 s1 x (v:real^3) K.
     ricci_flow_on (top,atlas) a b g /\ a < s0 /\ s0 <= s1 /\ s1 < b /\
     x IN topspace top /\ &0 <= K /\
     (!t u w. s0 <= t /\ t <= s1 /\ ~collinear {vec 0,u,w}
              ==> mfd_sectional atlas (g t) x u w <= K)
     ==> v dot (g s0 x ** v) <= exp(&4 * K * (s1 - s0)) * (v dot (g s1 x ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s0:real = s1` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 < s1:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                !t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < b
        ==> ((\t. exp(&4 * K * t) * ((v:real^3) dot ((g:real->A->real^3^3) t x ** v)))
             has_real_derivative
             (exp(&4 * K * t) *
              (v dot ((--(&2) %% mfd_ricci_matrix atlas (g t) x) ** v)) +
              ((&4 * K) * exp(&4 * K * t)) * (v dot (g t x ** v)))) (atreal t)`
  (LABEL_TAC "D") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\t:real. exp(&4 * K * t)`; `(&4 * K) * exp(&4 * K * t)`;
                   `\t. (v:real^3) dot ((g:real->A->real^3^3) t x ** v)`;
                   `(v:real^3) dot ((--(&2) %% mfd_ricci_matrix atlas
                                     ((g:real->A->real^3^3) t) x) ** v)`;
                   `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P4_RF_PREFERRED_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. exp(&4 * K * t) * ((v:real^3) dot ((g:real->A->real^3^3) t x ** v))`;
    `\t. exp(&4 * K * t) *
         ((v:real^3) dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->A->real^3^3) t) x) ** v)) +
         ((&4 * K) * exp(&4 * K * t)) * (v dot (g t x ** v))`;
    `s0:real`; `s1:real`] REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
      REWRITE_TAC[real_differentiable_on; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      EXISTS_TAC
       `exp(&4 * K * t) *
        ((v:real^3) dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->A->real^3^3) t) x) ** v)) +
        ((&4 * K) * exp(&4 * K * t)) * (v dot (g t x ** v))` THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      USE_THEN "D" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      USE_THEN "D" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `t IN real_interval(s0,s1)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ricci atlas ((g:real->A->real^3^3) t) x v v <=
                &2 * K * (v dot (g t x ** v))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`; `K:real`; `v:real^3`]
                  P2BFF_MFD_RICCI_SEC_UPPER) THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->A->real^3^3) t) x) ** v) =
                --(&2) * mfd_ricci atlas (g t) x v v` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`; `v:real^3`; `v:real^3`] P3S_MFD_RICCI_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot ((g:real->A->real^3^3) t x ** v)` ASSUME_TAC THENL
   [ASM_CASES_TAC `v:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`] RIEMANNIAN_METRIC_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(&4 * K * t)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (exp(&4 * K * t) *
           ((v:real^3) dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->A->real^3^3) t) x) ** v)) +
           ((&4 * K) * exp(&4 * K * t)) * (v dot (g t x ** v))) * (s1 - s0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= e * (&4 * K * q - &2 * r) ==> &0 <= e * --(&2) * r + ((&4 * K) * e) * q`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(&4 * K * s0) * ((v:real^3) dot ((g:real->A->real^3^3) s0 x ** v)) <=
    exp(&4 * K * s1) * (v dot (g s1 x ** v))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `exp(&4 * K * s0)` THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN
  SUBGOAL_THEN `exp(&4 * K * s0) * exp(&4 * K * (s1 - s0)) *
                ((v:real^3) dot ((g:real->A->real^3^3) s1 x ** v)) =
                exp(&4 * K * s1) * (v dot (g s1 x ** v))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* T911.B8 The curvature hypothesis of P2C_PROP_5_14 for the slice limit of *)
(* the kviews at the base times -tau k: the images of W m lie in balls of   *)
(* g(-tau n) about q n of radius (D + 1) sqrt(tau n) (LIM_BALL_OUT at s = 0) *)
(* where Cor 9.10 bounds abs Rm by CM / tau n at the times -(1 - s) tau n.   *)

let P2B11_FWD_HYPS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (sub:num->num) (top':B topology) atlas' g0 xl W phi.
     P2B_COR_9_10_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ (!k. &0 < tau k) /\
     (!k. q k IN topspace top /\ p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2) /\
     p2c_slice_limit_with (\k. p2b_kview (top,atlas) g) (q o sub)
                          (\k. --(tau(sub k))) (\k. inv(tau(sub k)))
                          (top',atlas') g0 xl W phi /\
     connected_space top' /\ mfd_complete (top',atlas') g0
     ==> !m a b.
           real_interval[a,b] SUBSET {s | s < &1}
           ==> ?CM N. !n. N <= n
                 ==> (!s. a <= s /\ s <= b
                          ==> IMAGE (phi n) (W m) SUBSET
                              topspace(rfs_vtop (p2b_kview (top,atlas) g)
                                         (--(tau(sub n)) + s / inv(tau(sub n))))) /\
                     rfs_persists (p2b_kview (top,atlas) g) (IMAGE (phi n) (W m))
                                  (--(tau(sub n)) + a / inv(tau(sub n)))
                                  (--(tau(sub n)) + b / inv(tau(sub n))) /\
                     !s y. a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                           ==> p3_vrm (p2b_kview (top,atlas) g)
                                      (--(tau(sub n)) + s / inv(tau(sub n))) y <=
                               CM * inv(tau(sub n))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cor") (CONJUNCTS_THEN2 (LABEL_TAC "ks")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tau")
    (CONJUNCTS_THEN2 (LABEL_TAC "q") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `!n s. s / inv((tau:num->real)((sub:num->num) n)) = s * tau(sub n)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div; REAL_INV_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. rfs_vatlas (p2b_kview (top,atlas) (g:real->B->real^3^3)) t = atlas /\
                    rfs_vmetric (p2b_kview (top,atlas) g) t = g t /\
                    (t <= &0 ==> rfs_vtop (p2b_kview (top,atlas) g) t = top)`
  (LABEL_TAC "kv") THENL
   [GEN_TAC THEN REWRITE_TAC[p2b_kview; P2BX0_VIEW_FACTS; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o REWRITE_RULE[p2c_slice_limit_with]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "W")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "phix")
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "lck")))))))))) THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `b < a:real` THENL
   [MAP_EVERY EXISTS_TAC [`&0`; `0`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `b * (tau:num->real)((sub:num->num) n) < a * tau(sub n)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN SUBGOAL_THEN `F` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; MESON_TAC[]];
      REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_persists] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN SUBGOAL_THEN `F` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; MESON_TAC[]];
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `F` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `b < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET {s:real | s < &1}` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the radius D of a g0-ball containing W m *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `top' closure_of (W:num->B->bool) m`] LIM_COMPACT_DIST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "W" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET mfd_ball (top',atlas':((B->bool)#(B->real^3))->bool) (g0:B->real^3^3) xl D` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:B) IN topspace top' /\ z IN top' closure_of (W:num->B->bool) m`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "W" (MP_TAC o SPEC `m:num`) THEN STRIP_TAC THEN
      SUBGOAL_THEN `(W:num->B->bool) m SUBSET topspace top'` ASSUME_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top':B topology`; `(W:num->B->bool) m`] CLOSURE_OF_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* LIM_BALL_OUT at s = 0 *)
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `(q:num->B) o (sub:num->num)`;
                 `\k. --((tau:num->real)((sub:num->num) k))`; `\k. inv((tau:num->real)((sub:num->num) k))`;
                 `{&0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `\s:real. (g0:B->real^3^3)`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `&0`; `xl:B`; `D:real`; `D + &1`] LIM_BALL_OUT) THEN
  REWRITE_TAC[IN_SING] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2B11_SLICE_TO_FLOW0 THEN USE_THEN "sl" ACCEPT_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC[p2b_kview] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `{t:real | t <= &0}`; `g:real->B->real^3^3`] P2BX0_VIEW_REGULAR) THEN
      REWRITE_TAC[IN_ELIM_THM; P2BX0_VIEW_FACTS] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "out")) THEN
  EXISTS_TAC `&3 / &2 * (inv((&1 - b) pow 2) + abs(&1 - a)) * (&2 + (D + &1)) pow 2 /
              (&1 - b)` THEN
  EXISTS_TAC `(k0:num) + SUC (m:num)` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ABBREV_TAC `Tk = (tau:num->real)((sub:num->num) n)` THEN
  SUBGOAL_THEN `&0 < Tk` ASSUME_TAC THENL
   [EXPAND_TAC "Tk" THEN USE_THEN "tau" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  (* the images of W m *)
  SUBGOAL_THEN
   `!z. z IN (W:num->B->bool) m
        ==> (phi:num->B->B) n z IN
            mfd_ball (top,atlas) ((g:real->B->real^3^3)(--Tk)) ((q:num->B)((sub:num->num) n))
                     ((D + &1) * sqrt Tk)`
  (LABEL_TAC "img") THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    USE_THEN "out" (MP_TAC o SPECL [`n:num`; `z:B`]) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `--Tk <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "phix" (fun th -> REWRITE_TAC[th; o_THM]) THEN
    ASM_SIMP_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; SQRT_INV; REAL_INV_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= b ==> --Tk + s * Tk <= &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `s * Tk <= &1 * Tk` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "kv" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `--Tk + s * Tk`) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    USE_THEN "img" (MP_TAC o C MP (ASSUME `(z:B) IN (W:num->B->bool) m`) o SPEC `z:B`) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE o CONJUNCT1) THEN SIMP_TAC[];
    REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_persists; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s <= &0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--Tk + b * Tk` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "dif" (MP_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `rfs_vtop (p2b_kview (top,atlas) (g:real->B->real^3^3))
                    (--((tau:num->real)((sub:num->num) n))) = top /\
                  rfs_vatlas (p2b_kview (top,atlas) g) (--(tau(sub n))) = atlas`
    (fun th -> REWRITE_TAC[th]) THENL
     [USE_THEN "kv" (MP_TAC o SPEC `--((tau:num->real)((sub:num->num) n))`) THEN
      SUBGOAL_THEN `--((tau:num->real)((sub:num->num) n)) <= &0` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `psi:B->B`) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) n`; `IMAGE ((phi:num->B->B) n) ((W:num->B->bool) n)`;
                   `(phi:num->B->B) n`; `psi:B->B`; `{}:B->bool`; `(W:num->B->bool) m`]
                  LIM_DIFFEO_IMAGE_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_IN_EMPTY; EMPTY_SUBSET] THEN
      SUBGOAL_THEN `!m n. m <= n ==> (W:num->B->bool) m SUBSET W n`
      (fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC) THEN
      MATCH_MP_TAC P2B_EXHAUST_MONO THEN
      X_GEN_TAC `k:num` THEN USE_THEN "W" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top' closure_of (W:num->B->bool) k` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:B) IN IMAGE ((phi:num->B->B) n) ((W:num->B->bool) m)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[p3_vrm] THEN USE_THEN "kv" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC P2B11_CURV_BOUND THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`; `p:B`;
                          `(q:num->B)((sub:num->num) n)`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXPAND_TAC "Tk" THEN USE_THEN "q" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* T911.B9 The forward extension (P2C_PROP_5_14 on the times s < 1) of     *)
(* the slice limit at time 0, with the same W and phi.                      *)

let P2B11_FWD_LIMIT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (sub:num->num) (top':B topology) atlas' g0 xl W phi.
     P2C_PROP_5_14_STATEMENT w w /\ P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ (!k. &0 < tau k) /\
     (!k. q k IN topspace top /\ p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2) /\
     p2c_slice_limit_with (\k. p2b_kview (top,atlas) g) (q o sub)
                          (\k. --(tau(sub k))) (\k. inv(tau(sub k)))
                          (top',atlas') g0 xl W phi /\
     connected_space top' /\ mfd_complete (top',atlas') g0
     ==> ?sub2 g'. p3_subseq sub2 /\ g'(&0) = g0 /\
                   p2c_flow_limit_with (\n. p2b_kview (top,atlas) g) (\n. q(sub(sub2 n)))
                     (\n. --(tau(sub(sub2 n)))) (\n. inv(tau(sub(sub2 n)))) {s | s < &1}
                     (top',atlas') g' xl W (\n. phi(sub2 n)) /\
                   (!s. s < &1 ==> riemannian_metric atlas' (g' s)) /\
                   (!a b. a < b /\ b < &1 ==> ricci_flow_on (top',atlas') a b g')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "514") (CONJUNCTS_THEN2 (LABEL_TAC "cor")
    (CONJUNCTS_THEN2 (LABEL_TAC "ks") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "tau") (CONJUNCTS_THEN2 (LABEL_TAC "q")
    (CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `tau:num->real`; `q:num->B`; `sub:num->num`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`] P2B11_FWD_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "hyps")] THEN
  USE_THEN "514" (MP_TAC o REWRITE_RULE[P2C_PROP_5_14_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `(q:num->B) o (sub:num->num)`;
    `\k. --((tau:num->real)((sub:num->num) k))`; `\k. inv((tau:num->real)((sub:num->num) k))`;
    `{s:real | s < &1}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a0 - &1`) THEN ASM_REAL_ARITH_TAC;
      TRY GEN_TAC THEN MATCH_MP_TAC P2B11_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN
      USE_THEN "ks" ACCEPT_TAC;
      USE_THEN "sl" ACCEPT_TAC;
      USE_THEN "hyps" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "rfo") (K ALL_TAC)))))))) THEN
  MAP_EVERY EXISTS_TAC [`sub2:num->num`; `g':real->B->real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[o_DEF]) THEN REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "riem" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    USE_THEN "rfo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* T911.B10 The forward limit data of the route (an abbreviation of this    *)
(* unit) and their existence.                                                *)

let p2b11_flim = new_definition
 `p2b11_flim kappa (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
             (g:real->B->real^3^3) (p:B) (tau:num->real) (q:num->B)
             (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
             (g':real->B->real^3^3) (xl:B) (W:num->B->bool) (phi:num->B->B) <=>
    p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\
    (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
    (!k. q k IN topspace top /\ p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2) /\
    p2c_flow_limit_with (\k. p2b_kview (top,atlas) g) q (\k. --(tau k)) (\k. inv(tau k))
                        {s | s < &1} (top',atlas') g' xl W phi /\
    connected_space top' /\ mfd_complete (top',atlas') (g'(&0)) /\
    (!s. s < &1 ==> riemannian_metric atlas' (g' s)) /\
    (!a b. a < b /\ b < &1 ==> ricci_flow_on (top',atlas') a b g')`;;

let P2B11_FLIM_EXISTS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p.
     P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2C_PROP_5_14_STATEMENT w w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top
     ==> ?tau q (top':B topology) atlas' g' xl W phi.
            p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]
                P2B11_FL4_SEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau0:num->real` (X_CHOOSE_THEN `q0:num->B`
    (CONJUNCTS_THEN2 (LABEL_TAC "tpos") (CONJUNCTS_THEN2 (LABEL_TAC "tdiv")
      (LABEL_TAC "q0"))))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `tau0:num->real`; `q0:num->B`] P2B11_BACK_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g0:B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `tau0:num->real`; `q0:num->B`; `sub:num->num`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`] P2B11_FWD_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `g':real->B->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`\n. (tau0:num->real)((sub:num->num)((sub2:num->num) n))`;
    `\n. (q0:num->B)((sub:num->num)((sub2:num->num) n))`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
    `xl:B`; `W:num->B->bool`; `\n. (phi:num->B->B)((sub2:num->num) n)`] THEN
  REWRITE_TAC[p2b11_flim] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  X_GEN_TAC `M:real` THEN USE_THEN "tdiv" (X_CHOOSE_TAC `N:num` o SPEC `M:real`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPEC `sub:num->num` P2BX0_SUBSEQ_GE) THEN
  MP_TAC(SPEC `sub2:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `(sub2:num->num) k`) THEN MP_TAC th) THEN
  ASM_ARITH_TAC);;

(* T911.B11 Properties of the forward limit: the view hypotheses of the    *)
(* limit statements (such as LIM_CURV_STATEMENT and LIM_KNC_STATEMENT),    *)
(* nonnegative sectional curvature, phi k y lies in the slices, and the    *)
(* scalar curvature does not decrease in s.                                *)

let P2B11_KVIEW_LIMHYPS = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> (!s. ~(topspace(rfs_vtop (p2b_kview (top,atlas) g) s) = {})
              ==> smooth_manifold_atlas (rfs_vtop (p2b_kview (top,atlas) g) s)
                                        (rfs_vatlas (p2b_kview (top,atlas) g) s) /\
                  riemannian_metric (rfs_vatlas (p2b_kview (top,atlas) g) s)
                                    (rfs_vmetric (p2b_kview (top,atlas) g) s)) /\
         (!s. hausdorff_space (rfs_vtop (p2b_kview (top,atlas) g) s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  REWRITE_TAC[p2b_kview] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `{t:real | t <= &0}`; `g:real->B->real^3^3`] P2BX0_VIEW_REGULAR) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX0_VIEW_HAUSDORFF THEN ASM_REWRITE_TAC[]]);;

let P2B11_FLIM_FACTS = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         (!s. s <= &0 ==> riemannian_metric atlas (g s)) /\
         (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
         (!t x u v. t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g t) x u v) /\
         hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ xl IN topspace top' /\
         (!k. (phi:num->B->B) k xl = q k) /\
         (!s. ~(topspace(rfs_vtop (p2b_kview (top,atlas) g) s) = {})
              ==> smooth_manifold_atlas (rfs_vtop (p2b_kview (top,atlas) g) s)
                                        (rfs_vatlas (p2b_kview (top,atlas) g) s) /\
                  riemannian_metric (rfs_vatlas (p2b_kview (top,atlas) g) s)
                                    (rfs_vmetric (p2b_kview (top,atlas) g) s)) /\
         (!s. hausdorff_space (rfs_vtop (p2b_kview (top,atlas) g) s)) /\
         (!t. rfs_vatlas (p2b_kview (top,atlas) g) t = atlas /\
              rfs_vmetric (p2b_kview (top,atlas) g) t = g t /\
              (t <= &0 ==> rfs_vtop (p2b_kview (top,atlas) g) t = top))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b11_flim] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B11_KVIEW_LIMHYPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  UNDISCH_TAC `p2c_flow_limit_with (\k. p2b_kview (top,atlas) (g:real->B->real^3^3))
                 (q:num->B) (\k. --((tau:num->real) k)) (\k. inv(tau k)) {s | s < &1}
                 (top',atlas') g' xl W (phi:num->B->B)` THEN
  REWRITE_TAC[p2c_flow_limit_with] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN REWRITE_TAC[p2b_kview; P2BX0_VIEW_FACTS; IN_ELIM_THM] THEN SIMP_TAC[]);;

(* Nonnegative sectional curvature of the limit slices. *)

let P2B11_FLIM_SEC = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> !s y u v. s < &1 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional atlas' (g' s) y u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2B11_FLIM_FACTS th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[p2b11_flim] th)) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:B)`; `(:B)`] LIM_CURV) THEN
  REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `q:num->B`;
    `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`; `{s:real | s < &1}`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`; `y:B`]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(REPEAT GEN_TAC THEN FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC th) THEN NO_TAC) THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `0` THEN MAP_EVERY X_GEN_TAC [`k:num`; `z:B`; `u':real^3`; `v':real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `--((tau:num->real) k) + s / inv(tau k) <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_INV] THEN
    SUBGOAL_THEN `&0 < (tau:num->real) k` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `s * (tau:num->real) k <= &1 * tau k` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]] THEN
  UNDISCH_TAC `(z:B) IN topspace (rfs_vtop (p2b_kview (top,atlas) (g:real->B->real^3^3))
                 (--((tau:num->real) k) + s / inv(tau k)))` THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* T911.B12 Points of the limit are eventually carried into the slices; the *)
(* scalar curvature of the limit does not decrease in s (KSOL_DRDT for the  *)
(* kappa-solution and LIM_CURV).                                             *)

let P2B11_SEQ_LIM_LE = prove
 (`!(f:num->real) g l m.
     (f ---> l) sequentially /\ (g ---> m) sequentially
     ==> (?N. !k. N <= k ==> f k <= g k) ==> l <= m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC [`f:num->real`; `g:num->real`] THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]);;

let P2B11_FLIM_PHI_IN = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> !s y. s < &1 /\ y IN topspace top'
               ==> ?k0. !k. k0 <= k ==> (phi:num->B->B) k y IN topspace top`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2B11_FLIM_FACTS th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[p2b11_flim] th)) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2c_flow_limit_with (\k. p2b_kview (top,atlas) (g:real->B->real^3^3))
                 (q:num->B) (\k. --((tau:num->real) k)) (\k. inv(tau k)) {s | s < &1}
                 (top',atlas') g' xl W (phi:num->B->B)` THEN
  REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `s:real`; `{y:B}`; `0`; `&1`] o
             last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01; SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN MP_TAC(SPEC `k:num` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real` o CONJUNCT1)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:B->B` (MP_TAC o CONJUNCT1 o CONJUNCT2 o
    REWRITE_RULE[mfd_diffeo])) THEN
  SUBGOAL_THEN `--((tau:num->real) k) + s / inv(tau k) <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_INV] THEN
    SUBGOAL_THEN `&0 < (tau:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s * (tau:num->real) k <= &1 * tau k` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

let P2B11_FLIM_MONO = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     P2B_KSOL_DRDT_STATEMENT w /\
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> !s1 s2 y. s1 <= s2 /\ s2 < &1 /\ y IN topspace top'
                   ==> mfd_scalar atlas' (g' s1) y <= mfd_scalar atlas' (g' s2) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2B11_FLIM_FACTS th) THEN
    LABEL_TAC "fl" th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2b11_flim] th))) THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`; `y:B`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:B`; `tau:num->real`; `q:num->B`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2B11_FLIM_PHI_IN) THEN
  ANTS_TAC THENL [USE_THEN "fl" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s1:real`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "in")) THEN
  SUBGOAL_THEN `s1 < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (sv,lab) ->
    MP_TAC(ISPECL [`(:B)`; `(:B)`] LIM_CURV) THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `q:num->B`;
      `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`; `{s:real | s < &1}`;
      `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
      `xl:B`; `W:num->B->bool`; `phi:num->B->B`; sv; `y:B`]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(REPEAT GEN_TAC THEN FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC th) THEN NO_TAC) THEN
      TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC THEN NO_TAC);
      DISCH_THEN(LABEL_TAC lab o CONJUNCT1)])
    [`s1:real`,"lim1"; `s2:real`,"lim2"] THEN
  USE_THEN "lim1" (fun th1 -> USE_THEN "lim2" (fun th2 -> MP_TAC(CONJ th1 th2))) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2B11_SEQ_LIM_LE) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `Tk = (tau:num->real) k` THEN
  SUBGOAL_THEN `&0 < Tk` ASSUME_TAC THENL
   [EXPAND_TAC "Tk" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_INV] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `s1 * Tk <= s2 * Tk /\ s2 * Tk < &1 * Tk` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX0_SCALAR_MONO THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `--Tk + s1 * Tk - &1`; `&0`] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `rfs_flow_upto (top,atlas) (--Tk + s1 * Tk - &1) (&0) (g:real->B->real^3^3)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)`)
            (concl th))) THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[rfs_flow_upto]];
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `dR:real`] THEN STRIP_TAC THEN
    USE_THEN "drdt" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] o
      REWRITE_RULE[P2B_KSOL_DRDT_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o SPECL [`s:real`; `(phi:num->B->B) k y`]) THEN
    ASM_REWRITE_TAC[] THEN
    TRY CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* T911.B13 More properties of the forward limit: Ricci flow on (a,1),     *)
(* complete slices for s <= 0, dR/ds >= 0, kappa-noncollapsing (given      *)
(* complete slices), and compact images of curves.                           *)

let P2B11_FLIM_RFO1 = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> !a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b11_flim] THEN STRIP_TAC THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2B11_RFO_TO_ONE THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P2B11_FLIM_COMPLETE_BACK = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> !s. s <= &0 ==> mfd_complete (top',atlas') (g' s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B11_FLIM_FACTS) THEN
  FIRST_ASSUM(LABEL_TAC "sec" o MATCH_MP P2B11_FLIM_SEC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2b11_flim] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b11_flim"))
                         (concl th))) THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(:B)` LIM_FLOW_COMPLETE_BACK) THEN
  REWRITE_TAC[LIM_FLOW_COMPLETE_BACK_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `g':real->B->real^3^3`; `s - &1`; `&0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`s - &1`; `&1 / &2`] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!a b. a < b /\ b < &1 ==> ricci_flow_on (top',atlas') a b
                                  (g':real->B->real^3^3)`) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2B11_FLIM_DRDS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     P2B_KSOL_DRDT_STATEMENT w /\
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> !s y dR. s < &1 /\ y IN topspace top' /\
                  ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                  ==> &0 <= dR`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "mono" o MATCH_MP P2B11_FLIM_MONO) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `dR:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX0_MONO_DERIV_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`\t. mfd_scalar atlas' ((g':real->B->real^3^3) t) y`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2B11_FLIM_KNC = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     (!s. s < &1 ==> mfd_complete (top',atlas') (g' s))
     ==> !r0. rfs_kappa_noncollapsed (rfs_flow_view (top',atlas') {s | s < &1} g') kappa r0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2B11_FLIM_FACTS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2b11_flim] th)) (LABEL_TAC "comp")) THEN
  X_GEN_TAC `r0:real` THEN
  MP_TAC(ISPECL [`(:B)`; `(:B)`] LIM_KNC) THEN REWRITE_TAC[LIM_KNC_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `q:num->B`;
    `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->B`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC th);
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN
    MP_TAC(ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`) THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol; p2b_kview] THEN SIMP_TAC[]]);;

let P2B11_CURVE_IMAGE_COMPACT = prove
 (`!top atlas (gamma:real->A) a b.
     mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b
     ==> compact_in top (IMAGE gamma (real_interval[a,b]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve] THEN STRIP_TAC THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL; COMPACT_IN_EUCLIDEANREAL_INTERVAL]);;

(* T911.B14 Transferred distance bound: a curve from xl of g'(s)-length < D *)
(* lies in some W m, where the rescaled pullbacks are at most twice g'(s),  *)
(* so its end is eventually at g(-tau k + s tau k)-distance at most        *)
(* sqrt 2 D sqrt(tau k) from q k (LIM_QF_CLOSE, P2B9S_DIST_IN_PB_LE).       *)

let P2B11_VIEW_DIST = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi s (gamma:real->B) D.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     s < &1 /\ mfd_c1_curve (top',atlas') gamma (&0) (&1) /\ gamma(&0) = xl /\
     mfd_length atlas' (g' s) gamma (&0) (&1) < D
     ==> ?k0. !k. k0 <= k
              ==> (phi:num->B->B) k (gamma(&1)) IN topspace top /\
                  mfd_joinable (top,atlas) (q k) (phi k (gamma(&1))) /\
                  mfd_dist (top,atlas) (g(--(tau k) + s * tau k)) (q k) (phi k (gamma(&1))) <=
                  sqrt(&2) * D * sqrt(tau k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2B11_FLIM_FACTS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2b11_flim] th)) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(LABEL_TAC "fl" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_flow_limit_with"))
        (concl th))) THEN
  USE_THEN "fl" (STRIP_ASSUME_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!s. s < &1 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`)
          (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the image of gamma lies in some W m *)
  SUBGOAL_THEN `compact_in top' (IMAGE (gamma:real->B) (real_interval[&0,&1]))` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`]
                       P2B11_CURVE_IMAGE_COMPACT) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. IMAGE (gamma:real->B) (real_interval[&0,&1]) SUBSET (W:num->B->bool) m`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o SPECL [`s:real`; `s:real`;
      `IMAGE (gamma:real->B) (real_interval[&0,&1])`; `0`; `&1`] o last o CONJUNCTS o
      REWRITE_RULE[p2c_flow_limit_with]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01; SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `m:num` (MP_TAC o SPEC `m:num`)) THEN
      REWRITE_TAC[LE_REFL] THEN MESON_TAC[]];
    ALL_TAC] THEN
  (* closeness on the closure of W m *)
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `q:num->B`;
                 `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`; `{s:real | s < &1}`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `s:real`; `s:real`; `top' closure_of (W:num->B->bool) m`; `&1`] LIM_QF_CLOSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "fl" ACCEPT_TAC;
      REPEAT GEN_TAC THEN FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC th);
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s':real = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "fl" (MP_TAC o SPEC `m:num` o el 5 o CONJUNCTS o REWRITE_RULE[p2c_flow_limit_with]) THEN SIMP_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "close")) THEN
  EXISTS_TAC `k1:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ABBREV_TAC `Tk = (tau:num->real) k` THEN
  SUBGOAL_THEN `&0 < Tk` ASSUME_TAC THENL
   [EXPAND_TAC "Tk" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--Tk + s * Tk <= &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `s * Tk <= &1 * Tk` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "close" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real`)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; real_div; REAL_INV_INV] THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "qf" (last cs) THEN X_CHOOSE_TAC `psi:B->B` (el (length cs - 2) cs)) THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET top' closure_of W m` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    USE_THEN "fl" (MP_TAC o SPEC `m:num` o el 5 o CONJUNCTS o REWRITE_RULE[p2c_flow_limit_with]) THEN
    MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W k` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) s`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3)(--Tk + s * Tk)`;
                 `(W:num->B->bool) k`; `IMAGE ((phi:num->B->B) k) (W k)`; `(phi:num->B->B) k`;
                 `psi:B->B`; `(W:num->B->bool) m`; `&2 * Tk`; `xl:B`; `(gamma:real->B)(&1)`]
                P2B9S_DIST_IN_PB_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!s. s <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) s)`)
            (concl th))) THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:B`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "qf" (MP_TAC o SPECL [`z:B`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `inv Tk` THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
      SUBGOAL_THEN `inv Tk * (&2 * Tk) * (v dot ((g':real->B->real^3^3) s z ** v)) =
                    &2 * (v dot (g' s z ** v))` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Tk` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[mfd_joinable_in] THEN EXISTS_TAC `gamma:real->B` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        not(is_forall(concl th)))) THEN
      REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN EXISTS_TAC `u:real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_dist_in (top',atlas') ((g':real->B->real^3^3) s) ((W:num->B->bool) m) xl (gamma(&1)) <
                D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas' ((g':real->B->real^3^3) s) gamma (&0) (&1)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->B)(&0) = xl`)) THEN
    MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
      not(is_forall(concl th)) && can (find_term ((=) `(W:num->B->bool) m`)) (concl th))) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) ((q:num->B) k) ((phi:num->B->B) k (gamma(&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN
    EXISTS_TAC `IMAGE ((phi:num->B->B) k) ((W:num->B->bool) m)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist_in (top,atlas) ((g:real->B->real^3^3)(--Tk + s * Tk))
                (IMAGE ((phi:num->B->B) k) ((W:num->B->bool) m)) (q k) (phi k (gamma(&1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!s. s <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) s)`)
          (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&2 * Tk) * mfd_dist_in (top',atlas') ((g':real->B->real^3^3) s) ((W:num->B->bool) m) xl
                                         (gamma(&1))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `sqrt(&2) * D * sqrt Tk = (sqrt(&2) * sqrt Tk) * D` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_POS; REAL_LT_IMP_LE]);;

(* T911.B15 Cor 9.10 at the backward time t' = (1 - s) T, 0 <= s < 1, for  *)
(* a point joined to q0 at g(-t')-distance at most sqrt 2 D sqrt T, where  *)
(* q0 has reduced length at most 3/2 at time T:                             *)
(*   T R(-t') <= 3 (2 + 2D)^2 / (1 - s)^3.                                   *)

let P2B11_SQ_LE = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x pow 2 <= y pow 2 ==> x <= y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_REFL] THEN
  ASM_MESON_TAC[REAL_LE_SQUARE_ABS; REAL_ABS_REFL]);;

let P2B11_LX_VIEW = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p Tk q0 s D y.
     P2B_COR_9_10_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ &0 < Tk /\ q0 IN topspace top /\
     p2b_klx (top,atlas) g p Tk q0 <= &3 / &2 /\
     &0 <= s /\ s < &1 /\ &0 <= D /\ mfd_joinable (top,atlas) q0 y /\
     mfd_dist (top,atlas) (g(--Tk + s * Tk)) q0 y <= sqrt(&2) * D * sqrt Tk
     ==> mfd_scalar atlas (g(--Tk + s * Tk)) y * Tk <= &3 * (&2 + &2 * D) pow 2 / (&1 - s) pow 3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cor") (CONJUNCTS_THEN2 (LABEL_TAC "ks")
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  USE_THEN "cor" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`] o
    REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
    (LABEL_TAC "c3"))) THEN
  ABBREV_TAC `u = &1 - s` THEN
  SUBGOAL_THEN `&0 < u /\ u <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--Tk + s * Tk = --(u * Tk)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "u" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t' = u * Tk` THEN
  SUBGOAL_THEN `&0 < t' /\ t' <= Tk` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `L = p2b_klx (top,atlas) (g:real->B->real^3^3) p t' y` THEN
  ABBREV_TAC `L0 = p2b_klx (top,atlas) (g:real->B->real^3^3) p t' q0` THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->B->real^3^3)(--t')) q0 y` THEN
  SUBGOAL_THEN `&0 <= L /\ mfd_scalar atlas ((g:real->B->real^3^3)(--t')) y <= &3 * L / t' /\
                &0 <= L0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "L0"] THEN
    USE_THEN "c1" (MP_TAC o SPECL [`t':real`; `y:B`]) THEN
    USE_THEN "c1" (MP_TAC o SPECL [`t':real`; `q0:B`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!s. s <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) s)`)
          (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* L0 u^2 <= 3/2 *)
  SUBGOAL_THEN `L0 * u pow 2 <= &3 / &2` ASSUME_TAC THENL
   [USE_THEN "c3" (MP_TAC o SPECL [`q0:B`; `t':real`; `Tk:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t'" THEN REWRITE_TAC[REAL_POW_MUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < Tk pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `Tk pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Tk pow 2 * p2b_klx (top,atlas) (g:real->B->real^3^3) p Tk q0 <=
                  Tk pow 2 * &3 / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the gradient estimate *)
  SUBGOAL_THEN `sqrt L <= sqrt L0 + sqrt(&3 / (&4 * t')) * d` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "L0"; "d"] THEN USE_THEN "c2" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt L0 * u <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B11_SQ_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_LT_IMP_LE; REAL_POS] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3 / (&4 * t')) * d * u <= &2 * D` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B11_SQ_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `sqrt(&3 / (&4 * t')) pow 2 = &3 / (&4 * t')` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `d pow 2 <= &2 * D pow 2 * Tk` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt(&2) * D * sqrt Tk) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3)(--t')) q0 y <=
                     sqrt(&2) * D * sqrt Tk` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POW_MUL] THEN
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_POS] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "t'" THEN
    SUBGOAL_THEN `&3 / (&4 * u * Tk) * d pow 2 * u pow 2 = (&3 * u / (&4 * Tk)) * d pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < u` THEN UNDISCH_TAC `&0 < Tk` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * u / (&4 * Tk)) * (&2 * D pow 2 * Tk)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&3 * u / (&4 * Tk)) * (&2 * D pow 2 * Tk) = &3 / &2 * u * D pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Tk` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `&0 <= D pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `u * D pow 2 <= &1 * D pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L * u pow 2 <= (&2 + &2 * D) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `L * u pow 2 = (sqrt L * u) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sqrt L0 + sqrt(&3 / (&4 * t')) * d) * u` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the scalar curvature *)
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * L / t') * Tk` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  EXPAND_TAC "t'" THEN
  SUBGOAL_THEN `(&3 * L / (u * Tk)) * Tk = &3 * (L * u pow 2) / u pow 3` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < u` THEN UNDISCH_TAC `&0 < Tk` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* T911.B16 The transferred Cor 9.16: on the g'(s)-ball of radius D about  *)
(* xl, 0 <= s < 1, the scalar curvature of the limit is at most            *)
(* 3 (2 + 2D)^2 / (1 - s)^3.                                                 *)

let P2B11_FLIM_RBALL = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi s D z.
     P2B_COR_9_10_STATEMENT w /\
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     &0 <= s /\ s < &1 /\ z IN mfd_ball (top',atlas') (g' s) xl D
     ==> mfd_scalar atlas' (g' s) z <= &3 * (&2 + &2 * D) pow 2 / (&1 - s) pow 3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cor") (CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "fl" th THEN
    STRIP_ASSUME_TAC(MATCH_MP P2B11_FLIM_FACTS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2b11_flim] th)) STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(z:B) IN mfd_ball (top',atlas') ((g':real->B->real^3^3) s) xl D` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!s. s < &1 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`)
          (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top',atlas') ((g':real->B->real^3^3) s) xl z` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) s`; `xl:B`; `z:B`;
                 `D - mfd_dist (top',atlas') ((g':real->B->real^3^3) s) xl z`]
                P2BC_DIST_APPROX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:B`; `tau:num->real`; `q:num->B`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `s:real`; `gamma:real->B`; `D:real`] P2B11_VIEW_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "vd")) THEN
  MP_TAC(ISPECL [`(:B)`; `(:B)`] LIM_CURV) THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `q:num->B`;
    `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`; `{s:real | s < &1}`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`; `z:B`]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(REPEAT GEN_TAC THEN FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC th) THEN NO_TAC) THEN
    TRY(ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE] THEN NO_TAC) THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`sequentially`; `&3 * (&2 + &2 * D) pow 2 / (&1 - s) pow 3`] REALLIM_CONST) THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2B11_SEQ_LIM_LE) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "vd" (MP_TAC o C MP (ASSUME `k0 <= k:num`) o SPEC `k:num`) THEN STRIP_TAC THEN
  ABBREV_TAC `Tk = (tau:num->real) k` THEN
  SUBGOAL_THEN `&0 < Tk` ASSUME_TAC THENL
   [EXPAND_TAC "Tk" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_INV] THEN ASM_REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC P2B11_LX_VIEW THEN
  MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`; `p:B`;
                        `(q:num->B) k`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Tk" THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* T911.B17 Completeness of the forward slices, 0 <= s < 1: a closed       *)
(* g'(s)-ball lies in a g'(s)-ball about xl of radius D, where the scalar  *)
(* curvature is at most C at all times in [0,s] (B16 and monotonicity), so  *)
(* sec <= C/2, g'(0) <= exp(4 (C/2) s) g'(s) along curves (B7), and the    *)
(* ball lies in a closed g'(0)-ball, which is compact.                      *)

let P2B11_FLIM_COMPLETE_FWD = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi s.
     P2B_COR_9_10_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w /\
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     &0 <= s /\ s < &1
     ==> mfd_complete (top',atlas') (g' s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cor") (CONJUNCTS_THEN2 (LABEL_TAC "drdt")
    (CONJUNCTS_THEN2 (fun th ->
      LABEL_TAC "fl" th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2B11_FLIM_FACTS th) THEN
      LABEL_TAC "sec" (MATCH_MP P2B11_FLIM_SEC th) THEN
      LABEL_TAC "rfo1" (MATCH_MP P2B11_FLIM_RFO1 th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2b11_flim] th)) STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!s1 s2 y. s1 <= s2 /\ s2 < &1 /\ y IN topspace top'
                          ==> mfd_scalar atlas' ((g':real->B->real^3^3) s1) y <=
                              mfd_scalar atlas' (g' s2) y` (LABEL_TAC "mono") THENL
   [MATCH_MP_TAC P2B11_FLIM_MONO THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `tau:num->real`;
      `q:num->B`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "fl" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < &1 ==> riemannian_metric atlas' ((g':real->B->real^3^3) t)`
  (LABEL_TAC "riem") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_complete] THEN MAP_EVERY X_GEN_TAC [`x:B`; `r:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top',atlas':((B->bool)#(B->real^3))->bool) (xl:B) x` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D = abs(mfd_dist (top',atlas') ((g':real->B->real^3^3) s) xl x) + abs r + &1` THEN
  SUBGOAL_THEN `&1 <= D` ASSUME_TAC THENL [EXPAND_TAC "D" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = (&3 * (&2 + &2 * D) pow 2 / (&1 - s) pow 3) / &2` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top',atlas') ((g':real->B->real^3^3)(&0)) xl
                        (sqrt(exp(&4 * K * s)) * D)` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top',atlas') ((g':real->B->real^3^3)(&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC;
    MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) s) /\
                riemannian_metric atlas' (g' (&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top',atlas':((B->bool)#(B->real^3))->bool) (xl:B) y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_dist (top',atlas') ((g':real->B->real^3^3) s) xl y < D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (top',atlas') ((g':real->B->real^3^3) s) xl x +
                mfd_dist (top',atlas') (g' s) x y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top',atlas') ((g':real->B->real^3^3) s) xl y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) s`; `xl:B`; `y:B`;
                 `D - mfd_dist (top',atlas') ((g':real->B->real^3^3) s) xl y`]
                P2BC_DIST_APPROX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_length atlas' ((g':real->B->real^3^3) s) gamma (&0) (&1) < D`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* along gamma the metric g'(0) is at most exp(4 K s) g'(s) *)
  SUBGOAL_THEN `!u v. &0 <= u /\ u <= &1
                      ==> v dot ((g':real->B->real^3^3)(&0) (gamma u) ** v) <=
                          exp(&4 * K * s) * (v dot (g' s (gamma u) ** v))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma:real->B) u IN mfd_ball (top',atlas') ((g':real->B->real^3^3) s) xl D`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(g':real->B->real^3^3) s`; `gamma:real->B`; `xl:B`; `D:real`]
                    LIM_CURVE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(gamma:real->B) u IN topspace top'` ASSUME_TAC THENL
     [UNDISCH_TAC `(gamma:real->B) u IN mfd_ball (top',atlas') ((g':real->B->real^3^3) s) xl D` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(&4 * K * s) = exp(&4 * K * (s - &0))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_SUB_RZERO]; ALL_TAC] THEN
    MATCH_MP_TAC P2B11_METRIC_FWD THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `--(&1)`; `&1`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rfo1" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `a1:real^3`; `a2:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm atlas' ((g':real->B->real^3^3) t) ((gamma:real->B) u)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
      MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top':B topology` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas' ((g':real->B->real^3^3) t) ((gamma:real->B) u) / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top':B topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "K" THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> x / &2 <= y / &2`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas' ((g':real->B->real^3^3) s) ((gamma:real->B) u)` THEN CONJ_TAC THENL
     [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2B11_FLIM_RBALL THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`;
        `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `tau:num->real`;
        `q:num->B`; `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "fl" ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas' ((g':real->B->real^3^3)(&0)) gamma (&0) (&1)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->B)(&0) = xl`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->B)(&1) = y`)) THEN
    MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(exp(&4 * K * s)) * mfd_length atlas' ((g':real->B->real^3^3) s) gamma (&0) (&1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_METRIC_COMPARE THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_EXP_POS_LE; REAL_LT_IMP_LE]]);;

(* T911.B18 Assembly: MT Thm 9.11 (without the classification) from the    *)
(* route inputs, with the leaf in the corrected form; the route theorem.    *)

let P2B11_FLIM_P3_ON = prove
 (`!kappa top atlas (g:real->B->real^3^3) p (tau:num->real) (q:num->B)
    (top':B topology) atlas' g' xl W phi.
     p2b11_flim kappa (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> p3_flow_limit_on (\k. p2b_kview (top,atlas) g) q (\k. --(tau k)) (\k. inv(tau k))
                          {s | s < &1} (top',atlas') g' xl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b11_flim; p2c_flow_limit_with; p3_flow_limit_on] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->B`] THEN ASM_REWRITE_TAC[]);;

let P2B11_THM_9_11_CORE = prove
 (`!w:B->bool.
     P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     P2B_PROP_9_20_STATEMENT w w /\ P2B_SOLITON_FROM_LINF_FIX_STATEMENT w /\
     P2B_KSOL_DRDT_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
     P2C_PROP_5_14_STATEMENT w w
     ==> P2B_THM_9_11_STATEMENT w`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl4") (CONJUNCTS_THEN2 (LABEL_TAC "cor")
    (CONJUNCTS_THEN2 (LABEL_TAC "p920") (CONJUNCTS_THEN2 (LABEL_TAC "sol")
    (CONJUNCTS_THEN2 (LABEL_TAC "drdt") (CONJUNCTS_THEN2 (LABEL_TAC "ac")
    (LABEL_TAC "514"))))))) THEN
  REWRITE_TAC[P2B_THM_9_11_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p:B. p IN topspace top` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`) THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]
                P2B11_FLIM_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:num->real` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` (LABEL_TAC "flim"))))))))) THEN
  USE_THEN "flim" (STRIP_ASSUME_TAC o MATCH_MP P2B11_FLIM_FACTS) THEN
  USE_THEN "flim" (LABEL_TAC "sec" o MATCH_MP P2B11_FLIM_SEC) THEN
  USE_THEN "flim" (LABEL_TAC "rfo1" o MATCH_MP P2B11_FLIM_RFO1) THEN
  USE_THEN "flim" (LABEL_TAC "back" o MATCH_MP P2B11_FLIM_COMPLETE_BACK) THEN
  USE_THEN "flim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2b11_flim]) THEN
  (* complete slices for s < 1 *)
  SUBGOAL_THEN `!s. s < &1 ==> mfd_complete (top',atlas') ((g':real->B->real^3^3) s)`
  (LABEL_TAC "comp") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN ASM_CASES_TAC `s <= &0` THENL
     [USE_THEN "back" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2B11_FLIM_COMPLETE_FWD THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`;
        `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `tau:num->real`;
        `q:num->B`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Prop 9.20 *)
  USE_THEN "p920" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
    `tau:num->real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] o
    REWRITE_RULE[P2B_PROP_9_20_STATEMENT]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2bg_setup] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `linf:real->B->real`
    (X_CHOOSE_THEN `V:real` STRIP_ASSUME_TAC))) THEN
  (* the leaf *)
  USE_THEN "sol" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `linf:real->B->real`; `V:real`] o
    REWRITE_RULE[P2B_SOLITON_FROM_LINF_FIX_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
        NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "shr") (LABEL_TAC "nonflat")) THEN
  MAP_EVERY EXISTS_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `\s:real. (linf:real->B->real) (&1 - s)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[] THEN USE_THEN "shr" ACCEPT_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC P2B11_FLIM_P3_ON THEN
      MAP_EVERY EXISTS_TAC [`kappa:real`; `p:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      USE_THEN "flim" ACCEPT_TAC THEN NO_TAC) THEN
  REWRITE_TAC[p2b_ancflow0] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MP_TAC(ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`) THEN
      REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SIMP_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(MATCH_MP_TAC P2B11_FLIM_DRDS THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`;
        `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `tau:num->real`;
        `q:num->B`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MATCH_MP_TAC P2B11_FLIM_KNC THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `p:B`; `tau:num->real`; `q:num->B`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->B`] THEN
  CONJ_TAC THENL [USE_THEN "flim" ACCEPT_TAC; USE_THEN "comp" ACCEPT_TAC]);;

(* The route theorem.  The route statement takes the corrected leaf; the     *)
(* last step also accepts the original leaf input, which implies the        *)
(* corrected one (P2B_SOLITON_FROM_LINF_ORIG_IMP_FIX of pc_p2b_gaussreq).   *)

let P2B_THM_9_11_ROUTE = prove
 (`!w:B->bool. P2B_THM_9_11_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_THM_9_11_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2B11_THM_9_11_CORE THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC P2B_SOLITON_FROM_LINF_ORIG_IMP_FIX THEN ASM_REWRITE_TAC[]));;

