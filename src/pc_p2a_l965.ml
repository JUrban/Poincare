(* ========================================================================= *)
(* pc_p2a_l965: MT Lemma 9.65 (bounded curvature at bounded distance on      *)
(* 3-dimensional kappa-solutions) in route form, the statement               *)
(* P2B_LEMMA_9_65_ROUTE_STATEMENT (pc_p2b_chainstmts), on Tao's route        *)
(* (Prop 3.18.7 with Cor 3.18.6 = MT Cor 9.62, which argues at p             *)
(* itself and so covers compact kappa-solutions too).                        *)
(* S: limits of sequences of kappa-solutions rescaled at base points with    *)
(*    curvature bounds on balls of every radius (ANCIENT_COMPACT,            *)
(*    restriction to the joinable class, one limit on s <= 0).               *)
(* V: MT Cor 9.62: a ball with volume >= nu rho^3 has rho^2 R <= C on the    *)
(*    ball of radius A rho (point picking, Bishop-Gromov, S, THM_9_59).      *)
(* L: Lemma 9.65: collapse at fixed scales about p (V), the critical radius  *)
(*    r_k of the volume ratio (Bishop-Gromov monotonicity), the flat limit   *)
(*    (Thm 4.18 clause of SMP_SPLIT_PT) with Euclidean balls (FLAT_KNC)      *)
(*    against LIM_VOL.                                                       *)
(* ========================================================================= *)

needs "src/pc_p2a_asv.ml";;
needs "src/pc_p2b_x0.ml";;
needs "src/pc_p2b_flatknc.ml";;
needs "src/pc_lim_back.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The volume ratio of balls about a point is nonincreasing                 *)
(* (Bishop-Gromov), and the critical radius of a nonincreasing ratio (a     *)
(* supremum; no continuity in the radius needed).                           *)
(* ========================================================================= *)

let P2AL65_RATIO_MONO = prove
 (`!(w:B->bool) top atlas (g:B->real^3^3) x s t.
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g y u v) /\
     x IN topspace top /\ &0 < s /\ s <= t
     ==> mfd_volume (top,atlas) g (mfd_ball (top,atlas) g x t) / t pow 3 <=
         mfd_volume (top,atlas) g (mfd_ball (top,atlas) g x s) / s pow 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bg") STRIP_ASSUME_TAC) THEN
  USE_THEN "bg" (MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `x:B`;
     `s:real`; `t:real`;
     `mfd_volume (top,atlas) (g:B->real^3^3) (mfd_ball (top,atlas) g x s)`;
     `mfd_volume (top,atlas) (g:B->real^3^3) (mfd_ball (top,atlas) g x t)`] o
    REWRITE_RULE[P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MFD_HAS_VOLUME_BALL]; SIMP_TAC[]]);;

(* The critical radius: for a ratio nonincreasing on (0,inf) that is >= nu *)
(* somewhere and < nu at 1, the supremum r of the radii with ratio >= nu.  *)

let P2AL65_SUP_RADIUS = prove
 (`!(rat:real->real) nu s0.
     (!s t. &0 < s /\ s <= t ==> rat t <= rat s) /\
     &0 < s0 /\ nu <= rat s0 /\ rat (&1) < nu
     ==> ?r. &0 < r /\ r <= &1 /\
             (!s. &0 < s /\ s < r ==> nu <= rat s) /\
             (!s. r < s ==> rat s < nu)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mono") STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `S = {s:real | &0 < s /\ nu <= rat s}` THEN
  SUBGOAL_THEN `!s:real. s IN S <=> &0 < s /\ nu <= rat s` (LABEL_TAC "S") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real. s IN S ==> s < &1` (LABEL_TAC "lt1") THENL
   [X_GEN_TAC `s:real` THEN USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "mono" (MP_TAC o SPECL [`&1`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `s0:real` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `&1` THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "lt1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "up") (LABEL_TAC "least")) THEN
  SUBGOAL_THEN `&0 < sup(S:real->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "up" MATCH_MP_TAC THEN USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `sup(S:real->bool)` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "least" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "lt1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?s':real. s' IN S /\ s < s'` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `sup(S:real->bool) <= s` MP_TAC THENL
       [USE_THEN "least" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(s':real) IN S` THEN USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rat:real->real) s'` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real) IN S` MP_TAC THENL
     [USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> USE_THEN "up" (MP_TAC o C MATCH_MP th)) THEN
      ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* On a kappa-solution with dR/dt >= 0 (KSOL_DRDT) the scalar curvature     *)
(* at earlier times is at most its value at time 0 (P2BX0_SCALAR_MONO on    *)
(* (t-1,0) and the left limit at the final time from the smooth box of      *)
(* RFA_UPTO_BOX), hence abs Rm(t) <= R(0) / 2.                              *)
(* ========================================================================= *)

(* A lower bound on [t1,b) passes to the final time b of a flow smooth up   *)
(* to b.                                                                     *)

let P2AL65_UPTO_SCALAR_LEFT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a b x t1 c0.
     rfs_flow_upto (top,atlas) a b g /\ x IN topspace top /\ t1 < b /\
     (!t. t1 <= t /\ t < b ==> c0 <= mfd_scalar atlas (g t) x)
     ==> c0 <= mfd_scalar atlas (g b) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`] RFA_UPTO_BOX) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\p. lscalar ((Gb:real->real^3->real^3^3) (drop(fstcart p))) (sndcart p) - c0`;
                 `interval(lift(b - d),lift(b + d)) PCROSS ball(SND (c:(A->bool)#(A->real^3)) x,d)`;
                 `max t1 (b - d / &2)`; `b:real`; `SND (c:(A->bool)#(A->real^3)) x`]
                RFA_LEFT_LIMIT_NONNEG) THEN
  BETA_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [CONV_TAC(RATOR_CONV(RAND_CONV(REWRITE_CONV[o_DEF] THENC DEPTH_CONV BETA_CONV THENC
                                    REWRITE_CONV[LIFT_SUB]))) THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC LRG_LSMOOTH_LSCALAR THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t = metric_local atlas c ((g:real->A->real^3^3) t)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `c0 <= x ==> &0 <= x - c0`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (term_match [] `!t. t1 <= t /\ t < b
                                ==> c0 <= mfd_scalar atlas ((g:real->A->real^3^3) t) (x:A)`)
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "c" THEN REWRITE_TAC[mfd_scalar]];
    SUBGOAL_THEN `(Gb:real->real^3->real^3^3) b = metric_local atlas c ((g:real->A->real^3^3) b)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[GSYM mfd_scalar] THEN REAL_ARITH_TAC]);;

(* R(t) <= R(0) on a kappa-solution with dR/dt >= 0. *)

let P2AL65_KSOL_SCALAR_LE0 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) t x.
     P2B_KSOL_DRDT_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     t <= &0 /\ x IN topspace top
     ==> mfd_scalar atlas (g t) x <= mfd_scalar atlas (g(&0)) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `t = &0` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `t < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  SUBGOAL_THEN `rfs_flow_upto (top,atlas) (t - &1) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (t - &1) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  MATCH_MP_TAC P2AL65_UPTO_SCALAR_LEFT THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `t - &1`; `t:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX0_SCALAR_MONO THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `t - &1`; `&0`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `dR:real`] THEN STRIP_TAC THEN
  USE_THEN "drdt" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `g:real->B->real^3^3`] o
                   REWRITE_RULE[P2B_KSOL_DRDT_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`s:real`; `x:B`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* abs Rm at earlier times is at most R(0) / 2. *)

let P2AL65_KSOL_RM_LE0 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) t x.
     P2B_KSOL_DRDT_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     t <= &0 /\ x IN topspace top
     ==> mfd_rm_norm atlas (g t) x <= mfd_scalar atlas (g(&0)) x / &2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) t) x / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a / &2 <= b / &2`) THEN
    MATCH_MP_TAC P2AL65_KSOL_SCALAR_LE0 THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* S, part 1: the hypotheses of ANCIENT_COMPACT for a sequence of           *)
(* kappa-solutions rescaled by Q k at base points x k, from scalar bounds   *)
(* R <= CA Q k at time 0 on the balls of radius A / sqrt(Q k): abs          *)
(* Rm(s) <= R(0) / 2 (P2AL65_KSOL_RM_LE0) and kappa-noncollapsing at        *)
(* the scale r0 / sqrt(Q k), r0 = 1 / (1 + abs C1).                         *)
(* ========================================================================= *)

let P2AL65_SEQ_HYPS = prove
 (`!(w:B->bool) kappa (top:num->B topology) (atlas:num->((B->bool)#(B->real^3))->bool)
    (g:num->real->B->real^3^3) (x:num->B) (Q:num->real).
     P2B_KSOL_DRDT_STATEMENT w /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ x k IN topspace (top k) /\
          &0 < Q k) /\
     (!A. &0 < A
          ==> ?CA N. !k y. N <= k /\
                           y IN mfd_ball (top k,atlas k) (g k (&0)) (x k) (A * inv(sqrt(Q k)))
                           ==> mfd_scalar (atlas k) (g k (&0)) y <= CA * Q k)
     ==> (!k. hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
              (!a. a < &0 ==> rfs_flow_upto (top k,atlas k) a (&0) (g k)) /\
              (!t. t <= &0 ==> mfd_complete (top k,atlas k) (g k t)) /\
              x k IN topspace(top k) /\ &0 < Q k) /\
         (!A a. &0 < A /\ a < &0
                ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                                   y IN mfd_ball (top k,atlas k) (g k (&0)) (x k)
                                          (A * inv(sqrt(Q k)))
                                   ==> mfd_rm_norm (atlas k) (g k (s / Q k)) y <= CA * Q k) /\
         (?r0 kappa' N. &0 < r0 /\ &0 < kappa' /\
            !k. N <= k
                ==> ?v. mfd_has_volume (top k,atlas k) (g k (&0))
                          (mfd_ball (top k,atlas k) (g k (&0)) (x k) (r0 * inv(sqrt(Q k)))) v /\
                        kappa' * (r0 * inv(sqrt(Q k))) pow 3 <= v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") (CONJUNCTS_THEN2 (LABEL_TAC "ks")
    (LABEL_TAC "ball"))) THEN
  SUBGOAL_THEN
   `!k. hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
        (!a. a < &0 ==> rfs_flow_upto (top k,atlas k) a (&0) ((g:num->real->B->real^3^3) k)) /\
        (!t. t <= &0 ==> mfd_complete (top k,atlas k) (g k t)) /\
        x k IN topspace(top k) /\ &0 < Q k`
  (LABEL_TAC "basic") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "ks" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* abs Rm on the balls at all earlier times *)
  SUBGOAL_THEN
   `!A CA N k s y.
      (!k y. N <= k /\
             y IN mfd_ball (top k,atlas k) ((g:num->real->B->real^3^3) k (&0)) (x k)
                           (A * inv(sqrt(Q k)))
             ==> mfd_scalar (atlas k) (g k (&0)) y <= CA * Q k) /\
      N <= k /\ s <= &0 /\
      y IN mfd_ball (top k,atlas k) (g k (&0)) (x k) (A * inv(sqrt(Q k)))
      ==> mfd_rm_norm (atlas k) (g k s) y <= CA / &2 * Q k`
  (LABEL_TAC "rm") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:B) IN topspace(top(k:num))` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:B) IN mfd_ball (top(k:num),atlas k) ((g:num->real->B->real^3^3) k (&0))
                                       (x k) (A * inv(sqrt(Q k)))` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar (atlas(k:num)) ((g:num->real->B->real^3^3) k (&0)) y / &2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AL65_KSOL_RM_LE0 THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top(k:num):B topology`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "ks" (fun th -> REWRITE_TAC[th]);
      MATCH_MP_TAC(REAL_ARITH `a <= c * q ==> a / &2 <= c / &2 * q`) THEN
      USE_THEN "b" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "basic" ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`A:real`; `a:real`] THEN STRIP_TAC THEN
    USE_THEN "ball" (MP_TAC o SPEC `A:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `CA:real` (X_CHOOSE_TAC `N:num`)) THEN
    MAP_EVERY EXISTS_TAC [`CA / &2`; `N:num`] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y:B`] THEN STRIP_TAC THEN
    USE_THEN "rm" MATCH_MP_TAC THEN EXISTS_TAC `A:real` THEN EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < Q(k:num)` ASSUME_TAC THENL
     [USE_THEN "basic" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  (* noncollapsing at the base points *)
  USE_THEN "ball" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (X_CHOOSE_TAC `N:num`)) THEN
  MAP_EVERY EXISTS_TAC [`inv(&1 + abs C1)`; `kappa:real`; `N:num`] THEN
  SUBGOAL_THEN `&0 < kappa` ASSUME_TAC THENL
   [USE_THEN "ks" (MP_TAC o SPEC `0`) THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "basic" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
                 SPEC `k:num`) THEN
  ABBREV_TAC `r = inv(&1 + abs C1) * inv(sqrt(Q(k:num)))` THEN
  SUBGOAL_THEN `&0 < sqrt(Q(k:num))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ r <= &1 * inv(sqrt(Q(k:num))) /\
                C1 / &2 * Q k <= inv(r pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV; REAL_INV_MUL; REAL_INV_INV] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + abs C1` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&1 <= x /\ x <= x pow 2 ==> x <= x pow 2`) THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_kappa_noncollapsed"))
        (concl th) && is_forall (concl th))) THEN
  REWRITE_TAC[rfs_flow_view] THEN REWRITE_TAC[rfs_kappa_noncollapsed] THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `(x:num->B) k`; `r:real`]) THEN
  REWRITE_TAC[rfs_flow_view; rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 / &2 * Q(k:num)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "rm" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:B) IN mfd_ball (top(k:num),atlas k) ((g:num->real->B->real^3^3) k (&0))
                                  (x k) r` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Flow limits pass to further subsequences (the exhaustion, the times ts   *)
(* and the maps phi along sub).                                             *)
(* ========================================================================= *)

let P2AL65_REAL_MONO_SEQ = prove
 (`!ts:num->real. (!k. ts k <= ts (SUC k)) ==> !m n. m <= n ==> ts m <= ts n`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\m n:num. (ts:num->real) m <= ts n` TRANSITIVE_STEPWISE_LE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let P2AL65_P3_SUBSEQ = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl Tl (sub:num->num).
     p3_flow_limit V x t Q (top,atlas) g xl Tl /\ p3_subseq sub
     ==> p3_flow_limit (\k. V (sub k)) (x o sub) (t o sub) (Q o sub) (top,atlas) g xl Tl`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[p3_flow_limit] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX0_SUBSEQ_GE) THEN
  SUBGOAL_THEN `!k. SUC((sub:num->num) k) <= sub (SUC k)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LE_SUC_LT] THEN
    UNDISCH_TAC `p3_subseq (sub:num->num)` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. (W:num->B->bool) k SUBSET W (SUC k)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) k` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_EXHAUST_MONO) THEN
  SUBGOAL_THEN `!m n. m <= n ==> (ts:num->real) m <= ts n` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL65_REAL_MONO_SEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MAP_EVERY EXISTS_TAC [`(W:num->B->bool) o (sub:num->num)`; `(ts:num->real) o (sub:num->num)`;
                        `(phi:num->B->A) o (sub:num->num)`] THEN
  REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(W:num->B->bool) (SUC((sub:num->num) k))` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN X_GEN_TAC `y:B` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:B->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `k:num`) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      DISCH_TAC THEN
      SUBGOAL_THEN `(y:B) IN UNIONS {(W:num->B->bool) k | k IN (:num)}` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:B->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `k:num`) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      EXISTS_TAC `(W:num->B->bool) ((sub:num->num) k)` THEN
      CONJ_TAC THENL [EXISTS_TAC `k:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET]];
    X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `SUC((sub:num->num) k)` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Tl:real`)) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "ts")) (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(ts:num->real) k` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`; `a:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`; `a:real`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* S, part 2: existence of the limit.  The kviews of the kappa-solutions    *)
(* rescaled by Q k at x k converge (along a subsequence) for every Tl       *)
(* (ANCIENT_COMPACT with P2AL65_SEQ_HYPS); each per-Tl limit is restricted  *)
(* to the joinable class of xl (P2CO_P3_FLOW_RESTRICT, connected); one      *)
(* limit on s <= 0 by P2BX0_FLOW_LIMIT_DIAG.  Model: P2BX0_LIMIT_EXISTS     *)
(* of pc_p2b_x0 (one flow with moving points); here a sequence of           *)
(* manifolds.                                                               *)
(* ========================================================================= *)

let P2AL65_SEQ_LIMIT_EXISTS = prove
 (`!(w:B->bool) kappa (top:num->B topology) (atlas:num->((B->bool)#(B->real^3))->bool)
    (g:num->real->B->real^3^3) (x:num->B) (Q:num->real).
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ x k IN topspace (top k) /\
          &0 < Q k) /\
     (!A. &0 < A
          ==> ?CA N. !k y. N <= k /\
                           y IN mfd_ball (top k,atlas k) (g k (&0)) (x k) (A * inv(sqrt(Q k)))
                           ==> mfd_scalar (atlas k) (g k (&0)) y <= CA * Q k)
     ==> ?sub (top':B topology) atlas' g' xl W phi.
            p3_subseq sub /\
            p2c_flow_limit_with (\k. p2b_kview (top (sub k),atlas (sub k)) (g (sub k)))
                                (x o sub) (\k. &0) (Q o sub) {s | s <= &0}
                                (top',atlas') g' xl W phi /\
            connected_space top' /\
            (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
            (!s. s <= &0 ==> riemannian_metric atlas' (g' s)) /\
            mfd_complete (top',atlas') (g'(&0)) /\
            (!Tl. &0 < Tl
                  ==> p3_flow_limit (\k. p2b_kview (top (sub k),atlas (sub k)) (g (sub k)))
                                    (x o sub) (\k. &0) (Q o sub) (top',atlas') g' xl Tl)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "AC") (CONJUNCTS_THEN2 (LABEL_TAC "drdt")
    (CONJUNCTS_THEN2 (LABEL_TAC "ks") (LABEL_TAC "ball")))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `x:num->B`; `Q:num->real`] P2AL65_SEQ_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "hyps")] THEN
  USE_THEN "AC" (MP_TAC o REWRITE_RULE[P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                             `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`]) THEN
  ANTS_TAC THENL [USE_THEN "hyps" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top1:B topology`
    (X_CHOOSE_THEN `atlas1:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g1:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim1")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem1") (LABEL_TAC "comp1"))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top1:B topology) (atlas1:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "lim1" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the views are regular *)
  SUBGOAL_THEN
   `!n s. ~(topspace(rfs_vtop (rfs_flow_view (top ((sub1:num->num) n),atlas (sub1 n))
                                              {t | t <= &0}
                                              ((g:num->real->B->real^3^3) (sub1 n))) s) = {})
          ==> smooth_manifold_atlas
                (rfs_vtop (rfs_flow_view (top (sub1 n),atlas (sub1 n)) {t | t <= &0}
                                         (g (sub1 n))) s)
                (rfs_vatlas (rfs_flow_view (top (sub1 n),atlas (sub1 n)) {t | t <= &0}
                                           (g (sub1 n))) s) /\
              riemannian_metric
                (rfs_vatlas (rfs_flow_view (top (sub1 n),atlas (sub1 n)) {t | t <= &0}
                                           (g (sub1 n))) s)
                (rfs_vmetric (rfs_flow_view (top (sub1 n),atlas (sub1 n)) {t | t <= &0}
                                            (g (sub1 n))) s)`
  (LABEL_TAC "reg") THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top((sub1:num->num) n):B topology`;
                   `atlas((sub1:num->num) n):((B->bool)#(B->real^3))->bool`;
                   `{t:real | t <= &0}`; `(g:num->real->B->real^3^3) ((sub1:num->num) n)`]
                  P2BX0_VIEW_REGULAR) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "ks" (MP_TAC o SPEC `(sub1:num->num) n`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* restriction of every per-Tl limit to the joinable class of xl *)
  SUBGOAL_THEN
   `(!Tl. &0 < Tl
          ==> p3_flow_limit
                (\k:num. rfs_flow_view (top ((sub1:num->num) k),atlas (sub1 k)) {t | t <= &0}
                                       ((g:num->real->B->real^3^3) (sub1 k)))
                ((x:num->B) o sub1) (\k. &0) ((Q:num->real) o sub1)
                (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
                 restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
                (\s. restrict_metric atlas1 {y | mfd_joinable (top1,atlas1) xl y}
                                     ((g1:real->B->real^3^3) s)) xl Tl) /\
    connected_space
      (subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y})`
  (CONJUNCTS_THEN2 (LABEL_TAC "rlim") ASSUME_TAC) THENL
   [CONJ_TAC THENL [X_GEN_TAC `Tl:real` THEN DISCH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\k:num. rfs_flow_view (top ((sub1:num->num) k),atlas (sub1 k)) {t | t <= &0}
                             ((g:num->real->B->real^3^3) (sub1 k))`;
      `(x:num->B) o (sub1:num->num)`; `\k:num. &0`; `(Q:num->real) o (sub1:num->num)`;
      `top1:B topology`; `atlas1:((B->bool)#(B->real^3))->bool`; `g1:real->B->real^3^3`; `xl:B`]
     P2CO_P3_FLOW_RESTRICT) THENL
     [DISCH_THEN(MP_TAC o SPEC `Tl:real`); DISCH_THEN(MP_TAC o SPEC `&1`)] THEN
    BETA_TAC THEN REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [CONJ_TAC THENL
        [USE_THEN "reg" ACCEPT_TAC;
         USE_THEN "lim1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_01]];
       SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < &0
        ==> rfs_flow_upto
              (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
               restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y}) a (&0)
              (\s. restrict_metric atlas1
                     {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                     ((g1:real->B->real^3^3) s))`
  (LABEL_TAC "upto") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rlim" (MP_TAC o SPEC `&1 - a`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p3_flow_limit] THEN
    DISCH_THEN(MP_TAC o el 5 o CONJUNCTS) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s <= &0
        ==> riemannian_metric
              (restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
              (restrict_metric atlas1
                 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                 ((g1:real->B->real^3^3) s))`
  (LABEL_TAC "riem") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `s - &1`; `&0`;
      `\s. restrict_metric atlas1
             {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
             ((g1:real->B->real^3^3) s)`;
      `s:real`] P2AP_UPTO_RIEM) THEN
    REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_complete (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
                  restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
                 (restrict_metric atlas1
                    {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                    ((g1:real->B->real^3^3) (&0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CO_CLASS_COMPLETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* one limit on s <= 0 *)
  MP_TAC(ISPECL
   [`\k:num. rfs_flow_view (top ((sub1:num->num) k),atlas (sub1 k)) {t | t <= &0}
                           ((g:num->real->B->real^3^3) (sub1 k))`;
    `(x:num->B) o (sub1:num->num)`; `\k:num. &0`; `(Q:num->real) o (sub1:num->num)`;
    `subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`] P2BX0_FLOW_LIMIT_DIAG) THEN
  ANTS_TAC THENL [USE_THEN "rlim" ACCEPT_TAC; ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `W:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->B` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "with"))))) THEN
  SUBGOAL_THEN `(\k:num. &0) o (sub2:num->num) = (\k. &0)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  (* the per-Tl limits along the composed subsequence *)
  SUBGOAL_THEN
   `!Tl. &0 < Tl
         ==> p3_flow_limit
               (\k. p2b_kview (top (((sub1:num->num) o (sub2:num->num)) k),
                               atlas ((sub1 o sub2) k))
                              ((g:num->real->B->real^3^3) ((sub1 o sub2) k)))
               ((x:num->B) o (sub1 o sub2)) (\k. &0) ((Q:num->real) o (sub1 o sub2))
               (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
                restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
               (\s. restrict_metric atlas1
                      {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                      ((g1:real->B->real^3^3) s)) xl Tl`
  (LABEL_TAC "p3") THENL
   [X_GEN_TAC `Tl:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\k:num. rfs_flow_view (top ((sub1:num->num) k),atlas (sub1 k)) {t | t <= &0}
                             ((g:num->real->B->real^3^3) (sub1 k))`;
      `(x:num->B) o (sub1:num->num)`; `\k:num. &0`; `(Q:num->real) o (sub1:num->num)`;
      `subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `\s. restrict_metric atlas1
             {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
             ((g1:real->B->real^3^3) s)`;
      `xl:B`; `Tl:real`; `sub2:num->num`] P2AL65_P3_SUBSEQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rlim" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    BETA_TAC THEN REWRITE_TAC[p2b_kview; o_THM; o_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(sub1:num->num) o (sub2:num->num)` THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "with" MP_TAC THEN ASM_REWRITE_TAC[p2b_kview; o_THM; o_ASSOC];
    ASM_REWRITE_TAC[];
    USE_THEN "upto" ACCEPT_TAC;
    BETA_TAC THEN USE_THEN "riem" ACCEPT_TAC;
    BETA_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "p3" ACCEPT_TAC]);;

(* ========================================================================= *)
(* S, part 3: the limit data p2al65_slim (the subsequence already applied)  *)
(* and its properties: basic facts, sec >= 0 (LIM_CURV), complete slices    *)
(* (LIM_FLOW_COMPLETE_BACK), kappa-noncollapsing (LIM_KNC), p2b_ksep        *)
(* (P2B_KSEP_LIMIT), convergence of the rescaled scalar curvature at every  *)
(* point (LIM_CURV), points of the limit ball B'(xl,A) eventually in the    *)
(* balls B(x k, A / sqrt(Q k)) (LIM_DIST), and the local scalar bounds in   *)
(* the limit.  Model: the P2BX0_XLIM_ lemmas of pc_p2b_x0.                  *)
(* ========================================================================= *)

let p2al65_slim = new_definition
 `p2al65_slim kappa (top:num->B topology) (atlas:num->((B->bool)#(B->real^3))->bool)
              (g:num->real->B->real^3^3) (x:num->B) (Q:num->real)
              (top':B topology,atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
              (xl:B) (W:num->B->bool) (phi:num->B->B) <=>
    (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
         x k IN topspace (top k) /\ &0 < Q k) /\
    p2c_flow_limit_with (\k. p2b_kview (top k,atlas k) (g k)) x (\k. &0) Q {s | s <= &0}
                        (top',atlas') g' xl W phi /\
    connected_space top' /\
    (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
    (!s. s <= &0 ==> riemannian_metric atlas' (g' s)) /\
    mfd_complete (top',atlas') (g'(&0))`;;

let P2AL65_SLIM_EXISTS = prove
 (`!(w:B->bool) kappa (top:num->B topology) (atlas:num->((B->bool)#(B->real^3))->bool)
    (g:num->real->B->real^3^3) (x:num->B) (Q:num->real).
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
          x k IN topspace (top k) /\ &0 < Q k) /\
     (!A. &0 < A
          ==> ?CA N. !k y. N <= k /\
                           y IN mfd_ball (top k,atlas k) (g k (&0)) (x k) (A * inv(sqrt(Q k)))
                           ==> mfd_scalar (atlas k) (g k (&0)) y <= CA * Q k)
     ==> ?sub (top':B topology) atlas' g' xl W phi.
            p3_subseq sub /\
            p2al65_slim kappa (top o sub) (atlas o sub) (g o sub) (x o sub) (Q o sub)
                        (top',atlas') g' xl W phi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ks") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `x:num->B`; `Q:num->real`] P2AL65_SEQ_LIMIT_EXISTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[p2al65_slim; o_THM]);;

(* The same, with the per-Tl flow limits along the subsequence (the form of *)
(* the conclusion of MT Thm 9.64).                                          *)

let P2AL65_SLIM_EXISTS_P3 = prove
 (`!(w:B->bool) kappa (top:num->B topology) (atlas:num->((B->bool)#(B->real^3))->bool)
    (g:num->real->B->real^3^3) (x:num->B) (Q:num->real).
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
          x k IN topspace (top k) /\ &0 < Q k) /\
     (!A. &0 < A
          ==> ?CA N. !k y. N <= k /\
                           y IN mfd_ball (top k,atlas k) (g k (&0)) (x k) (A * inv(sqrt(Q k)))
                           ==> mfd_scalar (atlas k) (g k (&0)) y <= CA * Q k)
     ==> ?sub (top':B topology) atlas' g' xl W phi.
            p3_subseq sub /\
            p2al65_slim kappa (top o sub) (atlas o sub) (g o sub) (x o sub) (Q o sub)
                        (top',atlas') g' xl W phi /\
            (!Tl. &0 < Tl
                  ==> p3_flow_limit (\k. p2b_kview (top (sub k),atlas (sub k)) (g (sub k)))
                                    (x o sub) (\k. &0) (Q o sub) (top',atlas') g' xl Tl)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ks") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `x:num->B`; `Q:num->real`] P2AL65_SEQ_LIMIT_EXISTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[p2al65_slim; o_THM]);;

(* Basic facts. *)

let P2AL65_SLIM_BASIC = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi
     ==> hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ xl IN topspace top' /\
         (!k. (phi:num->B->B) k xl = x k) /\
         (!n s. ~(topspace(rfs_vtop (p2b_kview (top n,atlas n) (g n)) s) = {})
                ==> smooth_manifold_atlas (rfs_vtop (p2b_kview (top n,atlas n) (g n)) s)
                                          (rfs_vatlas (p2b_kview (top n,atlas n) (g n)) s) /\
                    riemannian_metric (rfs_vatlas (p2b_kview (top n,atlas n) (g n)) s)
                                      (rfs_vmetric (p2b_kview (top n,atlas n) (g n)) s)) /\
         (!k tau. hausdorff_space (rfs_vtop (p2b_kview (top k,atlas k) (g k)) tau)) /\
         (!k s. s <= &0
                ==> rfs_vtop (p2b_kview (top k,atlas k) (g k)) s = top k /\
                    rfs_vatlas (p2b_kview (top k,atlas k) (g k)) s = atlas k /\
                    rfs_vmetric (p2b_kview (top k,atlas k) (g k)) s = g k s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2al65_slim] THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (top':B topology) /\
                smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
                (xl:B) IN topspace top' /\ (!k. (phi:num->B->B) k xl = x k)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th))) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS o CONJUNCT1) THEN
    REWRITE_TAC[p2b_kview] THEN MATCH_MP_TAC P2BX0_VIEW_REGULAR THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th))) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS o CONJUNCT1) THEN
    REWRITE_TAC[p2b_kview] THEN MATCH_MP_TAC P2BX0_VIEW_HAUSDORFF THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AK0_KVIEW_SLICE THEN
    ASM_REWRITE_TAC[]]);;

(* sec >= 0 on the limit. *)

let P2AL65_SLIM_SEC = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi
     ==> !s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional atlas' (g' s) y u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[LIM_CURV_STATEMENT] (ISPECL [`(:B)`; `(:B)`] LIM_CURV)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
    `x:num->B`; `\k:num. &0`; `Q:num->real`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`; `y:B`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `0` THEN MAP_EVERY X_GEN_TAC [`k:num`; `z:B`; `u':real^3`; `v':real^3`] THEN
    REWRITE_TAC[REAL_ADD_LID] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s / Q(k:num) <= &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th))) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:B) IN topspace (rfs_vtop (p2b_kview ((top:num->B topology) k,atlas k)
                                    ((g:num->real->B->real^3^3) k)) (s / Q k))` THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th))) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Complete slices for all s <= 0. *)

let P2AL65_SLIM_COMPLETE = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi
     ==> !s. s <= &0 ==> mfd_complete (top',atlas') (g' s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_SEC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[LIM_FLOW_COMPLETE_BACK_STATEMENT] (ISPEC `(:B)` LIM_FLOW_COMPLETE_BACK)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `g':real->B->real^3^3`; `s - &1`; `&0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* kappa-noncollapsing of the limit at all scales. *)

let P2AL65_SLIM_KNC = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi
     ==> !r0. rfs_kappa_noncollapsed (p2b_kview (top',atlas') g') kappa r0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_COMPLETE th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  X_GEN_TAC `r0:real` THEN REWRITE_TAC[p2b_kview] THEN
  MP_TAC(REWRITE_RULE[LIM_KNC_STATEMENT] (ISPECL [`(:B)`; `(:B)`] LIM_KNC)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
    `x:num->B`; `\k:num. &0`; `Q:num->real`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `kappa:real`;
    `r0:real`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th))) THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol; p2b_kview] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* p2b_ksep of the limit. *)

let P2AL65_SLIM_KSEP = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi
     ==> p2b_ksep top' atlas'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[p2al65_slim]) THEN
  MP_TAC(REWRITE_RULE[P2B_KSEP_LIMIT_STATEMENT] (ISPEC `(:B)` P2B_KSEP_LIMIT)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                        `g:num->real->B->real^3^3`; `x:num->B`; `\k:num. &0`; `Q:num->real`;
                        `g':real->B->real^3^3`; `xl:B`; `{s:real | s <= &0}`] THEN
  REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th))) THEN
    STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->B`] THEN ASM_REWRITE_TAC[]]);;

(* The rescaled scalar curvature converges at every point of the limit. *)

let P2AL65_SLIM_SCALAR = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi
    s y.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi /\ s <= &0 /\
     y IN topspace top'
     ==> ((\k. mfd_scalar (atlas k) (g k (s / Q k)) ((phi:num->B->B) k y) / Q k) --->
          mfd_scalar atlas' (g' s) y) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) STRIP_ASSUME_TAC) THEN
  MP_TAC(REWRITE_RULE[LIM_CURV_STATEMENT] (ISPECL [`(:B)`; `(:B)`] LIM_CURV)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
    `x:num->B`; `\k:num. &0`; `Q:num->real`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`; `y:B`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vatlas; rfs_vmetric; REAL_ADD_LID]);;

(* Points of the limit are eventually at rescaled distance close to their   *)
(* limit distance from the base points (LIM_DIST on the pair xl, y at s = 0).*)

let P2AL65_SLIM_NEAR = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi
    y e.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi /\ y IN topspace top' /\
     &0 < e
     ==> ?k0. !k. k0 <= k
                  ==> (phi:num->B->B) k y IN topspace (top k) /\
                      mfd_joinable (top k,atlas k) (x k) (phi k y) /\
                      abs(sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (x k) (phi k y) -
                          mfd_dist (top',atlas') (g'(&0)) xl y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) STRIP_ASSUME_TAC) THEN
  MP_TAC(REWRITE_RULE[LIM_DIST_STATEMENT] (ISPECL [`(:B)`; `(:B)`] LIM_DIST)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
    `x:num->B`; `\k:num. &0`; `Q:num->real`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`;
    `{xl:B,y}`; `e:real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; REAL_ARITH `!x:real. &0 / x = &0`; REAL_ADD_RID] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_THEN(LABEL_TAC "d") THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REMOVE_THEN "d" (MP_TAC o SPECL [`k:num`; `xl:B`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[]);;

(* Local scalar bounds pass to the limit. *)

let P2AL65_SLIM_LOCAL = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q
    top' atlas' g' xl W phi A CA N.
     P2B_KSOL_DRDT_STATEMENT w /\
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi /\ &0 < A /\
     (!k y. N <= k /\ y IN mfd_ball (top k,atlas k) (g k (&0)) (x k) (A * inv(sqrt(Q k)))
            ==> mfd_scalar (atlas k) (g k (&0)) y <= CA * Q k)
     ==> !s y. s <= &0 /\ y IN mfd_ball (top',atlas') (g'(&0)) xl A
               ==> mfd_scalar atlas' (g' s) y <= CA`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "balls")))) THEN
  USE_THEN "sl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                 `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `y:B`;
                 `A - mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl y`]
                P2AL65_SLIM_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "near")) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                 `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `s:real`; `y:B`] P2AL65_SLIM_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\k. mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (s / Q k))
                             ((phi:num->B->B) k y) / Q k` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `k0 + N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "near" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(Q(k:num))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s / Q(k:num) <= &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((phi:num->B->B) k y) <=
    CA * Q(k:num)`
  ASSUME_TAC THENL
   [USE_THEN "balls" MATCH_MP_TAC THEN
    CONJ_TAC THENL [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    UNDISCH_TAC `abs(sqrt(Q(k:num)) *
                     mfd_dist (top k,atlas k) ((g:num->real->B->real^3^3) k (&0)) (x k)
                              ((phi:num->B->B) k y) -
                     mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl y) <
                 A - mfd_dist (top',atlas') (g'(&0)) xl y` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (s / Q k)) ((phi:num->B->B) k y) <=
    mfd_scalar (atlas k) (g k (&0)) (phi k y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL65_KSOL_SCALAR_LE0 THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* V, part 1: point picking at time 0 of a kappa-solution (P2BX0_POINT_PICK *)
(* for R), Bishop-Gromov noncollapsing at the picked point, and arithmetic. *)
(* ========================================================================= *)

let P2AL65_PICK = prove
 (`!kappa top atlas (g:real->B->real^3^3) y rho.
     p2b_kappa_solution kappa (top,atlas) g /\ y IN topspace top /\ &0 < rho /\
     &0 < mfd_scalar atlas (g(&0)) y
     ==> ?q s. &0 < s /\ s <= rho / &2 /\ q IN topspace top /\
               mfd_joinable (top,atlas) y q /\ mfd_dist (top,atlas) (g(&0)) y q < rho /\
               mfd_scalar atlas (g(&0)) y <= mfd_scalar atlas (g(&0)) q /\
               rho pow 2 * mfd_scalar atlas (g(&0)) y <=
               &4 * s pow 2 * mfd_scalar atlas (g(&0)) q /\
               (!z. z IN mfd_ball (top,atlas) (g(&0)) q s
                    ==> mfd_scalar atlas (g(&0)) z <= &4 * mfd_scalar atlas (g(&0)) q)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `mfd_scalar atlas ((g:real->B->real^3^3)(&0))`;
                 `y:B`; `rho:real`] P2BX0_POINT_PICK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:B` THEN DISCH_TAC THEN MATCH_MP_TAC P2AV9_KSOL_SCALAR THEN
      MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:B` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`q:B`; `(rho - mfd_dist (top,atlas) ((g:real->B->real^3^3)(&0)) y q) / &2`] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3)(&0)) y q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `(rho - mfd_dist (top,atlas) ((g:real->B->real^3^3)(&0)) y q) pow 2`))
          (concl th))) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_FIELD;
    X_GEN_TAC `z:B` THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The arithmetic of Bishop-Gromov noncollapsing at the picked point. *)

let P2AL65_ARITH_BG = prove
 (`!nu L rho s V1 V2.
     &0 < s /\ &0 < L /\ &0 < rho /\ nu * rho pow 3 <= V2 /\
     V2 / (L * rho) pow 3 <= V1 / s pow 3
     ==> nu / L pow 3 * s pow 3 <= V1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s pow 3 /\ &0 < (L * rho) pow 3 /\ &0 < L pow 3 /\ &0 < rho pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `nu / L pow 3 <= V2 / (L * rho) pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `nu / L pow 3 * (L * rho) pow 3 = nu * rho pow 3` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN UNDISCH_TAC `&0 < L pow 3` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `nu / L pow 3 <= V1 / s pow 3` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]);;

(* Bishop-Gromov noncollapsing at a point q near x0 at time 0. *)

let P2AL65_BG_NC = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) x0 q rho v nu A s.
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     x0 IN topspace top /\ q IN topspace top /\ &0 < rho /\ &0 <= A /\
     mfd_dist (top,atlas) (g(&0)) x0 q < (A + &1) * rho /\
     mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) x0 rho) v /\
     nu * rho pow 3 <= v /\ &0 < s /\ s <= (A + &2) * rho
     ==> nu / (A + &2) pow 3 * s pow 3 <=
         mfd_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) q s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bg") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(&0)) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3)(&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) x0 rho SUBSET
    mfd_ball (top,atlas) (g(&0)) q ((A + &2) * rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (q:B) z /\
                  mfd_joinable (top,atlas) q x0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`; `q:B`; `x0:B`; `z:B`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`; `q:B`; `x0:B`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `q:B`; `(A + &2) * rho`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `v <= mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                    (mfd_ball (top,atlas) (g(&0)) q ((A + &2) * rho))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) x0 rho`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) q ((A + &2) * rho)`;
                   `v:real`;
                   `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                               (mfd_ball (top,atlas) (g(&0)) q ((A + &2) * rho))`]
                  MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `q:B`; `s:real`; `(A + &2) * rho`]
                P2AL65_RATIO_MONO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC P2AL65_ARITH_BG THEN
  MAP_EVERY EXISTS_TAC [`rho:real`;
    `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                (mfd_ball (top,atlas) (g(&0)) q ((A + &2) * rho))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* A cube eventually exceeds any constant. *)

let P2AL65_CUBE_CONTRA = prove
 (`!e b c. &0 < e ==> ?R. c <= R /\ &0 < R /\ b < e * R pow 3`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `&1 + abs c + abs b / e` THEN
  ABBREV_TAC `R = &1 + abs c + abs b / e` THEN
  SUBGOAL_THEN `&0 <= abs b / e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= R` ASSUME_TAC THENL [EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs b < e * R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
    SUBGOAL_THEN `e * abs b / e = abs b` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ &0 <= e * abs c ==> abs b < e + e * abs c + abs b`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e * R <= e * R pow 3` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `R pow 3 = R * R pow 2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* V, part 2: the limit of picked points is a kappa-solution (R' <= 4 from   *)
(* the picked balls, R'(xl,0) = 1, abs Rm' <= 2, R' > 0 at all times         *)
(* by P2BX0_SCALAR_POS_ALL); positive asymptotic volume in the limit         *)
(* (LIM_VOL); the contradiction with THM_9_59 or with a finite total volume. *)
(* ========================================================================= *)

let P2AL65_LIM_KSOL = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q
    top' atlas' g' xl W phi.
     P2B_KSOL_DRDT_STATEMENT w /\
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi /\
     (!k. mfd_scalar (atlas k) (g k (&0)) (x k) = Q k) /\
     (!A. &0 < A
          ==> ?N. !k y. N <= k /\
                        y IN mfd_ball (top k,atlas k) (g k (&0)) (x k) (A * inv(sqrt(Q k)))
                        ==> mfd_scalar (atlas k) (g k (&0)) y <= &4 * Q k)
     ==> p2b_kappa_solution kappa (top',atlas') g' /\ p2b_ksep top' atlas'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 (LABEL_TAC "Rx") (LABEL_TAC "balls")))) THEN
  USE_THEN "sl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_SEC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_COMPLETE th) THEN
    ASSUME_TAC(REWRITE_RULE[p2b_kview] (MATCH_MP P2AL65_SLIM_KNC th)) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_KSEP th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  (* R' <= 4 *)
  SUBGOAL_THEN `!s y. s <= &0 /\ y IN topspace top'
                      ==> mfd_scalar atlas' ((g':real->B->real^3^3) s) y <= &4`
  (LABEL_TAC "R4") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top',atlas':((B->bool)#(B->real^3))->bool) xl y` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_dist (top',atlas') ((g':real->B->real^3^3)(&0)) xl y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `A = mfd_dist (top',atlas') ((g':real->B->real^3^3)(&0)) xl y + &1` THEN
    USE_THEN "balls" (MP_TAC o SPEC `A:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
    MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                   `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                   `x:num->B`; `Q:num->real`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->B`; `A:real`; `&4`; `N:num`]
                  P2AL65_SLIM_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* R'(xl,0) = 1 *)
  SUBGOAL_THEN `mfd_scalar atlas' ((g':real->B->real^3^3)(&0)) xl = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                   `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`] P2AL65_SLIM_SCALAR) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `!x:real. &0 / x = &0`] THEN
    SUBGOAL_THEN `(\k. (Q:num->real) k / Q k) = (\k. &1)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN MATCH_MP_TAC REAL_DIV_REFL THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th) &&
        is_forall(concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REALLIM_CONST_EQ; TRIVIAL_LIMIT_SEQUENTIALLY] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* abs Rm' <= 2 *)
  SUBGOAL_THEN `!s y. s <= &0 /\ y IN topspace top'
                      ==> mfd_rm_norm atlas' ((g':real->B->real^3^3) s) y <= &2`
  (LABEL_TAC "rm2") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas' ((g':real->B->real^3^3) s) y / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top':B topology` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH `a <= &4 ==> a / &2 <= &2`) THEN
      USE_THEN "R4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* R' > 0 at all times *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `&2`] P2BX0_SCALAR_POS_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < kappa` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th) &&
      is_forall(concl th))) THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXISTS_TAC `&2` THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN USE_THEN "rm2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) t`; `xl:B`] P2AU_MFD_SCALAR_ABS_3) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas' ((g':real->B->real^3^3) t) xl` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN EXISTS_TAC `&2` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:B`] THEN STRIP_TAC THEN
    USE_THEN "rm2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Rescaling arithmetic: Q sqrt(Q) nu (R0 / sqrt Q)^3 = nu R0^3. *)

let P2AL65_ARITH_SCALE = prove
 (`!Q nu R0 vk v.
     &0 < Q /\ nu * (R0 * inv(sqrt Q)) pow 3 <= vk /\ Q * sqrt Q * vk <= v + &1
     ==> nu * R0 pow 3 - &1 <= v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Q /\ sqrt Q pow 2 = Q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q * sqrt Q) * (nu * (R0 * inv(sqrt Q)) pow 3) = nu * R0 pow 3` ASSUME_TAC THENL
   [UNDISCH_TAC `sqrt Q pow 2 = Q` THEN UNDISCH_TAC `&0 < sqrt Q` THEN UNDISCH_TAC `&0 < Q` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q * sqrt Q) * (nu * (R0 * inv(sqrt Q)) pow 3) <= (Q * sqrt Q) * vk` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Volumes of limit balls B(xl, 2 R0) from noncollapsing of the sequence at *)
(* the scales R0 / sqrt(Q k) (LIM_VOL, first inequality, e = 1).            *)

let P2AL65_LIM_VOLUME = prove
 (`!kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q top' atlas' g' xl W phi nu.
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi /\
     (!R0. &0 < R0
           ==> ?N. !k v. N <= k /\
                         mfd_has_volume (top k,atlas k) (g k (&0))
                           (mfd_ball (top k,atlas k) (g k (&0)) (x k) (R0 * inv(sqrt(Q k)))) v
                         ==> nu * (R0 * inv(sqrt(Q k))) pow 3 <= v)
     ==> !R0 v. &0 < R0 /\
                mfd_has_volume (top',atlas') (g'(&0))
                  (mfd_ball (top',atlas') (g'(&0)) xl (&2 * R0)) v
                ==> nu * R0 pow 3 - &1 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sl") (LABEL_TAC "nc")) THEN
  USE_THEN "sl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  MAP_EVERY X_GEN_TAC [`R0:real`; `v:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&0)`; `xl:B`; `R0:real`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(REWRITE_RULE[LIM_VOL_STATEMENT] (ISPECL [`(:B)`; `(:B)`] LIM_VOL)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
    `x:num->B`; `\k:num. &0`; `Q:num->real`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`;
    `R0:real`; `&2 * R0`;
    `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0)) (mfd_ball (top',atlas') (g'(&0)) xl R0)`;
    `v:real`; `&1`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL; REAL_LT_01] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!x:real. &0 / x = &0`; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  USE_THEN "nc" (MP_TAC o SPEC `R0:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k0 + N:num` o check (fun th ->
    can (find_term ((=) `k0:num`)) (concl th))) THEN
  REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `vk1:real` (X_CHOOSE_THEN `vk2:real` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC P2AL65_ARITH_SCALE THEN
  MAP_EVERY EXISTS_TAC [`(Q:num->real)(k0 + N)`; `vk1:real`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `N:num`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Positive asymptotic volume contradicts THM_9_59 (or a finite total      *)
(* volume in the compact case).                                             *)

let P2AL65_AVR_CONTRA = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) xl nu.
     P2B_THM_9_59_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ xl IN topspace top /\
     &0 < nu /\
     (!R0 v. &0 < R0 /\
             mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) xl (&2 * R0)) v
             ==> nu * R0 pow 3 - &1 <= v)
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t959") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `compact_space (top:B topology)` THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`; `topspace top:B->bool`]
                  MFD_HAS_VOLUME_COMPACT) THEN
    ASM_REWRITE_TAC[GSYM compact_space] THEN DISCH_THEN(X_CHOOSE_TAC `V:real`) THEN
    MP_TAC(SPECL [`nu:real`; `V + &1`; `&0`] P2AL65_CUBE_CONTRA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`; `xl:B`; `&2 * R`] MFD_HAS_VOLUME_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    USE_THEN "low" (MP_TAC o SPECL [`R:real`;
      `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                  (mfd_ball (top,atlas) (g(&0)) xl (&2 * R))`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) xl (&2 * R)`;
                   `topspace top:B->bool`;
                   `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                               (mfd_ball (top,atlas) (g(&0)) xl (&2 * R))`;
                   `V:real`] MFD_HAS_VOLUME_MONO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "t959" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `g:real->B->real^3^3`; `xl:B`; `nu / &16`] o
                   REWRITE_RULE[P2B_THM_9_59_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (LABEL_TAC "up")) THEN
  MP_TAC(SPECL [`nu / &2`; `&1`; `r0 / &2`] P2AL65_CUBE_CONTRA) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `xl:B`; `&2 * R`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "low" (MP_TAC o SPECL [`R:real`;
    `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                (mfd_ball (top,atlas) (g(&0)) xl (&2 * R))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "up" (MP_TAC o SPECL [`&2 * R`;
    `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                (mfd_ball (top,atlas) (g(&0)) xl (&2 * R))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&1 < nu / &2 * R pow 3` THEN
  UNDISCH_TAC `nu * R pow 3 - &1 <=
               mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                          (mfd_ball (top,atlas) (g(&0)) xl (&2 * R))` THEN
  REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* V, part 3: MT Cor 9.62 in the form of Tao's Cor 3.18.6: a ball           *)
(* B_0(x0,rho) with volume >= nu rho^3 has rho^2 R <= C(kappa,nu,A) on      *)
(* B_0(x0, A rho).  By contradiction: picked points q n with R <= 4 Q n     *)
(* on B(q n, s n), Q n s n^2 -> inf; the limit (S) is a kappa-solution      *)
(* with positive asymptotic volume (Bishop-Gromov at q n, LIM_VOL), against *)
(* THM_9_59.                                                                *)
(* ========================================================================= *)

let P2AL65_ARITH_RAD = prove
 (`!Q s a. &0 < Q /\ &0 < s /\ &0 < a /\ a pow 2 <= Q * s pow 2
           ==> a * inv(sqrt Q) <= s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; GSYM real_div; REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* Picked points along a sequence of counterexamples. *)

let P2AL65_PICK_SEQ = prove
 (`!kappa nu A (top:num->B topology) atlas (g:num->real->B->real^3^3) x0 rho v y.
     (!n. (p2b_kappa_solution kappa (top n,atlas n) (g n) /\ p2b_ksep (top n) (atlas n) /\
           x0 n IN topspace (top n) /\ &0 < rho n /\
           mfd_has_volume (top n,atlas n) (g n (&0))
             (mfd_ball (top n,atlas n) (g n (&0)) (x0 n) (rho n)) (v n) /\
           nu * rho n pow 3 <= v n /\
           y n IN mfd_ball (top n,atlas n) (g n (&0)) (x0 n) (A * rho n)) /\
          &n < rho n pow 2 * mfd_scalar (atlas n) (g n (&0)) (y n))
     ==> ?q sr. !n. &0 < sr n /\ sr n <= rho n / &2 /\ q n IN topspace (top n) /\
                    mfd_dist (top n,atlas n) (g n (&0)) (x0 n) (q n) < (A + &1) * rho n /\
                    &0 < mfd_scalar (atlas n) (g n (&0)) (q n) /\
                    &n / &4 < mfd_scalar (atlas n) (g n (&0)) (q n) * sr n pow 2 /\
                    (!z. z IN mfd_ball (top n,atlas n) (g n (&0)) (q n) (sr n)
                         ==> mfd_scalar (atlas n) (g n (&0)) z <=
                             &4 * mfd_scalar (atlas n) (g n (&0)) (q n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "seq") THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric (atlas(n:num)) ((g:num->real->B->real^3^3) n (&0))`
  ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(y:num->B) n IN mfd_ball (top n,atlas n) ((g:num->real->B->real^3^3) n (&0))
                                        (x0 n) (A * rho n)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:num->B) n IN topspace(top n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar (atlas n) ((g:num->real->B->real^3^3) n (&0)) ((y:num->B) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `rho(n:num) pow 2 * mfd_scalar (atlas n) ((g:num->real->B->real^3^3) n (&0))
                                                  ((y:num->B) n) <= &0`
    MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
      REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `(top:num->B topology) n`;
                 `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                 `(g:num->real->B->real^3^3) n`; `(y:num->B) n`; `(rho:num->real) n`]
                P2AL65_PICK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `qn:B` (X_CHOOSE_THEN `sn:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`qn:B`; `sn:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `mfd_joinable (top n,atlas n:((B->bool)#(B->real^3))->bool) ((x0:num->B) n) qn`
    ASSUME_TAC THENL [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(top:num->B topology) n`; `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                   `(g:num->real->B->real^3^3) n (&0)`; `(x0:num->B) n`; `(y:num->B) n`;
                   `qn:B`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `!x a b. x < a /\ a <= &4 * b ==> x / &4 < b`) THEN
    EXISTS_TAC `rho(n:num) pow 2 * mfd_scalar (atlas n) ((g:num->real->B->real^3^3) n (&0))
                                                ((y:num->B) n)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `sn pow 2`)) (concl th) && not(is_forall(concl th)))) THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `z:B` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM]]);;

(* The same with the scales Q n = R(q n) as a sequence. *)

let P2AL65_PICK_SEQ_Q = prove
 (`!kappa nu A (top:num->B topology) atlas (g:num->real->B->real^3^3) x0 rho v y.
     (!n. (p2b_kappa_solution kappa (top n,atlas n) (g n) /\ p2b_ksep (top n) (atlas n) /\
           x0 n IN topspace (top n) /\ &0 < rho n /\
           mfd_has_volume (top n,atlas n) (g n (&0))
             (mfd_ball (top n,atlas n) (g n (&0)) (x0 n) (rho n)) (v n) /\
           nu * rho n pow 3 <= v n /\
           y n IN mfd_ball (top n,atlas n) (g n (&0)) (x0 n) (A * rho n)) /\
          &n < rho n pow 2 * mfd_scalar (atlas n) (g n (&0)) (y n))
     ==> ?q sr Q. !n. mfd_scalar (atlas n) (g n (&0)) (q n) = Q n /\
                      &0 < sr n /\ sr n <= rho n / &2 /\ q n IN topspace (top n) /\
                      mfd_dist (top n,atlas n) (g n (&0)) (x0 n) (q n) < (A + &1) * rho n /\
                      &0 < Q n /\ &n / &4 < Q n * sr n pow 2 /\
                      (!z. z IN mfd_ball (top n,atlas n) (g n (&0)) (q n) (sr n)
                           ==> mfd_scalar (atlas n) (g n (&0)) z <= &4 * Q n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2AL65_PICK_SEQ) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->B` (X_CHOOSE_THEN `sr:num->real` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`q:num->B`; `sr:num->real`;
    `\n. mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) n)
                    ((g:num->real->B->real^3^3) n (&0)) ((q:num->B) n)`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[]);;

(* MT Cor 9.62 (Tao Cor 3.18.6). *)

let P2AL65_VOL_CURV = prove
 (`!(w:B->bool).
     P2B_THM_9_59_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w
     ==> !kappa nu A. &0 < nu /\ &0 <= A
           ==> ?C. !top atlas (g:real->B->real^3^3) x0 rho v y.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 x0 IN topspace top /\ &0 < rho /\
                 mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) x0 rho) v /\
                 nu * rho pow 3 <= v /\
                 y IN mfd_ball (top,atlas) (g(&0)) x0 (A * rho)
                 ==> rho pow 2 * mfd_scalar atlas (g(&0)) y <= C`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t959") (CONJUNCTS_THEN2 (LABEL_TAC "AC")
    (CONJUNCTS_THEN2 (LABEL_TAC "bg") (LABEL_TAC "drdt")))) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `nu:real`; `A:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&n`) THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `top:num->B topology`
    (X_CHOOSE_THEN `atlas:num->((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g:num->real->B->real^3^3` (X_CHOOSE_THEN `x0:num->B`
    (X_CHOOSE_THEN `rho:num->real` (X_CHOOSE_THEN `v:num->real`
    (X_CHOOSE_THEN `y:num->B` (LABEL_TAC "seq")))))))) THEN
  MP_TAC(ISPECL [`kappa:real`; `nu:real`; `A:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `x0:num->B`; `rho:num->real`; `v:num->real`; `y:num->B`] P2AL65_PICK_SEQ_Q) THEN
  ANTS_TAC THENL [USE_THEN "seq" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->B` (X_CHOOSE_THEN `sr:num->real`
    (X_CHOOSE_THEN `Q:num->real` (LABEL_TAC "pk")))) THEN
  (* bounds on the balls of radius a / sqrt(Q k) *)
  SUBGOAL_THEN
   `!a. &0 < a
        ==> ?N. !k. N <= k ==> a * inv(sqrt((Q:num->real) k)) <= (sr:num->real) k`
  (LABEL_TAC "rad") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `&4 * a pow 2` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "pk" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    MATCH_MP_TAC P2AL65_ARITH_RAD THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&N <= &k` MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. &0 < a
        ==> ?N. !k z. N <= k /\
                      z IN mfd_ball (top k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                                    ((q:num->B) k) (a * inv(sqrt((Q:num->real) k)))
                      ==> mfd_scalar (atlas k) (g k (&0)) z <= &4 * Q k`
  (LABEL_TAC "ballh") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `z:B`] THEN STRIP_TAC THEN
    USE_THEN "pk" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:B) IN mfd_ball (top(k:num),atlas k) ((g:num->real->B->real^3^3) k (&0))
                               ((q:num->B) k) (a * inv(sqrt((Q:num->real) k)))` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `a * inv(sqrt((Q:num->real) k))` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* noncollapsing at the scales R0 / sqrt(Q k) (Bishop-Gromov at q k) *)
  SUBGOAL_THEN
   `!R0. &0 < R0
         ==> ?N. !k vv. N <= k /\
                        mfd_has_volume (top k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                          (mfd_ball (top k,atlas k) (g k (&0)) ((q:num->B) k)
                                    (R0 * inv(sqrt((Q:num->real) k)))) vv
                        ==> nu / (A + &2) pow 3 * (R0 * inv(sqrt(Q k))) pow 3 <= vv`
  (LABEL_TAC "nch") THENL
   [X_GEN_TAC `R0:real` THEN DISCH_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `R0:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `vv:real`] THEN STRIP_TAC THEN
    USE_THEN "pk" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
    SUBGOAL_THEN `riemannian_metric (atlas(k:num)) ((g:num->real->B->real^3^3) k (&0))`
    ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `R0 * inv(sqrt((Q:num->real) k)) <= (sr:num->real) k` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < R0 * inv(sqrt((Q:num->real) k))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                   `(g:num->real->B->real^3^3) k (&0)`;
                   `mfd_ball (top k,atlas k) ((g:num->real->B->real^3^3) k (&0)) ((q:num->B) k)
                             (R0 * inv(sqrt((Q:num->real) k)))`;
                   `vv:real`] MFD_HAS_VOLUME_VOLUME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC P2AL65_BG_NC THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(x0:num->B) k`; `(rho:num->real) k`;
                          `(v:num->real) k`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= A * (rho:num->real) k` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the limit *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `q:num->B`; `Q:num->real`] P2AL65_SLIM_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "ballh" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN MAP_EVERY EXISTS_TAC [`&4`; `N:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl"))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX0_SUBSEQ_GE) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `(top:num->B topology) o (sub:num->num)`;
                 `(atlas:num->((B->bool)#(B->real^3))->bool) o (sub:num->num)`;
                 `(g:num->real->B->real^3^3) o (sub:num->num)`; `(q:num->B) o (sub:num->num)`;
                 `(Q:num->real) o (sub:num->num)`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`] P2AL65_LIM_KSOL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "ballh" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `z:B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `(top:num->B topology) o (sub:num->num)`;
                 `(atlas:num->((B->bool)#(B->real^3))->bool) o (sub:num->num)`;
                 `(g:num->real->B->real^3^3) o (sub:num->num)`; `(q:num->B) o (sub:num->num)`;
                 `(Q:num->real) o (sub:num->num)`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `nu / (A + &2) pow 3`] P2AL65_LIM_VOLUME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `R0:real` THEN DISCH_TAC THEN
    USE_THEN "nch" (MP_TAC o SPEC `R0:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `vv:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC P2AL65_AVR_CONTRA THEN
  MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                        `nu / (A + &2) pow 3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "sl" (fun th -> REWRITE_TAC[MATCH_MP P2AL65_SLIM_BASIC th]);
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* L, part 1: noncollapsing at a small scale (the slab bound on [-1,0]),    *)
(* the critical radius of the volume ratio about p, and collapse at fixed   *)
(* scales about p along a sequence with R(q n) -> inf at bounded distance   *)
(* (Cor 9.62).                                                              *)
(* ========================================================================= *)

let P2AL65_SMALL_NC = prove
 (`!kappa top atlas (g:real->B->real^3^3) x.
     p2b_kappa_solution kappa (top,atlas) g /\ x IN topspace top
     ==> ?s0. &0 < s0 /\ s0 <= &1 /\
              kappa * s0 pow 3 <=
              mfd_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) x s0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
    check (fun th -> can (find_term (fun t -> is_const t &&
                                              fst(dest_const t) = "p2b_kappa_solution"))
                         (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(&1)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th) &&
    can (find_term ((=) `a:real`)) (concl th))) THEN
  REWRITE_TAC[REAL_ARITH `--(&1) <= &0`] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
  ABBREV_TAC `s0 = inv(&1 + abs K)` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 <= &1 /\ K <= inv(s0 pow 2) /\ s0 pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN
    SUBGOAL_THEN `&1 <= &1 + abs K` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_INV; REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + abs K` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_kappa_noncollapsed"))
        (concl th) && is_forall (concl th))) THEN
  REWRITE_TAC[rfs_flow_view] THEN REWRITE_TAC[rfs_kappa_noncollapsed] THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `x:B`; `s0:real`]) THEN
  REWRITE_TAC[rfs_flow_view; rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "K" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) x s0` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`;
                 `mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) x s0`; `v0:real`]
                MFD_HAS_VOLUME_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* The critical radius of the volume ratio about p at the level nu0. *)

let P2AL65_CRIT_RADIUS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p nu0.
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ &0 < nu0 /\ nu0 <= kappa /\
     mfd_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) p (&1)) < nu0
     ==> ?r. &0 < r /\ r <= &1 /\
             (!s. &0 < s /\ s < r
                  ==> nu0 * s pow 3 <=
                      mfd_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) p s)) /\
             (!s. r < s
                  ==> mfd_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) p s) <
                      nu0 * s pow 3)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bg") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(&0)) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3)(&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:B`] P2AL65_SMALL_NC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\s. mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0)) (mfd_ball (top,atlas) (g(&0)) p s) /
         s pow 3`; `nu0:real`; `s0:real`] P2AL65_SUP_RADIUS) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL65_RATIO_MONO THEN EXISTS_TAC `w:B->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&0 < s0 pow 3` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kappa * s0 pow 3` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[REAL_POW_ONE; REAL_DIV_1]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `&0 < s pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ];
    SUBGOAL_THEN `&0 < s pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ]]);;

(* Collapse at a fixed scale c about p n: from Cor 9.62 at A = r / c. *)

let P2AL65_COLLAPSE = prove
 (`!kappa r (top:num->B topology) atlas (g:num->real->B->real^3^3) p q c nu C.
     (!n. p2b_kappa_solution kappa (top n,atlas n) (g n) /\ p2b_ksep (top n) (atlas n) /\
          p n IN topspace (top n) /\ q n IN mfd_ball (top n,atlas n) (g n (&0)) (p n) r /\
          &n < mfd_scalar (atlas n) (g n (&0)) (q n)) /\
     &0 < c /\ &0 < r /\
     (!top atlas (g:real->B->real^3^3) x0 rho v y.
        p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
        x0 IN topspace top /\ &0 < rho /\
        mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) x0 rho) v /\
        nu * rho pow 3 <= v /\
        y IN mfd_ball (top,atlas) (g(&0)) x0 (r / c * rho)
        ==> rho pow 2 * mfd_scalar atlas (g(&0)) y <= C)
     ==> ?N. !n. N <= n
                 ==> mfd_volume (top n,atlas n) (g n (&0))
                       (mfd_ball (top n,atlas n) (g n (&0)) (p n) c) < nu * c pow 3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v")))) THEN
  MP_TAC(SPEC `C / c pow 2` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  SUBGOAL_THEN `riemannian_metric (atlas(n:num)) ((g:num->real->B->real^3^3) n (&0))`
  ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->B topology) n`; `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                 `(g:num->real->B->real^3^3) n (&0)`; `(p:num->B) n`; `c:real`]
                MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "v" (MP_TAC o SPECL
    [`(top:num->B topology) n`; `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
     `(g:num->real->B->real^3^3) n`; `(p:num->B) n`; `c:real`;
     `mfd_volume (top n,atlas n) ((g:num->real->B->real^3^3) n (&0))
                 (mfd_ball (top n,atlas n) (g n (&0)) (p n) c)`; `(q:num->B) n`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r / c * c = r` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `C < c pow 2 * mfd_scalar (atlas n) ((g:num->real->B->real^3^3) n (&0))
                                            ((q:num->B) n)`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&n` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* L, part 2: arithmetic for the critical radius and the final              *)
(* contradiction, the sequence facts (collapse, the critical radii rr       *)
(* n -> 0, the ball bounds at scale rr n), and the route theorem for MT     *)
(* Lemma 9.65.                                                              *)
(* ========================================================================= *)

let P2AL65_SQRT_INV_SQ = prove
 (`!rr. &0 < rr ==> sqrt(inv(rr pow 2)) = inv rr`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SQRT_INV] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC POW_2_SQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P2AL65_ARITH_HALF = prove
 (`!rr R C. &0 < rr /\ (rr / &2) pow 2 * R <= C ==> R <= (&4 * C) * inv(rr pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rr pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  UNDISCH_TAC `(rr / &2) pow 2 * R <= C` THEN
  REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let P2AL65_ARITH_FLAT = prove
 (`!rr nu0 vk.
     &0 < rr /\ nu0 <= &1 /\ vk < nu0 * (&6 / &5 * rr) pow 3 /\
     &4 / &3 * pi <= inv(rr pow 2) * inv rr * vk + &1 / &10
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rr pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(rr pow 2) * inv rr * vk = vk / rr pow 3` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < rr` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `vk / rr pow 3 < nu0 * (&6 / &5) pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `vk < nu0 * (&6 / &5 * rr) pow 3` THEN
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  UNDISCH_TAC `vk / rr pow 3 < nu0 * (&6 / &5) pow 3` THEN
  UNDISCH_TAC `&4 / &3 * pi <= vk / rr pow 3 + &1 / &10` THEN
  UNDISCH_TAC `nu0 <= &1` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* The critical radii along a sequence with R(q n) -> inf at distance < r. *)

let P2AL65_L_RADII = prove
 (`!(w:B->bool) kappa r nu0 (top:num->B topology) atlas (g:num->real->B->real^3^3) p q.
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\
     (!nu A. &0 < nu /\ &0 <= A
             ==> ?C. !top atlas (g:real->B->real^3^3) x0 rho v y.
                   p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                   x0 IN topspace top /\ &0 < rho /\
                   mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) x0 rho) v /\
                   nu * rho pow 3 <= v /\
                   y IN mfd_ball (top,atlas) (g(&0)) x0 (A * rho)
                   ==> rho pow 2 * mfd_scalar atlas (g(&0)) y <= C) /\
     &0 < r /\ &0 < nu0 /\ nu0 <= kappa /\
     (!n. p2b_kappa_solution kappa (top n,atlas n) (g n) /\ p2b_ksep (top n) (atlas n) /\
          p n IN topspace (top n) /\ q n IN mfd_ball (top n,atlas n) (g n (&0)) (p n) r /\
          &n < mfd_scalar (atlas n) (g n (&0)) (q n))
     ==> ?N1 rr. (!n. &0 < rr n) /\
                 (!n. N1 <= n
                      ==> rr n <= &1 /\
                          (!s. &0 < s /\ s < rr n
                               ==> nu0 * s pow 3 <=
                                   mfd_volume (top n,atlas n) (g n (&0))
                                     (mfd_ball (top n,atlas n) (g n (&0)) (p n) s)) /\
                          (!s. rr n < s
                               ==> mfd_volume (top n,atlas n) (g n (&0))
                                     (mfd_ball (top n,atlas n) (g n (&0)) (p n) s) <
                                   nu0 * s pow 3)) /\
                 (!c. &0 < c ==> ?N. !n. N <= n ==> rr n <= c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bg") (CONJUNCTS_THEN2 (LABEL_TAC "V")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seq")))))) THEN
  SUBGOAL_THEN
   `!c nu. &0 < c /\ &0 < nu
           ==> ?N. !n. N <= n
                       ==> mfd_volume (top n,atlas n) ((g:num->real->B->real^3^3) n (&0))
                             (mfd_ball (top n,atlas n) (g n (&0)) ((p:num->B) n) c) <
                           nu * c pow 3`
  (LABEL_TAC "col") THENL
   [MAP_EVERY X_GEN_TAC [`c:real`; `nu:real`] THEN STRIP_TAC THEN
    USE_THEN "V" (MP_TAC o SPECL [`nu:real`; `r / c`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
    MATCH_MP_TAC P2AL65_COLLAPSE THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `r:real`; `q:num->B`; `C:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "col" (MP_TAC o SPECL [`&1`; `nu0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  SUBGOAL_THEN
   `?rr:num->real.
      !n. &0 < rr n /\
          (N1 <= n
           ==> rr n <= &1 /\
               (!s. &0 < s /\ s < rr n
                    ==> nu0 * s pow 3 <=
                        mfd_volume (top n,atlas n) ((g:num->real->B->real^3^3) n (&0))
                          (mfd_ball (top n,atlas n) (g n (&0)) ((p:num->B) n) s)) /\
               (!s. rr n < s
                    ==> mfd_volume (top n,atlas n) (g n (&0))
                          (mfd_ball (top n,atlas n) (g n (&0)) (p n) s) < nu0 * s pow 3))`
  (X_CHOOSE_THEN `rr:num->real` (LABEL_TAC "rr")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    ASM_CASES_TAC `N1 <= n:num` THENL
     [USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `(top:num->B topology) n`;
                     `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                     `(g:num->real->B->real^3^3) n`; `(p:num->B) n`; `nu0:real`]
                    P2AL65_CRIT_RADIUS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`N1:num`; `rr:num->real`] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "rr" (fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN USE_THEN "rr" (MP_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    USE_THEN "col" (MP_TAC o SPECL [`c:real`; `nu0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN EXISTS_TAC `N1 + N2:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "rr" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "below") (K ALL_TAC))) THEN
    USE_THEN "below" (MP_TAC o SPEC `c:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* The route theorem for MT Lemma 9.65 (Tao Prop 3.18.7).  By contradiction: *)
(* R(p n) = 1, R(q n) > n on B(p n,r); the critical radii rr n -> 0 of the  *)
(* volume ratio about p n at the level nu0 = min kappa 1; Cor 9.62 bounds R *)
(* by C_A / rr n^2 on B(p n, A rr n); the limit (S) at the scales 1 / rr n^2 *)
(* has R(xl,0) = 0, so it is flat (Thm 4.18 clause of SMP_SPLIT_PT) and      *)
(* kappa-noncollapsed, hence Euclidean (FLAT_KNC): vol B(xl,1) = 4/3 pi;    *)
(* but LIM_VOL bounds it by nu0 (6/5)^3 + 1/10.                              *)

let P2AL65_LEMMA_9_65_ROUTE = prove
 (`!w:B->bool. P2B_LEMMA_9_65_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_LEMMA_9_65_ROUTE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t959") (CONJUNCTS_THEN2 (LABEL_TAC "AC")
    (CONJUNCTS_THEN2 (LABEL_TAC "bg") (CONJUNCTS_THEN2 (LABEL_TAC "drdt")
    (CONJUNCTS_THEN2 (LABEL_TAC "smp") (LABEL_TAC "fk")))))) THEN
  MP_TAC(ISPEC `w:B->bool` P2AL65_VOL_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "V")] THEN
  REWRITE_TAC[P2B_LEMMA_9_65_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `r:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&n`) THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `top:num->B topology`
    (X_CHOOSE_THEN `atlas:num->((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g:num->real->B->real^3^3` (X_CHOOSE_THEN `p:num->B`
    (X_CHOOSE_THEN `q:num->B` (LABEL_TAC "seq0")))))) THEN
  SUBGOAL_THEN
   `!n. p2b_kappa_solution kappa (top n,atlas n) ((g:num->real->B->real^3^3) n) /\
        p2b_ksep (top n) (atlas n) /\ (p:num->B) n IN topspace (top n) /\
        (q:num->B) n IN mfd_ball (top n,atlas n) (g n (&0)) (p n) r /\
        &n < mfd_scalar (atlas n) (g n (&0)) (q n)`
  (LABEL_TAC "seq") THENL
   [GEN_TAC THEN USE_THEN "seq0" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `nu0 = min kappa (&1)` THEN
  SUBGOAL_THEN `&0 < nu0 /\ nu0 <= kappa /\ nu0 <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "nu0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `r:real`; `nu0:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `p:num->B`; `q:num->B`] P2AL65_L_RADII) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "V" (ACCEPT_TAC o SPEC `kappa:real`); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (X_CHOOSE_THEN `rr:num->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "rpos") (CONJUNCTS_THEN2 (LABEL_TAC "rr") (LABEL_TAC "r0"))))) THEN
  ABBREV_TAC `Q = \n:num. inv((rr:num->real) n pow 2)` THEN
  SUBGOAL_THEN `!n. (Q:num->real) n = inv(rr n pow 2) /\ &0 < Q n /\
                    sqrt(Q n) = inv(rr n) /\ inv(sqrt(Q n)) = rr n`
  (LABEL_TAC "Q") THENL
   [GEN_TAC THEN EXPAND_TAC "Q" THEN BETA_TAC THEN
    USE_THEN "rpos" (ASSUME_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; P2AL65_SQRT_INV_SQ; REAL_INV_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. &0 < a
        ==> ?CA N. !k y. N <= k /\
                         y IN mfd_ball (top k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                                       ((p:num->B) k) (a * inv(sqrt((Q:num->real) k)))
                         ==> mfd_scalar (atlas k) (g k (&0)) y <= CA * Q k`
  (LABEL_TAC "ballh") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "V" (MP_TAC o SPECL [`kappa:real`; `nu0:real`; `&2 * a`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "C")) THEN
    MAP_EVERY EXISTS_TAC [`&4 * C`; `N1:num`] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `y:B`] THEN STRIP_TAC THEN
    USE_THEN "Q" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "rpos" (ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "rr" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "below") (K ALL_TAC))) THEN
    USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
    SUBGOAL_THEN `riemannian_metric (atlas(k:num)) ((g:num->real->B->real^3^3) k (&0))`
    ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(y:B) IN mfd_ball (top(k:num),atlas k) ((g:num->real->B->real^3^3) k (&0))
                                ((p:num->B) k) (a * inv(sqrt((Q:num->real) k)))` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2AL65_ARITH_HALF THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                 `(g:num->real->B->real^3^3) k (&0)`; `(p:num->B) k`; `(rr:num->real) k / &2`]
                MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "C" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(top:num->B topology) k`; `(p:num->B) k`;
    `mfd_volume (top k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                (mfd_ball (top k,atlas k) (g k (&0)) ((p:num->B) k) (rr k / &2))`] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    USE_THEN "below" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(&2 * a) * (rr:num->real) k / &2 = a * rr k` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `p:num->B`; `Q:num->real`] P2AL65_SLIM_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl"))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX0_SUBSEQ_GE) THEN
  USE_THEN "sl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_SEC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_COMPLETE th) THEN
    ASSUME_TAC(REWRITE_RULE[p2b_kview] (MATCH_MP P2AL65_SLIM_KNC th)) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  SUBGOAL_THEN `((\k. (rr:num->real) ((sub:num->num) k) pow 2) ---> &0) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "r0" (MP_TAC o SPEC `min (&1) (e / &2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(rr:num->real) ((sub:num->num) k) <= min (&1) (e / &2)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "rpos" (ASSUME_TAC o SPEC `(sub:num->num) k`) THEN
    SUBGOAL_THEN `(rr:num->real) ((sub:num->num) k) pow 2 <= rr (sub k)` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `(rr:num->real) ((sub:num->num) k)` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas' ((g':real->B->real^3^3)(&0)) xl = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kappa:real`; `(top:num->B topology) o (sub:num->num)`;
                   `(atlas:num->((B->bool)#(B->real^3))->bool) o (sub:num->num)`;
                   `(g:num->real->B->real^3^3) o (sub:num->num)`; `(p:num->B) o (sub:num->num)`;
                   `(Q:num->real) o (sub:num->num)`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`] P2AL65_SLIM_SCALAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\k. mfd_scalar (((atlas:num->((B->bool)#(B->real^3))->bool) o (sub:num->num)) k)
                      (((g:num->real->B->real^3^3) o sub) k (&0 / ((Q:num->real) o sub) k))
                      ((phi:num->B->B) k xl) / (Q o sub) k) =
      (\k. (rr:num->real) (sub k) pow 2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `k:num` THEN
      ASM_REWRITE_TAC[REAL_ARITH `!x:real. &0 / x = &0`; o_THM] THEN
      USE_THEN "seq0" (MP_TAC o SPEC `(sub:num->num) k`) THEN SIMP_TAC[] THEN DISCH_TAC THEN
      USE_THEN "rpos" (ASSUME_TAC o SPEC `(sub:num->num) k`) THEN
      UNDISCH_TAC `&0 < (rr:num->real) ((sub:num->num) k)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
    EXISTS_TAC `\k. (rr:num->real) ((sub:num->num) k) pow 2` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y u v. t <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas' ((g':real->B->real^3^3) t) y u v = &0`
  (LABEL_TAC "flat") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "smp" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                                    `g':real->B->real^3^3`; `t - &1`; `&0`; `xl:B`; `&0`] o
                    REWRITE_RULE[P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x s. x IN topspace top' /\ &0 < s
          ==> ?v. mfd_has_volume (top',atlas') ((g':real->B->real^3^3)(&0))
                    (mfd_ball (top',atlas') (g'(&0)) x s) v /\ kappa * s pow 3 <= v`
  (LABEL_TAC "snc") THENL
   [MAP_EVERY X_GEN_TAC [`x:B`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_kappa_noncollapsed"))
          (concl th) && is_forall (concl th))) THEN
    REWRITE_TAC[rfs_flow_view] THEN REWRITE_TAC[rfs_kappa_noncollapsed] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `x:B`; `s:real`]) THEN
    REWRITE_TAC[rfs_flow_view; rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `t <= &0` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `y:B`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `mfd_rm_norm atlas' ((g':real->B->real^3^3) t) y = &0` SUBST1_TAC THENL
       [MATCH_MP_TAC FLT_RM_NORM_FLAT THEN REPEAT STRIP_TAC THEN
        USE_THEN "flat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:B) IN mfd_ball (top',atlas') ((g':real->B->real^3^3)(&0)) x s` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "fk" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                                 `(g':real->B->real^3^3)(&0)`; `kappa:real`] o
                 REWRITE_RULE[P2B_REQ_FLAT_KNC_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "flat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`xl:B`; `&1`]) THEN ASM_REWRITE_TAC[REAL_LT_01; REAL_POW_ONE; REAL_MUL_RID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&0)`; `xl:B`; `&6 / &5`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(REWRITE_RULE[LIM_VOL_STATEMENT] (ISPECL [`(:B)`; `(:B)`] LIM_VOL)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview (((top:num->B topology) o (sub:num->num)) k,
                       ((atlas:num->((B->bool)#(B->real^3))->bool) o sub) k)
                      (((g:num->real->B->real^3^3) o sub) k)`;
    `(p:num->B) o (sub:num->num)`; `\k:num. &0`; `(Q:num->real) o (sub:num->num)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`;
    `&1`; `&6 / &5`; `&4 / &3 * pi`;
    `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0)) (mfd_ball (top',atlas') (g'(&0)) xl (&6 / &5))`;
    `&1 / &10`]) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPEC `k0 + N1:num`)) THEN
  REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `vk1:real` (X_CHOOSE_THEN `vk2:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `k1 = k0 + N1:num` THEN
  SUBGOAL_THEN `N1 <= (sub:num->num) k1` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k1:num` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "k1" THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Q" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k1`) THEN
  USE_THEN "rpos" (ASSUME_TAC o SPEC `(sub:num->num) k1`) THEN
  USE_THEN "rr" (MP_TAC o SPEC `(sub:num->num) k1`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "above"))) THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k1`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `vk2:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_has_volume")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `vk2:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pi")) (concl th))) THEN
  REWRITE_TAC[o_THM; p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM;
              REAL_ARITH `!x:real. &0 / x = &0`; REAL_ADD_RID; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric (atlas((sub:num->num) k1)) ((g:num->real->B->real^3^3) (sub k1) (&0))`
  ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->B topology) ((sub:num->num) k1)`;
                 `(atlas:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k1)`;
                 `(g:num->real->B->real^3^3) ((sub:num->num) k1) (&0)`;
                 `mfd_ball (top((sub:num->num) k1),atlas (sub k1))
                           ((g:num->real->B->real^3^3) (sub k1) (&0)) ((p:num->B) (sub k1))
                           (&6 / &5 * (rr:num->real) (sub k1))`; `vk2:real`]
                MFD_HAS_VOLUME_VOLUME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "above" (MP_TAC o SPEC `&6 / &5 * (rr:num->real) ((sub:num->num) k1)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MATCH_MP_TAC P2AL65_ARITH_FLAT THEN
  MAP_EVERY EXISTS_TAC [`(rr:num->real) ((sub:num->num) k1)`; `nu0:real`; `vk2:real`] THEN
  ASM_REWRITE_TAC[]);;

