(* ========================================================================= *)
(* Unit pc_p2b_ancc: the route of P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT      *)
(* (pc_p2b_defs) on the statement of pc_p2b_anccreq:                         *)
(* P2BAC_ANCIENT_COMPACT_ROUTE |- !w. P2B_ANCIENT_COMPACT_ROUTE_STATEMENT w. *)
(* The flows are read as the views p2b_kview (the flow on the times t <= 0), *)
(* which are regular; at time 0 their balls have compact closures            *)
(* (completeness) and Shi's estimate in view form (VSHI_SHI_VIEW_CC) bounds  *)
(* the curvature derivatives, so Cheeger-Gromov compactness (the hypothesis) *)
(* gives a complete slice limit at time 0; P2BU_FROM_SLICE_UPTO              *)
(* (pc_p2c_blowup) extends it to a flow limit on the times s <= 0, smooth up *)
(* to 0, and P2BU_FLOW_LIMIT_OF_ON gives one subsequence for every Tl.       *)
(* ========================================================================= *)

needs "src/pc_p2b_anccreq.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_vshi.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_p2c_views.ml";;
needs "src/pc_p2c_blowup.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The views p2b_kview of a flow that is rfs_flow_upto on (a,0] for every a  *)
(* < 0: Riemannian slices for t <= 0, regular views, and the accessors       *)
(* (balls, abs Rm, persistence of open sets).                                *)
(* ========================================================================= *)

let P2BAC_SUBSEQ_O = prove
 (`!r e. p3_subseq r /\ p3_subseq e ==> p3_subseq (r o e)`,
  REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[]);;

let P2BAC_UPTO_RIEMANNIAN = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3).
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)
     ==> smooth_manifold_atlas top atlas /\
         !t. t <= &0 ==> riemannian_metric atlas (g t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "up") THEN CONJ_TAC THENL
   [USE_THEN "up" (MP_TAC o SPEC `-- &1`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto; ricci_flow_on]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  USE_THEN "up" (MP_TAC o SPEC `t - &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric")) (concl th) &&
    not(can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_derivative"))
            (concl th)))) THEN
  ASM_REAL_ARITH_TAC);;

let P2BAC_KVIEW_REGULAR = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3).
     hausdorff_space top /\ (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)
     ==> p2c_regular_view (p2b_kview (top,atlas) g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BAC_UPTO_RIEMANNIAN) THEN
  REWRITE_TAC[p2b_kview] THEN MATCH_MP_TAC P2CF_FLOW_VIEW_REGULAR_GEN THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `b = &0` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `&0`] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto"))
          (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]]];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CF_RFO_FROM THEN MAP_EVERY EXISTS_TAC [`a - &1`; `&0`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a - &1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto"))
        (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]]]);;

let P2BAC_KVIEW_FACTS = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) s x r.
     s <= &0
     ==> rfs_vtop (p2b_kview (top,atlas) g) s = top /\
         rfs_vatlas (p2b_kview (top,atlas) g) s = atlas /\
         rfs_vmetric (p2b_kview (top,atlas) g) s = g s /\
         rfs_vball (p2b_kview (top,atlas) g) s x r = mfd_ball (top,atlas) (g s) x r /\
         p3_vrm (p2b_kview (top,atlas) g) s x = mfd_rm_norm atlas (g s) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vball; p3_vrm;
              IN_ELIM_THM] THEN
  ASM_SIMP_TAC[]);;

let P2BAC_KVIEW_PERSISTS = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) U a b.
     smooth_manifold_atlas top atlas /\ open_in top U /\ b <= &0
     ==> rfs_persists (p2b_kview (top,atlas) g) U a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_persists; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The hypotheses of Cheeger-Gromov compactness at time 0 for the views      *)
(* p2b_kview of the flows: compact ball closures (completeness) and the      *)
(* derivative bounds p3_vderiv2 <= C Q^(l+2) on the balls of radius          *)
(* A/sqrt(Q) from Shi's estimate (VSHI_SHI_VIEW_CC) on the time interval     *)
(* (-1/Q, 0], where abs Rm <= CA Q on the balls of radius 4A/sqrt(Q).        *)
(* ========================================================================= *)

let P2BAC_DERIV0 = prove
 (`!top (atlas:num->((B->bool)#(B->real^3))->bool) (g:num->real->B->real^3^3) x Q.
     (!k. hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
          (!a. a < &0 ==> rfs_flow_upto (top k,atlas k) a (&0) (g k)) /\
          (!t. t <= &0 ==> mfd_complete (top k,atlas k) (g k t)) /\
          x k IN topspace(top k) /\ &0 < Q k) /\
     (!A a. &0 < A /\ a < &0
            ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                               y IN mfd_ball (top k,atlas k) (g k (&0)) (x k)
                                       (A * inv(sqrt(Q k)))
                               ==> mfd_rm_norm (atlas k) (g k (s / Q k)) y <= CA * Q k)
     ==> !A l. &0 < A
               ==> ?CAl N. !n y. N <= n /\
                                 y IN rfs_vball (p2b_kview (top n,atlas n) (g n)) (&0) (x n)
                                        (A * inv(sqrt(Q n)))
                                 ==> p3_vderiv2 (p2b_kview (top n,atlas n) (g n)) l (&0) y <=
                                     CAl * Q n pow (l + 2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") (LABEL_TAC "curv")) THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
  USE_THEN "curv" (MP_TAC o SPECL [`&4 * A`; `-- &1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CA:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "cb"))) THEN
  MP_TAC(ISPECL [`l:num`; `max CA (&1)`; `A:real`; `&1`]
                (INST_TYPE [`:B`,`:A`] VSHI_SHI_VIEW_CC)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "sv")) THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `N:num`] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:B`] THEN STRIP_TAC THEN
  USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  MP_TAC(ISPECL [`(top:num->B topology) n`; `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                 `(g:num->real->B->real^3^3) n`] P2BAC_UPTO_RIEMANNIAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric ((atlas:num->((B->bool)#(B->real^3))->bool) n)
                                  ((g:num->real->B->real^3^3) n (&0)) /\
                mfd_complete ((top:num->B topology) n,atlas n) (g n (&0))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  USE_THEN "sv" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(x:num->B) n`; `--inv((Q:num->real) n)`] THEN
  ASM_SIMP_TAC[P2BAC_KVIEW_FACTS; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BAC_KVIEW_REGULAR THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_NEG_LT0; REAL_LT_INV];
    UNDISCH_TAC `&0 < (Q:num->real) n` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC P2BAC_KVIEW_PERSISTS THEN ASM_SIMP_TAC[MFD_BALL_OPEN; REAL_LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`(top:num->B topology) n`;
    `(atlas:num->((B->bool)#(B->real^3))->bool) n`; `(g:num->real->B->real^3^3) n`;
    `&0`; `(x:num->B) n`; `(&4 * A) * inv(sqrt((Q:num->real) n))`] P2BAC_KVIEW_FACTS)
    (SPEC `&0` REAL_LE_REFL)]) THEN
  ASM_SIMP_TAC[P2BAC_KVIEW_FACTS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CA * (Q:num->real) n` THEN CONJ_TAC THENL
   [USE_THEN "cb" (MP_TAC o SPECL [`n:num`; `s * (Q:num->real) n`; `z:B`]) THEN
    SUBGOAL_THEN `(s * (Q:num->real) n) / Q n = s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (Q:num->real) n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `--inv((Q:num->real) n) * Q n = -- &1` (fun th -> REWRITE_TAC[GSYM th]) THENL
     [UNDISCH_TAC `&0 < (Q:num->real) n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_ARITH `s * q <= &0 <=> &0 <= --s * q`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The complete slice limit at time 0 of the views p2b_kview along a         *)
(* subsequence (Cheeger-Gromov compactness, the hypothesis of the route).    *)
(* ========================================================================= *)

let P2BAC_SLICE0 = prove
 (`!(w:B->bool) top (atlas:num->((B->bool)#(B->real^3))->bool) (g:num->real->B->real^3^3) x Q.
     P2C_CG_COMPACT_STATEMENT w w /\
     (!k. hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
          (!a. a < &0 ==> rfs_flow_upto (top k,atlas k) a (&0) (g k)) /\
          (!t. t <= &0 ==> mfd_complete (top k,atlas k) (g k t)) /\
          x k IN topspace(top k) /\ &0 < Q k) /\
     (!A a. &0 < A /\ a < &0
            ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                               y IN mfd_ball (top k,atlas k) (g k (&0)) (x k)
                                       (A * inv(sqrt(Q k)))
                               ==> mfd_rm_norm (atlas k) (g k (s / Q k)) y <= CA * Q k) /\
     (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
        !k. N <= k
            ==> ?v. mfd_has_volume (top k,atlas k) (g k (&0))
                      (mfd_ball (top k,atlas k) (g k (&0)) (x k) (r0 * inv(sqrt(Q k)))) v /\
                    kappa * (r0 * inv(sqrt(Q k))) pow 3 <= v)
     ==> ?sub (top0:B topology) atlas0 g0 xl.
            p3_subseq sub /\
            p3_slice_limit (\n. p2b_kview (top (sub n),atlas (sub n)) (g (sub n)))
                           (x o sub) ((\n:num. &0) o sub) (Q o sub) (top0,atlas0) g0 xl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_CG_COMPACT_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cg") (CONJUNCTS_THEN2 (LABEL_TAC "base")
    (CONJUNCTS_THEN2 (LABEL_TAC "curv") (LABEL_TAC "vol")))) THEN
  USE_THEN "cg" (MP_TAC o SPECL
   [`\n. p2b_kview ((top:num->B topology) n,(atlas:num->((B->bool)#(B->real^3))->bool) n)
                   ((g:num->real->B->real^3^3) n)`;
    `x:num->B`; `\n:num. &0`; `Q:num->real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      MP_TAC(ISPECL [`(top:num->B topology) n`; `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                     `(g:num->real->B->real^3^3) n`] P2BAC_UPTO_RIEMANNIAN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[P2BAC_KVIEW_FACTS; REAL_LE_REFL];
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      MP_TAC(ISPECL [`(top:num->B topology) n`; `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                     `(g:num->real->B->real^3^3) n`] P2BAC_UPTO_RIEMANNIAN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[P2BAC_KVIEW_FACTS; REAL_LE_REFL] THEN
      MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_SIMP_TAC[REAL_LE_REFL];
      MP_TAC(ISPECL [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                     `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`] P2BAC_DERIV0) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "vol" MP_TAC THEN SIMP_TAC[P2BAC_KVIEW_FACTS; REAL_LE_REFL]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* From the slice limit at 0 to one flow limit on the times s <= 0           *)
(* (P2BU_FROM_SLICE_UPTO): riemannian for s <= 0, complete at 0, smooth up   *)
(* to 0.  The ball hypotheses come from the abs Rm bound on [min a (-1), 0]  *)
(* at the indices of the subsequence.                                        *)
(* ========================================================================= *)

let P2BAC_SUBSEQ_BIGGER = prove
 (`!sub. p3_subseq sub ==> !n. n <= sub n`,
  GEN_TAC THEN REWRITE_TAC[p3_subseq] THEN DISCH_TAC THEN
  MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]);;

let P2BAC_NO_LEAST = prove
 (`!a0. a0 IN {s:real | s <= &0} /\ (!s. s IN {s:real | s <= &0} ==> a0 <= s) ==> a0 = &0`,
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a0 - &1`) THEN ASM_REAL_ARITH_TAC);;

let P2BAC_FLOW_ON = prove
 (`!top (atlas:num->((B->bool)#(B->real^3))->bool) (g:num->real->B->real^3^3) x Q sub
    (top0:B topology) atlas0 g0 xl.
     (!k. hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
          (!a. a < &0 ==> rfs_flow_upto (top k,atlas k) a (&0) (g k)) /\
          (!t. t <= &0 ==> mfd_complete (top k,atlas k) (g k t)) /\
          x k IN topspace(top k) /\ &0 < Q k) /\
     (!A a. &0 < A /\ a < &0
            ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                               y IN mfd_ball (top k,atlas k) (g k (&0)) (x k)
                                       (A * inv(sqrt(Q k)))
                               ==> mfd_rm_norm (atlas k) (g k (s / Q k)) y <= CA * Q k) /\
     p3_subseq sub /\
     p3_slice_limit (\n. p2b_kview (top (sub n),atlas (sub n)) (g (sub n)))
                    (x o sub) ((\n:num. &0) o sub) (Q o sub) (top0,atlas0) g0 xl
     ==> ?sub2 (top':B topology) atlas' g'.
            p3_subseq sub2 /\
            p3_flow_limit_on
              (\n. (\n. p2b_kview (top (sub n),atlas (sub n)) (g (sub n))) (sub2 n))
              ((x o sub) o sub2) (((\n:num. &0) o sub) o sub2) ((Q o sub) o sub2)
              {s | s <= &0} (top',atlas') g' xl /\
            (!s. s <= &0 ==> riemannian_metric atlas' (g' s)) /\
            mfd_complete (top',atlas') (g' (&0)) /\
            (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") (CONJUNCTS_THEN2 (LABEL_TAC "curv")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl")))) THEN
  USE_THEN "sl" (MP_TAC o REWRITE_RULE[P2C_SLICE_LIMIT_WITH]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `W:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->B` ASSUME_TAC))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BAC_SUBSEQ_BIGGER) THEN
  MP_TAC(ISPECL [`\n. p2b_kview ((top:num->B topology) ((sub:num->num) n),
                                 (atlas:num->((B->bool)#(B->real^3))->bool) (sub n))
                                ((g:num->real->B->real^3^3) (sub n))`;
                 `(x:num->B) o (sub:num->num)`; `(\n:num. &0) o (sub:num->num)`;
                 `(Q:num->real) o (sub:num->num)`; `{s:real | s <= &0}`;
                 `top0:B topology`; `atlas0:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BU_FROM_SLICE_UPTO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_THM; REAL_ADD_LID] THEN
    ASM_REWRITE_TAC[IS_REALINTERVAL_CLAUSES; IN_ELIM_THM; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a0 - &1`) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
      MATCH_MP_TAC P2BAC_KVIEW_REGULAR THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
      ASM_SIMP_TAC[P2BAC_KVIEW_FACTS; REAL_LE_REFL];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`A:real`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `b < a` THENL
     [MAP_EVERY EXISTS_TAC [`&0`; `0`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
      REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_persists] THEN X_GEN_TAC `s:real` THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `b / (Q:num->real) ((sub:num->num) n) < a / Q (sub n)` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; ASM_REAL_ARITH_TAC];
        REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
     [MP_TAC(SPEC `b:real` (REWRITE_RULE[SUBSET]
        (ASSUME `real_interval[a,b] SUBSET {s:real | s <= &0}`))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "curv" (MP_TAC o SPECL [`A:real`; `min a (-- &1)`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `CA:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "cb"))) THEN
    MAP_EVERY EXISTS_TAC [`CA:real`; `N:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
    MP_TAC(ISPECL [`(top:num->B topology) ((sub:num->num) n)`;
                   `(atlas:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) n)`;
                   `(g:num->real->B->real^3^3) ((sub:num->num) n)`] P2BAC_UPTO_RIEMANNIAN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `N <= (sub:num->num) n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!s. s <= b ==> s / (Q:num->real) ((sub:num->num) n) <= &0` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2BAC_KVIEW_FACTS; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[P2AP_BALL_SUBSET];
      MATCH_MP_TAC P2BAC_KVIEW_PERSISTS THEN ASM_SIMP_TAC[MFD_BALL_OPEN; REAL_LE_REFL];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
      USE_THEN "cb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`sub2:num->num`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric")) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "g'")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "g'")) (concl th))) THEN
    ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The headline.  Cheeger-Gromov at time 0 (P2BAC_SLICE0), the flow limit on *)
(* the times s <= 0 (P2BAC_FLOW_ON), and one further subsequence for every   *)
(* Tl > 0 (P2BU_FLOW_LIMIT_OF_ON with c k = k + 1).                          *)
(* ========================================================================= *)

let P2BAC_ANCIENT_COMPACT_ROUTE = prove
 (`!w:B->bool. P2B_ANCIENT_COMPACT_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_ANCIENT_COMPACT_ROUTE_STATEMENT; P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                       `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") (CONJUNCTS_THEN2 (LABEL_TAC "curv")
    (LABEL_TAC "vol"))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                 `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`] P2BAC_SLICE0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top0:B topology`
    (X_CHOOSE_THEN `atlas0:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g0:B->real^3^3`
    (X_CHOOSE_THEN `xl:B` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                 `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `sub1:num->num`;
                 `top0:B topology`; `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`] P2BAC_FLOW_ON) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL
   [`\n. (\n. p2b_kview ((top:num->B topology) ((sub1:num->num) n),
                         (atlas:num->((B->bool)#(B->real^3))->bool) (sub1 n))
                        ((g:num->real->B->real^3^3) (sub1 n))) ((sub2:num->num) n)`;
    `((x:num->B) o (sub1:num->num)) o (sub2:num->num)`;
    `((\n:num. &0) o (sub1:num->num)) o (sub2:num->num)`;
    `((Q:num->real) o (sub1:num->num)) o (sub2:num->num)`; `{s:real | s <= &0}`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
    `\k:num. &k + &1`] P2BU_FLOW_LIMIT_OF_ON) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub3:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fls"))) THEN
  MAP_EVERY EXISTS_TAC
   [`(sub1:num->num) o (sub2:num->num) o (sub3:num->num)`; `top':B topology`;
    `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC P2BAC_SUBSEQ_O THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `Tl:real` THEN DISCH_TAC THEN
  USE_THEN "fls" (MP_TAC o SPEC `Tl:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `a:real` THEN DISCH_TAC THEN MP_TAC(SPEC `a:real` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REAL_ARITH_TAC;
      X_GEN_TAC `a:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th) &&
        can (find_term (fun t -> is_var t && fst(dest_var t) = "g'")) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; p2b_kview] THEN SIMP_TAC[]);;

