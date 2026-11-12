(* ========================================================================= *)
(* Unit pc_p3_c171c: MT Prop 17.1, the T' argument (pp. 406-408) and its    *)
(* repair (a maximal T' over nested subsequences).                          *)
(* Start at rescaled time 0 (Claims 17.10-17.11: time-0 slice limit, Claims *)
(* 11.6-11.7, Prop 2.19), the supremum over nested subsequences, the       *)
(* extension past an intermediate time (Claim 17.9 at a base time t0, caps *)
(* excluded by Lemma 17.7 and by persistence), Step B (A-dependent         *)
(* extension past Tb from Thm 11.8 with its Cor 11.16 bound) and Step D (one *)
(* uniform window past Tb, with the bound RFA_171_UTB at -Tb), T' = infinity *)
(* along one subsequence, and the T' = infinity case (Thm 11.8 second part *)
(* and Cor 9.95).  Noncollapsing of a counterexample up to its first bad   *)
(* time (Prop 16.1 on the truncation, closedness at ts) and the packaging  *)
(* of the sequence hypotheses along subsequences.                          *)
(* ========================================================================= *)

needs "src/pc_p3_c171b.ml";;
needs "src/pc_p2c_bugq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Prop 17.1, the start of the T' argument (MT Claims 17.10-17.11 at time  *)
(* 0 in the rescaled flows): along a subsequence the counterexamples have   *)
(* the backward hypothesis of Thm 11.8 for one window dl > 0.               *)
(* ========================================================================= *)

(* Balls of nonpositive radius in the slices of a regular view are empty. *)

let P3H_VBALL_NONPOS_EMPTY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x r.
     p2c_regular_view V /\ r <= &0 ==> rfs_vball V t x r = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[P2C_VIEW_EXPAND; mfd_ball; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) t`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`; `x:A`; `y:A`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The backward hypothesis of Thm 11.8 from persistence of the balls for    *)
(* positive A (one window dl) and noncollapsing at all earlier times.        *)

let P3H_BACK_FROM_PERSIST = prove
 (`!(hs:num->(A)rfs_history) x ts kappa r0 dl.
     (!A. &0 < A
          ==> ?N. !n. N <= n
                      ==> rfs_persists (rfs_view (hs n))
                            (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                               (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                            (ts n - dl * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                            (ts n)) /\
     (!n. p2c_regular_view (rfs_view (hs n)) /\
          &0 < rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
     (!n s y. s <= ts n /\ y IN topspace(rfs_top_at (hs n) s)
              ==> p3_noncoll_at (rfs_view (hs n)) kappa r0 y s)
     ==> p3_blowup_back (kappa,r0) hs x ts dl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PB") (CONJUNCTS_THEN2 (LABEL_TAC "VF") (LABEL_TAC "NC"))) THEN
  REWRITE_TAC[p3_blowup_back] THEN X_GEN_TAC `A:real` THEN
  USE_THEN "PB" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "P1")) THEN
  ASM_CASES_TAC `&0 < A` THENL
   [USE_THEN "PB" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "PA")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "PA" (fun th -> MP_TAC(MP (SPEC `n:num` th) (ASSUME `N <= n:num`))) THEN
    DISCH_THEN(fun p -> REWRITE_TAC[p] THEN MP_TAC(REWRITE_RULE[P2AH_PERSISTS] p)) THEN
    DISCH_THEN(LABEL_TAC "PN") THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "NC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "PN" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `rfs_vball (rfs_view ((hs:num->(A)rfs_history) n)) ((ts:num->real) n) ((x:num->A) n)
                    (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))) = {}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P3H_VBALL_NONPOS_EMPTY THEN
      USE_THEN "VF" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `A * q <= &0 <=> &0 <= --A * q`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_IN_EMPTY; P2AH_PERSISTS; OPEN_IN_EMPTY] THEN
    USE_THEN "P1" (fun th -> MP_TAC(MP (SPEC `n:num` th) (ASSUME `N1 <= n:num`))) THEN
    REWRITE_TAC[REAL_MUL_LID; P2AH_PERSISTS] THEN MESON_TAC[]]);;

(* MT Claims 17.10-17.11 at rescaled time 0: along a subsequence, one     *)
(* backward window dl for all A (time-0 slice limit, Prop 9.79 canonical    *)
(* neighbourhoods of the limit via Claim 11.6, Prop 2.19 bounded curvature  *)
(* via Claim 11.7, then Claim 17.9 with the uniform bound).                  *)

let P3H_171_START = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa.
              eps <= eps0 /\ &0 < kappa /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
              (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
                       ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
              (!a s. apx_sphere_sep (rfs_top_at (hs a) s) (rfs_atlas_at (hs a) s))
              ==> ?sub dl. p3_subseq sub /\ &0 < dl /\
                           p3_blowup_back (kappa,eps) (hs o sub) (x o sub) (ts o sub) dl`,
  (GEN_TAC THEN STRIP_TAC) THEN
  (MP_TAC(ISPEC `u:A->bool` P3H_171_REGION_CEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "REG")))) THEN
  (MP_TAC(ISPEC `u:A->bool` P3H_171_SEQ179U_CEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UNI")))) THEN
  (MP_TAC(ISPECL [`u:A->bool`; `(:real^3)`] P2BU_CLAIM_11_6_GEN) THEN
  REWRITE_TAC[P2C_REQ_SLICE_FIX] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `eps1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C116")))))) THEN
  (MP_TAC(MATCH_MP P2B_NONNEG_BOUNDED_SLICE_ROUTE (ISPEC `(:real^3)` P2AS_PROP_2_19_SEP)) THEN
  REWRITE_TAC[P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BS")))) THEN
  (EXISTS_TAC `min (min e1 e2) (min eps1 (eb / K1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (CONJUNCTS_THEN2 (LABEL_TAC "NC") (LABEL_TAC "SEP")))))) THEN
  (USE_THEN "CEX" (STRIP_ASSUME_TAC o REWRITE_RULE[p3h_cexseq])) THEN
  (USE_THEN "REG" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`]) THEN
  USE_THEN "CEX" (fun c -> REWRITE_TAC[c; ASSUME `eps <= e1`]) THEN DISCH_THEN(LABEL_TAC "RG")) THEN
  (SUBGOAL_THEN `!n. p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) n)) /\
                    rfs_history_ok (hs n) /\ rfs_pinched (rfs_view (hs n)) /\
                    (x:num->A) n IN topspace(rfs_top_at (hs n) (ts n)) /\
                    &0 < rfs_vscalar (rfs_view (hs n)) (ts n) (x n)`
  (LABEL_TAC "VF") THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
    SUBGOAL_THEN `rfs_history_ok ((hs:num->(A)rfs_history) n) /\ rfs_pinched (rfs_view (hs n))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) ((dlt:num->real) n)
                     ((rs':num->num->real) n,(ks':num->num->real) n,(dd:num->num->real) n)
                     ((hs:num->(A)rfs_history) n)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
      REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((r:num->real) n pow 2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < eps /\ &2 <= C` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst] THEN SIMP_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `?eta N'. &0 < eta /\
             !n. N' <= n
                 ==> ?v. mfd_has_volume (rfs_top_at ((hs:num->(A)rfs_history) n) (ts n),
                                         rfs_atlas_at (hs n) (ts n))
                           (rfs_metric_at (hs n) (ts n))
                           (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                              (eta * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))) v /\
                         kappa * (eta * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))) pow 3
                         <= v`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "RG" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `dl1:real` (X_CHOOSE_THEN `K1':real` (X_CHOOSE_THEN `N1:num`
      STRIP_ASSUME_TAC))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[P2AH_VIEW_PARTS]) THEN
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `ts:num->real`;
                   `kappa:real`; `eps:real`; `dl1:real`; `K1':real`; `N1:num`] P2BU_SEQ_VOL) THEN
    REWRITE_TAC[P2AH_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "NC" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      USE_THEN "VF" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC]) THEN
  (MP_TAC(ISPEC `u:A->bool` P2CY_THM_5_11) THEN REWRITE_TAC[P2_THM_5_11_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`hs:num->(A)rfs_history`; `x:num->A`; `ts:num->real`;
    `\n. rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) ((x:num->A) n)`]) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "VF" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      USE_THEN "RG" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `dA:real` (X_CHOOSE_THEN `CA:real` (X_CHOOSE_THEN `N:num`
        STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`CA:real`; `dA:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[real_div] THEN SIMP_TAC[];
      MAP_EVERY EXISTS_TAC [`eta:real`; `kappa:real`; `N':num`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (REWRITE_TAC[o_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:(real^3)topology`
    (X_CHOOSE_THEN `atlas:((real^3->bool)#(real^3->real^3))->bool`
    (X_CHOOSE_THEN `g:real^3->real^3^3` (X_CHOOSE_THEN `xl:real^3` STRIP_ASSUME_TAC)))))) THEN
  (MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n))`;
                 `\n. (x:num->A) ((sub:num->num) n)`;
                 `\n. (ts:num->real) ((sub:num->num) n)`;
                 `\n. rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n)))
                        ((ts:num->real) (sub n)) ((x:num->A) (sub n))`;
                 `top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                 `g:real^3->real^3^3`; `xl:real^3`] P2CO_P3_SLICE_RESTRICT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN
    USE_THEN "VF" (MP_TAC o SPEC `(sub:num->num) n`) THEN
    REWRITE_TAC[p2c_regular_view] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `top' = subtopology top {y | mfd_joinable (top:(real^3)topology,
                 atlas:((real^3->bool)#(real^3->real^3))->bool) xl y}` THEN
  ABBREV_TAC `atlas' = restrict_atlas (atlas:((real^3->bool)#(real^3->real^3))->bool)
                 {y | mfd_joinable (top:(real^3)topology,atlas) xl y}` THEN
  ABBREV_TAC `g' = restrict_metric (atlas:((real^3->bool)#(real^3->real^3))->bool)
                 {y | mfd_joinable (top:(real^3)topology,atlas) xl y} (g:real^3->real^3^3)` THEN
  REWRITE_TAC[P2C_SLICE_LIMIT_WITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:num->real^3->bool` (X_CHOOSE_THEN `phi:num->real^3->A` (LABEL_TAC "SL"))))
    ASSUME_TAC)) THEN
  (SUBGOAL_THEN `p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds)
                  ((dlt:num->real) o sub,(r:num->real) o sub,(rs':num->num->real) o sub,
                   (ks':num->num->real) o sub,(dd:num->num->real) o sub,
                   (hs:num->(A)rfs_history) o sub,(ts:num->real) o sub,(x:num->A) o sub)`
  (LABEL_TAC "CEXS") THENL
   [MATCH_MP_TAC P3H_CEXSEQ_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (USE_THEN "REG" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
     `(dlt:num->real) o (sub:num->num)`; `(r:num->real) o (sub:num->num)`; `(rs':num->(num->real)) o (sub:num->num)`;
     `(ks':num->(num->real)) o (sub:num->num)`; `(dd:num->(num->real)) o (sub:num->num)`;
     `(hs:num->(A)rfs_history) o (sub:num->num)`; `(ts:num->real) o (sub:num->num)`; `(x:num->A) o (sub:num->num)`]) THEN
  USE_THEN "CEXS" (fun c -> REWRITE_TAC[c; ASSUME `eps <= e1`]) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(LABEL_TAC "RGS")) THEN
  (SUBGOAL_THEN
   `!A l. &0 < A
          ==> ?CAl N. !n y. N <= n /\
                  y IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n)))
                         ((ts:num->real) (sub n)) ((x:num->A) (sub n))
                         (A * inv(sqrt(rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) (x (sub n)))))
                  ==> p3_vderiv2 (rfs_view (hs (sub n))) l (ts (sub n)) y <=
                      CAl * rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) (x (sub n)) pow (l + 2)`
  (LABEL_TAC "SHI") THENL
   [MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n))`;
                   `\n. (x:num->A) ((sub:num->num) n)`; `\n. (ts:num->real) ((sub:num->num) n)`]
                  P2BU_SEQ_SHI) THEN
    BETA_TAC THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "VF" (MP_TAC o SPEC `(sub:num->num) n`) THEN
      REWRITE_TAC[P2AH_VIEW_PARTS] THEN SIMP_TAC[];
      USE_THEN "RGS" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `A:real` THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      REWRITE_TAC[P2AH_VIEW_PARTS] THEN MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN
      USE_THEN "VF" (MP_TAC o SPEC `(sub:num->num) n`) THEN SIMP_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!y. y IN topspace (top':(real^3)topology) /\
                    &4 < mfd_scalar (atlas':((real^3->bool)#(real^3->real^3))->bool)
                                    (g':real^3->real^3^3) y
                    ==> ?U. rfs_canonical_nbhd (top',atlas') g' (&2 * C) (K1 * eps) y U`
  (LABEL_TAC "CANL") THENL
   [USE_THEN "C116" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `\n. rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n))`;
       `\n. (x:num->A) ((sub:num->num) n)`; `\n. (ts:num->real) ((sub:num->num) n)`;
       `\n. rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n)))
              ((ts:num->real) (sub n)) ((x:num->A) (sub n))`;
       `top':(real^3)topology`; `atlas':((real^3->bool)#(real^3->real^3))->bool`;
       `g':real^3->real^3^3`; `xl:real^3`; `W:num->real^3->bool`; `phi:num->real^3->A`]) THEN
    BETA_TAC THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN REWRITE_TAC[P2AH_VIEW_PARTS] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
      REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "VF" (MP_TAC o SPEC `(sub:num->num) n`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `?D. &0 < D /\
        !A. &0 < A
            ==> ?N. !n y. N <= n /\
                          y IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n)))
                                 ((ts:num->real) (sub n)) ((x:num->A) (sub n))
                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n))
                                                 (x (sub n)))))
                          ==> rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) y <=
                              D * rfs_vscalar (rfs_view (hs (sub n))) (ts (sub n)) (x (sub n))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:A->bool`; `(:real^3)`; `&2 * C`; `K1 * eps`;
                   `\n. rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n))`;
                   `\n. (x:num->A) ((sub:num->num) n)`; `\n. (ts:num->real) ((sub:num->num) n)`;
                   `top':(real^3)topology`; `atlas':((real^3->bool)#(real^3->real^3))->bool`;
                   `g':real^3->real^3^3`; `xl:real^3`; `W:num->real^3->bool`;
                   `phi:num->real^3->A`] P2BU_CLAIM_11_7) THEN
    BETA_TAC THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[P2CP_THM_5_33] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "BS" (fun th -> MATCH_MP_TAC(SPECL [`&2 * C`; `K1 * eps`] th)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `eps <= eb / K1` THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= K ==> &0 < K`] THEN REAL_ARITH_TAC];
      X_GEN_TAC `n:num` THEN USE_THEN "VF" (MP_TAC o SPEC `(sub:num->num) n`) THEN
      REWRITE_TAC[P2AH_VIEW_PARTS; P2C_HIST_NEG_EMPTY] THEN SIMP_TAC[] THEN
      USE_THEN "SEP" (fun th -> REWRITE_TAC[th]);
      MP_TAC(ISPECL [`\m. rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) m)) ((ts:num->real) m)
                               ((x:num->A) m)`; `sub:num->num`] P2BU_QINF_SUBSEQ) THEN
      BETA_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (USE_THEN "UNI" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
     `(dlt:num->real) o (sub:num->num)`; `(r:num->real) o (sub:num->num)`;
     `(rs':num->(num->real)) o (sub:num->num)`; `(ks':num->(num->real)) o (sub:num->num)`;
     `(dd:num->(num->real)) o (sub:num->num)`; `(hs:num->(A)rfs_history) o (sub:num->num)`;
     `(ts:num->real) o (sub:num->num)`; `(x:num->A) o (sub:num->num)`; `D:real`]) THEN
  USE_THEN "CEXS" (fun c -> REWRITE_TAC[c; ASSUME `eps <= e2`]) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PB")))) THEN
  (MAP_EVERY EXISTS_TAC [`sub:num->num`; `dl:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3H_BACK_FROM_PERSIST THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [USE_THEN "PB" ACCEPT_TAC;
    X_GEN_TAC `n:num` THEN USE_THEN "VF" (MP_TAC o SPEC `(sub:num->num) n`) THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "NC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]));;

(* ========================================================================= *)
(* Prop 17.1, the maximal backward time T' as a supremum over subsequences  *)
(* (MT p. 408 takes "the maximum possible value" of t' without fixing the   *)
(* subsequence; the extension past T' holds only along a further            *)
(* subsequence, so the maximum is taken over nested subsequences).          *)
(* Abstract lemmas: nested subsequences and their diagonal, selections as   *)
(* compositions, and P3H_SUBSEQ_SUP.                                         *)
(* ========================================================================= *)

let P3H_SUBSEQ_COMP = prove
 (`!s k. p3_subseq s /\ p3_subseq k ==> p3_subseq (s o k)`,
  REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[]);;

let P3H_SUBSEQ_LT_EQ = prove
 (`!s a b. p3_subseq s ==> (s a < s b <=> a < b)`,
  REWRITE_TAC[p3_subseq] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `a:num`]) THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      UNDISCH_TAC `(s:num->num) a < s b` THEN ASM_REWRITE_TAC[LT_REFL]];
    FIRST_X_ASSUM(ACCEPT_TAC o SPECL [`a:num`; `b:num`])]);;

let P3H_NEST_SEL = prove
 (`!S:num->num->num.
     (!m. ?r. p3_subseq r /\ S (SUC m) = S m o r)
     ==> !d m i. ?i'. i <= i' /\ S (m + d) i = S m i'`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "NS") THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN EXISTS_TAC `i:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `i:num`] THEN
  USE_THEN "NS" (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC o SPEC `m + d:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i':num` STRIP_ASSUME_TAC o SPECL [`m:num`; `(r:num->num) i`] o
    check (fun th -> is_forall(concl th) && not(can (find_term (fun t -> t = `SUC`)) (concl th)))) THEN
  EXISTS_TAC `i':num` THEN ASM_REWRITE_TAC[ADD_CLAUSES; o_THM] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(r:num->num) i` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num->num` P3H_SUBSEQ_GE) THEN ASM_SIMP_TAC[]);;

let P3H_NEST_DIAG = prove
 (`!S:num->num->num.
     (!m. p3_subseq (S m)) /\ (!m. ?r. p3_subseq r /\ S (SUC m) = S m o r)
     ==> p3_subseq (\n. S n n) /\
         !m j. m <= j ==> ?j'. j <= j' /\ S j j = S m j'`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SQ") (LABEL_TAC "NS")) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3_subseq] THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "NS" (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    USE_THEN "SQ" (fun th -> REWRITE_TAC[MATCH_MP P3H_SUBSEQ_LT_EQ (SPEC `n:num` th)]) THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `SUC n` THEN REWRITE_TAC[LT] THEN
    MP_TAC(SPEC `r:num->num` P3H_SUBSEQ_GE) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "NS" (MP_TAC o SPECL [`j - m:num`; `m:num`; `j:num`] o MATCH_MP P3H_NEST_SEL) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `m <= j ==> m + j - m = j:num`]]);;

let P3H_SEL_COMP = prove
 (`!s1 s2 N. p3_subseq s1 /\ p3_subseq s2 /\
             (!j. N <= j ==> ?j'. j <= j' /\ s2 j = s1 j')
             ==> ?r. p3_subseq r /\ !j. N <= j ==> s1 (r j) = s2 j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S1") (CONJUNCTS_THEN2 (LABEL_TAC "S2") MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num` (LABEL_TAC "C")) THEN
  EXISTS_TAC `\j. if j < N then j else (c:num->num) j` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE] THEN
    USE_THEN "C" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[p3_subseq] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `b < N:num` THENL
   [SUBGOAL_THEN `a < N:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "C" (MP_TAC o SPEC `b:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `a < N:num` THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "C" (MP_TAC o SPEC `a:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "S1" (fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP P3H_SUBSEQ_LT_EQ th)]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(s1:num->num) ((c:num->num) a)`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(s1:num->num) ((c:num->num) b)`)) THEN
  USE_THEN "S2" (fun th -> REWRITE_TAC[MATCH_MP P3H_SUBSEQ_LT_EQ th]) THEN ASM_REWRITE_TAC[]);;

(* The maximal backward time over nested subsequences: P s Tb monotone in  *)
(* Tb, inherited by tail selections, true at 0, and extendable past every   *)
(* Tb >= 0 below which it holds, along a further subsequence; then one     *)
(* subsequence has it for all Tb.  (Nested near-maximal choices with the   *)
(* bounded potential atn, the diagonal, and the extension at the diagonal.) *)

let P3H_SUBSEQ_SUP = prove
 (`!P:(num->num)->real->bool.
     (!s Tb Tc. P s Tb /\ Tc <= Tb ==> P s Tc) /\
     (!s1 s2 Tb N. P s1 Tb /\ (!j. N <= j ==> ?j'. j <= j' /\ s2 j = s1 j') ==> P s2 Tb) /\
     (!s. P s (&0)) /\
     (!s Tb. p3_subseq s /\ &0 <= Tb /\ (!Tc. Tc < Tb ==> P s Tc)
            ==> ?k d. p3_subseq k /\ &0 < d /\ P (s o k) (Tb + d))
     ==> ?s. p3_subseq s /\ !Tb. P s Tb`,
  (GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MO") (CONJUNCTS_THEN2 (LABEL_TAC "SEL")
    (CONJUNCTS_THEN2 (LABEL_TAC "ZE") (LABEL_TAC "EXT")))) THEN
  REFUTE_THEN(LABEL_TAC "NEG" o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`; NOT_FORALL_THM])) THEN
  (SUBGOAL_THEN `?f:(num->num)->real. !s. f s = sup {atn Tb | P s Tb}`
   (X_CHOOSE_THEN `f:(num->num)->real` (LABEL_TAC "FD")) THENL
   [EXISTS_TAC `\s:num->num. sup {atn Tb | (P:(num->num)->real->bool) s Tb}` THEN REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!s:num->num. ~({atn Tb | (P:(num->num)->real->bool) s Tb} = {}) /\
                  (!y. y IN {atn Tb | P s Tb} ==> y <= pi / &2)`
   (LABEL_TAC "FS") THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`atn(&0)`; `&0`] THEN USE_THEN "ZE" (fun th -> REWRITE_TAC[th]);
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[ATN_BOUNDS]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `(!s:num->num. &0 <= f s /\ f s <= pi / &2) /\
                (!s Tb. (P:(num->num)->real->bool) s Tb ==> atn Tb <= f s) /\
                (!s Tb. atn Tb < f s ==> P s Tb)`
   (CONJUNCTS_THEN2 (LABEL_TAC "FB") (CONJUNCTS_THEN2 (LABEL_TAC "F1") (LABEL_TAC "F2"))) THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "FD" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_SUP THEN
        MAP_EVERY EXISTS_TAC [`pi / &2`; `atn(&0)`] THEN
        USE_THEN "FS" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `s:num->num` th)]) THEN
        REWRITE_TAC[ATN_0; REAL_LE_REFL; IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
        USE_THEN "ZE" (fun th -> REWRITE_TAC[th; ATN_0]);
        MATCH_MP_TAC REAL_SUP_LE THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th])];
      REPEAT STRIP_TAC THEN USE_THEN "FD" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_SUP THEN
      MAP_EVERY EXISTS_TAC [`pi / &2`; `atn Tb`] THEN
      USE_THEN "FS" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `s:num->num` th)]) THEN
      REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN EXISTS_TAC `Tb:real` THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN USE_THEN "FD" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`{atn Tb | (P:(num->num)->real->bool) s Tb}`; `atn Tb`] SUP_APPROACH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [USE_THEN "FS" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `pi / &2` THEN
        USE_THEN "FS" (fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real` (CONJUNCTS_THEN2 (X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC)
        ASSUME_TAC)) THEN
      USE_THEN "MO" MATCH_MP_TAC THEN EXISTS_TAC `T1:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ONCE_REWRITE_TAC[GSYM ATN_MONO_LT_EQ] THEN
      ASM_MESON_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!s:num->num. p3_subseq s ==> f s < pi / &2` (LABEL_TAC "F3") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "NEG" (fun th -> X_CHOOSE_TAC `T0:real`
      (MP (SPEC `s:num->num` th) (ASSUME `p3_subseq (s:num->num)`))) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `atn T0` THEN REWRITE_TAC[ATN_BOUNDS] THEN
    USE_THEN "FD" (fun th -> REWRITE_TAC[th]) THEN MATCH_MP_TAC REAL_SUP_LE THEN
    USE_THEN "FS" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN DISCH_THEN(X_CHOOSE_THEN `Tb:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[ATN_MONO_LE_EQ] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(P:(num->num)->real->bool) s T0` THEN REWRITE_TAC[] THEN
    USE_THEN "MO" MATCH_MP_TAC THEN EXISTS_TAC `Tb:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!s1 s2 N. (!j. N <= j ==> ?j'. j <= j' /\ (s2:num->num) j = s1 j')
                          ==> f s1 <= f s2` (LABEL_TAC "F4") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "FD" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
    USE_THEN "FS" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `Tb:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `Tb:real` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "SEL" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s1:num->num`; `N:num`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `pi / &2` THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th])];
    ALL_TAC]) THEN
  (REMOVE_THEN "FD" (K ALL_TAC) THEN REMOVE_THEN "FS" (K ALL_TAC)) THEN
  (SUBGOAL_THEN `!s:num->num. p3_subseq s ==> ?k. p3_subseq k /\ f s < f (s o k)`
   (LABEL_TAC "F5") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `atn(tan(f(s:num->num))) = f s` (LABEL_TAC "AT") THENL
     [MATCH_MP_TAC TAN_ATN THEN
      USE_THEN "F3" (fun th -> MP_TAC(MP (SPEC `s:num->num` th) (ASSUME `p3_subseq (s:num->num)`))) THEN
      USE_THEN "FB" (MP_TAC o SPEC `s:num->num`) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "EXT" (MP_TAC o SPECL [`s:num->num`; `tan(f(s:num->num))`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ONCE_REWRITE_TAC[GSYM ATN_MONO_LE_EQ] THEN USE_THEN "AT" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[ATN_0] THEN USE_THEN "FB" (fun th -> REWRITE_TAC[th]);
        X_GEN_TAC `Tc:real` THEN DISCH_TAC THEN USE_THEN "F2" MATCH_MP_TAC THEN
        USE_THEN "AT" (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
        ASM_REWRITE_TAC[ATN_MONO_LT_EQ]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num->num` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `k:num->num` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `atn(tan(f(s:num->num)) + d)` THEN
    CONJ_TAC THENL
     [USE_THEN "AT" (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
      REWRITE_TAC[ATN_MONO_LT_EQ] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "F1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `?g:(num->num)->real. !s. g s = sup {f (s o k) | k | p3_subseq k}`
   (X_CHOOSE_THEN `g:(num->num)->real` (LABEL_TAC "GD")) THENL
   [EXISTS_TAC `\s:num->num. sup {(f:(num->num)->real) (s o k) | k | p3_subseq k}` THEN
    REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!s:num->num. ~({(f:(num->num)->real) (s o k) | k | p3_subseq k} = {}) /\
                  (!y. y IN {f (s o k) | k | p3_subseq k} ==> y <= pi / &2)`
   (LABEL_TAC "GS") THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`(f:(num->num)->real) ((s:num->num) o I)`; `I:num->num`] THEN
      REWRITE_TAC[p3_subseq; I_THM];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "FB" (fun th -> REWRITE_TAC[th])];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `(!s:num->num. g s <= pi / &2) /\
                (!s k. p3_subseq k ==> f ((s:num->num) o k) <= g s) /\
                (!s c. c < g (s:num->num) ==> ?k. p3_subseq k /\ c < f (s o k))`
   (CONJUNCTS_THEN2 (LABEL_TAC "GB") (CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G3"))) THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "GD" (fun th -> REWRITE_TAC[th]) THEN MATCH_MP_TAC REAL_SUP_LE THEN
      USE_THEN "GS" (fun th -> REWRITE_TAC[th]);
      REPEAT STRIP_TAC THEN USE_THEN "GD" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_SUP THEN
      MAP_EVERY EXISTS_TAC [`pi / &2`; `(f:(num->num)->real) ((s:num->num) o k)`] THEN
      USE_THEN "GS" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `s:num->num` th)]) THEN
      REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN EXISTS_TAC `k:num->num` THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN USE_THEN "GD" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`{(f:(num->num)->real) ((s:num->num) o k) | k | p3_subseq k}`; `c:real`]
        SUP_APPROACH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [USE_THEN "GS" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `pi / &2` THEN
        USE_THEN "GS" (fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!s k. p3_subseq k ==> g ((s:num->num) o k) <= g s` (LABEL_TAC "G4") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "GD" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC REAL_SUP_LE THEN USE_THEN "GS" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `k':num->num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `y:real`)) THEN
    REWRITE_TAC[GSYM o_ASSOC] THEN
    USE_THEN "G1" MATCH_MP_TAC THEN MATCH_MP_TAC P3H_SUBSEQ_COMP THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (REMOVE_THEN "GD" (K ALL_TAC) THEN REMOVE_THEN "GS" (K ALL_TAC)) THEN
  (SUBGOAL_THEN `!s:num->num. p3_subseq s ==> f s < g s` (LABEL_TAC "G2") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "F5" (fun th -> X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC
      (MP (SPEC `s:num->num` th) (ASSUME `p3_subseq (s:num->num)`))) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(f:(num->num)->real) ((s:num->num) o k)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "G1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `?ch:(num->num)->(num->num).
                  !s. p3_subseq s ==> p3_subseq (ch s) /\ (f s + g s) / &2 < f (s o ch s)`
   (X_CHOOSE_THEN `ch:(num->num)->(num->num)` (LABEL_TAC "CH")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `s:num->num` THEN
    ASM_CASES_TAC `p3_subseq (s:num->num)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "G3" MATCH_MP_TAC THEN
    USE_THEN "G2" (fun th -> MP_TAC(MP (SPEC `s:num->num` th) (ASSUME `p3_subseq (s:num->num)`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (MP_TAC(prove_recursive_functions_exist num_RECURSION
    `(S:num->num->num) 0 = I /\ !m. S (SUC m) = S m o (ch:(num->num)->(num->num)) (S m)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:num->num->num` (CONJUNCTS_THEN2 (LABEL_TAC "S0") (LABEL_TAC "SS")))) THEN
  (SUBGOAL_THEN `!m. p3_subseq ((S:num->num->num) m)` (LABEL_TAC "S1") THENL
   [INDUCT_TAC THENL
     [USE_THEN "S0" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[p3_subseq; I_THM];
      USE_THEN "SS" (fun th -> REWRITE_TAC[th]) THEN MATCH_MP_TAC P3H_SUBSEQ_COMP THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "CH" (fun th -> MP_TAC(MP (SPEC `(S:num->num->num) m` th)
        (ASSUME `p3_subseq ((S:num->num->num) m)`))) THEN SIMP_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `(!m. ?r. p3_subseq r /\ (S:num->num->num) (SUC m) = S m o r) /\
                (!m. (f (S m) + g (S m)) / &2 < f ((S:num->num->num) (SUC m))) /\
                (!m. g ((S:num->num->num) (SUC m)) <= g (S m))`
   (CONJUNCTS_THEN2 (LABEL_TAC "S2") (CONJUNCTS_THEN2 (LABEL_TAC "S3") (LABEL_TAC "S4"))) THENL
   [REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN
    USE_THEN "S1" (fun s1 -> USE_THEN "CH" (fun th -> MP_TAC(MP (SPEC `(S:num->num->num) m` th)
      (SPEC `m:num` s1)))) THEN
    STRIP_TAC THEN USE_THEN "SS" (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `(ch:(num->num)->(num->num)) ((S:num->num->num) m)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "G4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!m. g ((S:num->num->num) m) - f (S m) <= (pi / &2) * inv(&2) pow m`
   (LABEL_TAC "S5") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
      USE_THEN "GB" (MP_TAC o SPEC `(S:num->num->num) 0`) THEN
      USE_THEN "FB" (MP_TAC o SPEC `(S:num->num->num) 0`) THEN REAL_ARITH_TAC;
      USE_THEN "S3" (MP_TAC o SPEC `m:num`) THEN USE_THEN "S4" (MP_TAC o SPEC `m:num`) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th)) &&
        can (find_term (fun t -> t = `pi`)) (concl th))) THEN
      REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `?D. p3_subseq D /\ !m j. m <= j ==> ?j'. j <= j' /\ D j = (S:num->num->num) m j'`
   (X_CHOOSE_THEN `D:num->num` (CONJUNCTS_THEN2 (LABEL_TAC "DS") (LABEL_TAC "DN"))) THENL
   [MP_TAC(ISPEC `S:num->num->num` P3H_NEST_DIAG) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [USE_THEN "S1" ACCEPT_TAC; USE_THEN "S2" ACCEPT_TAC]; ALL_TAC] THEN
    STRIP_TAC THEN EXISTS_TAC `\n. (S:num->num->num) n n` THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!m. f ((S:num->num->num) m) <= f (D:num->num)` (LABEL_TAC "DF") THENL
   [X_GEN_TAC `m:num` THEN USE_THEN "F4" MATCH_MP_TAC THEN EXISTS_TAC `m:num` THEN
    USE_THEN "DN" (ACCEPT_TAC o SPEC `m:num`);
    ALL_TAC]) THEN
  (USE_THEN "F5" (fun th -> X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC
    (MP (SPEC `D:num->num` th) (ASSUME `p3_subseq (D:num->num)`)))) THEN
  (SUBGOAL_THEN `!m. f ((D:num->num) o (k:num->num)) <= g ((S:num->num->num) m)` (LABEL_TAC "DG") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`(S:num->num->num) m`; `(D:num->num) o (k:num->num)`; `m:num`] P3H_SEL_COMP) THEN
    ANTS_TAC THENL
     [USE_THEN "S1" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3H_SUBSEQ_COMP THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        USE_THEN "DN" (MP_TAC o SPECL [`m:num`; `(k:num->num) j`]) THEN ANTS_TAC THENL
         [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(SPEC `k:num->num` P3H_SUBSEQ_GE) THEN ASM_SIMP_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `j':num` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(k:num->num) j` THEN
        ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `k:num->num` P3H_SUBSEQ_GE) THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RR"))) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `f((S:num->num->num) m o (r:num->num)):real` THEN
    CONJ_TAC THENL
     [USE_THEN "F4" MATCH_MP_TAC THEN EXISTS_TAC `m:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      EXISTS_TAC `j:num` THEN REWRITE_TAC[LE_REFL] THEN
      REMOVE_THEN "RR" (MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[o_THM];
      USE_THEN "G1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`inv(&2)`; `(f((D:num->num) o (k:num->num)) - f D) / (pi / &2)`]
    REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `(pi / &2) * inv(&2) pow m < f((D:num->num) o (k:num->num)) - f D` MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SUBGOAL_THEN `&0 < pi / &2` ASSUME_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `m:num`)) (concl th) &&
      not(is_forall(concl th)))) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
    ALL_TAC] THEN
  USE_THEN "S5" (MP_TAC o SPEC `m:num`) THEN USE_THEN "DF" (MP_TAC o SPEC `m:num`) THEN
  USE_THEN "DG" (MP_TAC o SPEC `m:num`) THEN REAL_ARITH_TAC));;

(* ========================================================================= *)
(* Prop 17.1, Lemma 11.2 and the small balls at an earlier base time t0 <=  *)
(* ts (used past the maximal backward time T', MT p. 408): the scale is     *)
(* still Q = R(x, ts); canonical neighbourhoods at all times <= ts above 2 Q *)
(* (worst bad point), so the proofs of P3H_171_BACK_BOUND and               *)
(* P3H_171_SMALLBALL carry over with the base time t0.                      *)
(* ========================================================================= *)

let P3H_171_BACK_BOUND_AT = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x t0 z t' rr D.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              t0 <= ts /\ z IN topspace(rfs_top_at hs t0) /\ &0 <= D /\
              rfs_vscalar (rfs_view hs) t0 z <= D * rfs_vscalar (rfs_view hs) ts x /\
              &0 < rr /\ rr <= inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x)) /\
              t' <= t0 /\
              t0 - t' <= inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) /\
              rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 z rr) t' t0
              ==> !s y. t' < s /\ s <= t0 /\ y IN rfs_vball (rfs_view hs) t0 z rr
                        ==> rfs_vscalar (rfs_view hs) s y <=
                            &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x`,
  GEN_TAC THEN REWRITE_TAC[P2_LEMMA_11_2_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "112"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                   (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(inv(sqrt(&2 * Q)) pow 2) = &2 * Q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; REAL_INV_INV] THEN MATCH_MP_TAC SQRT_POW_2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "112" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`;
    `inv(sqrt(&2 * Q))`; `z:A`; `t0:real`; `t':real`; `rr:real`]) THEN
  ASM_SIMP_TAC[REAL_ARITH `t' <= t0 ==> min t0 t' = t' /\ max t0 t' = t0`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                     `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`;
                     `ks:num->real`; `ds:num->real`; `dlt:real`; `rs':num->real`;
                     `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
                     `ts:real`; `x:A`; `&2`] P3H_171_CANON_ABOVE) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&2 * C * sqrt((D + &2) * Q))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN
        SUBGOAL_THEN `&0 <= D * Q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_ARITH `t' <= t0 ==> abs(t' - t0) = t0 - t'`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&16 * C * (D + &2) * Q)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= D * Q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (max (&0) (rfs_vscalar (rfs_view (hs:(A)rfs_history)) t0 z) + &2 * Q)` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D * Q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
let P3H_171_SMALLBALL_AT = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x t0 z D.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              t0 <= ts /\ z IN topspace(rfs_top_at hs t0) /\ &0 <= D /\
              rfs_vscalar (rfs_view hs) t0 z <= D * rfs_vscalar (rfs_view hs) ts x /\
              inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < t0
              ==> (rfs_persists (rfs_view hs)
                     (rfs_vball (rfs_view hs) t0 z
                        (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x))))
                     (t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) t0 /\
                   !s y. t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < s /\
                         s <= t0 /\
                         y IN rfs_vball (rfs_view hs) t0 z
                                (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x)))
                         ==> rfs_vscalar (rfs_view hs) s y <=
                             &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x) \/
                  (?k j y. 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                           t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) <
                           hs_time hs k /\
                           hs_time hs k < t0 /\
                           y IN rfs_vball (rfs_view hs) t0 z
                                  (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x))) /\
                           y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                           p3_flowline hs y (hs_time hs k) t0 /\
                           (!s. hs_time hs k <= s /\ s <= t0
                                ==> rfs_vscalar (rfs_view hs) s y <=
                                    &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) \/
                  (?k j y. 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                           hs_time hs k = t0 /\
                           y IN rfs_vball (rfs_view hs) t0 z
                                  (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x))) /\
                           y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_BACK_BOUND_AT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BB"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                   (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  ABBREV_TAC `rr = inv(&2 * C * sqrt((D + &2) * Q))` THEN
  ABBREV_TAC `eta = inv(&16 * C * (D + &2) * Q)` THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) t0 z rr` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rr /\ &0 < eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN EXPAND_TAC "eta" THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (rfs_top_at (hs:(A)rfs_history) t0) /\
                smooth_manifold_atlas (rfs_top_at hs t0) (rfs_atlas_at hs t0) /\
                riemannian_metric (rfs_atlas_at hs t0) (rfs_metric_at hs t0)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t0:real`; `z:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) t0) W /\ (z:A) IN W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[rfs_vball; rfs_view] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t0 < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W (t0 - eta) t0` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    REMOVE_THEN "BB" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
       `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:real`;
       `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
       `ts:real`; `x:A`; `t0:real`; `z:A`; `t0 - eta`; `rr:real`; `D:real`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `t0 - eta`; `t0:real`]
                P3H_PERSIST_INF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `T1:real = t0` THENL
   [DISJ2_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `t0:real`] P3H_EXPOSED_AT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  SUBGOAL_THEN `T1 < t0 /\ &0 < T1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `T1:real`; `t0:real`] P3H_EXPOSED_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    REWRITE_RULE[DISJOINT] o check (fun th -> is_neg(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> concl th =
    `(y:A) IN W /\ y IN IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) j) (cball(vec 0,&1))`)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `y:A`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) T1) W` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `hs_time (hs:(A)rfs_history) k = T1`)) THEN
    MATCH_MP_TAC P3H_OPEN_AT_EVENT THEN EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3_flowline] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s':real = T1` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      UNDISCH_TAC `open_in (rfs_top_at (hs:(A)rfs_history) T1) W` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W T1 t0` THEN
      REWRITE_TAC[rfs_view; rfs_persists] THEN DISCH_THEN(MP_TAC o SPEC `s':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. T1 < s /\ s <= t0
                    ==> rfs_vscalar (rfs_view (hs:(A)rfs_history)) s y <= &2 * (D + &2) * Q`
  (LABEL_TAC "B1") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REMOVE_THEN "BB" (MP_TAC o SPECL
      [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
       `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:real`;
       `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
       `ts:real`; `x:A`; `t0:real`; `z:A`; `T1:real`; `rr:real`; `D:real`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = T1` THENL
   [ALL_TAC; USE_THEN "B1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MP_TAC(ISPECL [`\u. rfs_vscalar (rfs_view (hs:(A)rfs_history)) u y`; `T1:real`;
                 `(T1 + t0) / &2`; `&2 * (D + &2) * Q`] P3H_CONT_RIGHT_LE) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2C_VIEW_SCALAR_CONT_FROM THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `t0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (rfs_view (hs:(A)rfs_history)) T1) W` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[rfs_view; rfs_vtop]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s'':real` THEN STRIP_TAC THEN USE_THEN "B1" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* A set persisting over (a, b] with a < T_k <= b misses the caps of event *)
(* k: just before T_k it lies in the old stage, whose topspace is disjoint *)
(* from the cut cores (rfs_event_ok).                                       *)

let P3H_PERSIST_CAPS_DISJOINT = prove
 (`!(hs:(A)rfs_history) W a b k j.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
     rfs_persists (rfs_view hs) W a b /\ a < hs_time hs k /\ hs_time hs k <= b
     ==> DISJOINT W (IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs k` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?s. a < s /\ s <= b /\ hs_time (hs:(A)rfs_history) (k - 1) <= s /\
                    s < hs_time hs k`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(max a (hs_time (hs:(A)rfs_history) (k - 1)) + hs_time hs k) / &2` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`; ARITH_RULE `k <= n ==> k - 1 <= n`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `W SUBSET topspace(hs_top (hs:(A)rfs_history) (k - 1))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (topspace(hs_top (hs:(A)rfs_history) (k - 1)))
                  (mfd_cut_cores (ev_index(hs_event hs k)) (ev_capp(hs_event hs k))
                                 (ev_capm(hs_event hs k)))`
  MP_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[rfs_event_ok] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) j) (cball(vec 0,&1)) SUBSET
                mfd_cut_cores (ev_index(hs_event hs k)) (ev_capp(hs_event hs k))
                              (ev_capm(hs_event hs k))`
  MP_TAC THENL
   [REWRITE_TAC[mfd_cut_cores; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE (ev_capp (hs_event (hs:(A)rfs_history) k) j) (cball(vec 0,&1)) UNION
                IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1))` THEN
    CONJ_TAC THENL [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[IN_UNION]];
    ALL_TAC] THEN
  UNDISCH_TAC `W SUBSET topspace(hs_top (hs:(A)rfs_history) (k - 1))` THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Prop 17.1, persistence past an intermediate time t0 (the step used twice *)
(* in the finite-T' extension, MT p. 408 as repaired here):                *)
(* if the balls W, W' persist over (a, ts] with a < t0, every point of W    *)
(* has R(., t0) <= D Q with its small ball at t0 inside W', R <= Kc Q on   *)
(* W' over (a, ts], and no Lemma 17.7 configuration starts in W', then W    *)
(* persists over (t0 - 1/(16 C (D+2) Q), ts] with R <= max(2(D+2), Kc) Q.  *)
(* ========================================================================= *)

let P3H_LE_MAX_MUL = prove
 (`!a b q r. &0 <= q /\ (r <= a * q \/ r <= b * q) ==> r <= max a b * q`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `a * q <= m /\ b * q <= m ==> (r <= a * q \/ r <= b * q) ==> r <= m`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3H_171_EXT_AT = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x t0 D a W W' Kc.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              &0 <= D /\ a < t0 /\ t0 <= ts /\
              inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < t0 /\
              ~(W = {}) /\ rfs_persists (rfs_view hs) W a ts /\ rfs_persists (rfs_view hs) W' a ts /\
              (!z. z IN W
                   ==> rfs_vscalar (rfs_view hs) t0 z <= D * rfs_vscalar (rfs_view hs) ts x) /\
              (!z. z IN W
                   ==> rfs_vball (rfs_view hs) t0 z
                         (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x)))
                       SUBSET W') /\
              (!s y. a < s /\ s <= ts /\ y IN W'
                     ==> rfs_vscalar (rfs_view hs) s y <= Kc * rfs_vscalar (rfs_view hs) ts x) /\
              ~(?y k j. y IN W' /\ 1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                        t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) <
                        hs_time hs k /\
                        hs_time hs k < ts /\
                        y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                        p3_flowline hs y (hs_time hs k) ts /\
                        (!s. hs_time hs k <= s /\ s <= ts
                             ==> rfs_vscalar (rfs_view hs) s y <=
                                 max (&2 * (D + &2)) Kc * rfs_vscalar (rfs_view hs) ts x))
              ==> rfs_persists (rfs_view hs) W
                    (t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) ts /\
                  (!s y. t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < s /\
                         s <= ts /\ y IN W
                         ==> rfs_vscalar (rfs_view hs) s y <=
                             max (&2 * (D + &2)) Kc * rfs_vscalar (rfs_view hs) ts x)`,
  (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_SMALLBALL_AT) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SB"))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "WORST")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "PW") (CONJUNCTS_THEN2 (LABEL_TAC "PW'")
    (CONJUNCTS_THEN2 (LABEL_TAC "RB") (CONJUNCTS_THEN2 (LABEL_TAC "SBW")
    (CONJUNCTS_THEN2 (LABEL_TAC "KC") (LABEL_TAC "N17"))))))))))))))))))))))) THEN
  (SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ p2c_regular_view (rfs_view hs)`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
     [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                     (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!z:A. z IN W ==> z IN topspace(rfs_top_at hs t0)` (LABEL_TAC "WT") THENL
   [USE_THEN "PW" (MP_TAC o SPEC `t0:real` o REWRITE_RULE[P2AH_PERSISTS]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN REWRITE_TAC[SUBSET];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!z:A. z IN W
          ==> rfs_persists (rfs_view hs)
                (rfs_vball (rfs_view hs) t0 z
                   (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x))))
                (t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x)) t0 /\
              !s y. t0 - inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) < s /\
                    s <= t0 /\
                    y IN rfs_vball (rfs_view hs) t0 z
                           (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x)))
                    ==> rfs_vscalar (rfs_view hs) s y <=
                        &2 * (D + &2) * rfs_vscalar (rfs_view hs) ts x`
   (LABEL_TAC "SBALL") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "SB" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
       `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
       `ds:num->real`; `dlt:real`; `rs':num->real`; `ks':num->real`; `dd:num->real`;
       `hs:(A)rfs_history`; `r':real`; `ts:real`; `x:A`; `t0:real`; `z:A`; `D:real`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (DISJ_CASES_THEN2 MP_TAC MP_TAC)) THENL
     [DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:A`
        STRIP_ASSUME_TAC))) THEN
      USE_THEN "N17" MP_TAC THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MAP_EVERY EXISTS_TAC [`y:A`; `k:num`; `j:num`] THEN
      SUBGOAL_THEN `(y:A) IN W'` ASSUME_TAC THENL
       [USE_THEN "SBW" (fun th -> MP_TAC(MP (SPEC `z:A` th) (ASSUME `(z:A) IN W`))) THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `p3_flowline (hs:(A)rfs_history) y (hs_time hs k) t0` THEN
        REWRITE_TAC[p3_flowline] THEN STRIP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `s':real` THEN STRIP_TAC THEN
        ASM_CASES_TAC `s' <= t0` THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "PW'" (MP_TAC o SPEC `s':real` o REWRITE_RULE[P2AH_PERSISTS]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC P3H_LE_MAX_MUL THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        ASM_CASES_TAC `s <= t0` THENL
         [DISJ1_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          DISJ2_TAC THEN USE_THEN "KC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC]];
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:A`
        STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN `(y:A) IN W'` ASSUME_TAC THENL
       [USE_THEN "SBW" (fun th -> MP_TAC(MP (SPEC `z:A` th) (ASSUME `(z:A) IN W`))) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `W':A->bool`; `a:real`; `ts:real`; `k:num`; `j:num`]
        P3H_PERSIST_CAPS_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `&0 < inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)) /\
    &0 < inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (ABBREV_TAC `rr = inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x))` THEN
  ABBREV_TAC `eta = inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`) THEN
  (SUBGOAL_THEN `!z:A. z IN W
                 ==> smooth_manifold_atlas (rfs_vtop (rfs_view hs) t0) (rfs_vatlas (rfs_view hs) t0) /\
                     riemannian_metric (rfs_vatlas (rfs_view hs) t0) (rfs_vmetric (rfs_view hs) t0) /\
                     z IN topspace(rfs_vtop (rfs_view hs) t0)`
   (LABEL_TAC "SL") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN topspace(rfs_vtop (rfs_view hs) t0)` ASSUME_TAC THENL
     [REWRITE_TAC[P2AH_VIEW_PARTS] THEN USE_THEN "WT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t0:real`; `z:A`] P2C_REGULAR_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!z:A. z IN W ==> z IN rfs_vball (rfs_view hs) t0 z rr` (LABEL_TAC "CEN") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "SL" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `z:A` th) (ASSUME `(z:A) IN W`))) THEN
    REWRITE_TAC[P2C_VIEW_EXPAND] THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `W SUBSET (W':A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "SBW" (fun th -> MP_TAC(MP (SPEC `z:A` th) (ASSUME `(z:A) IN W`))) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN USE_THEN "CEN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W (t0 - eta) t0` (LABEL_TAC "WP") THENL
   [MATCH_MP_TAC P2BU_BALL_PERSIST_UNION THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "PW" (MP_TAC o SPEC `t0:real` o REWRITE_RULE[P2AH_PERSISTS]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[P2AH_VIEW_PARTS] THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      EXISTS_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) t0 z rr` THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "CEN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "SL" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `z:A` th) (ASSUME `(z:A) IN W`))) THEN
        REWRITE_TAC[P2C_VIEW_EXPAND] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
        USE_THEN "SBALL" (MP_TAC o SPEC `z:A`) THEN ASM_SIMP_TAC[]]];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [REWRITE_TAC[P2AH_PERSISTS] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s <= t0` THENL
     [USE_THEN "WP" (MP_TAC o SPEC `s:real` o REWRITE_RULE[P2AH_PERSISTS]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "PW" (MP_TAC o SPEC `s:real` o REWRITE_RULE[P2AH_PERSISTS]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN MATCH_MP_TAC P3H_LE_MAX_MUL THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_CASES_TAC `s <= t0` THENL
     [DISJ1_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      USE_THEN "SBALL" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `y:A` th) (ASSUME `(y:A) IN W`)))) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CEN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN USE_THEN "KC" MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `W SUBSET (W':A->bool)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]));;

(* ========================================================================= *)
(* Prop 17.1, Step B: the A-dependent extension past Tb for                 *)
(* one counterexample (P3H_171_EXT_B_AT) and for the sequence.              *)
(* ========================================================================= *)

(* The closure of a slice ball lies in any larger ball (regular view). *)

let P3H_CLOSURE_VBALL_SUB = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x r r'.
     p2c_regular_view V /\ x IN topspace(rfs_vtop V t) /\ r < r'
     ==> rfs_vtop V t closure_of rfs_vball V t x r SUBSET rfs_vball V t x r'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `mfd_cball (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t,rfs_vatlas V t) (rfs_vmetric V t) x r` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* One counterexample: persistence past Tb by w/2, w = 1/(16 C (D+2)), from *)
(* the persistence of the A-, A2-, A3-balls back to Tb - eta/2, R <= Kc Q *)
(* on the A3-ball there, R <= D Q on the A-ball at Tb - eta and no 17.7   *)
(* configuration in the A2-ball (EXT_AT with VIEW_BALL_IN for the small   *)
(* balls; A2 from the pinching bound on abs Rm).                           *)

let P3H_171_EXT_B_AT = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x
            Tb eta D Kc A A2 A3.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              x IN topspace(rfs_top_at hs ts) /\ &1 <= rfs_vscalar (rfs_view hs) ts x /\
              &0 < A /\ &0 <= D /\ &0 <= Kc /\ &0 < eta /\ eta < Tb /\
              eta <= inv(&16 * C * (D + &2)) / &2 /\
              A2 = A + exp(&2 * (&2 * Kc + &12 + &2 * exp(&4)) * Tb) * inv(&2 * C * sqrt(D + &2)) /\
              A3 = A2 + &1 /\
              inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view hs) ts x) <
              ts - (Tb - eta) * inv(rfs_vscalar (rfs_view hs) ts x) /\
              rfs_persists (rfs_view hs)
                (rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                (ts - (Tb - eta / &2) * inv(rfs_vscalar (rfs_view hs) ts x)) ts /\
              rfs_persists (rfs_view hs)
                (rfs_vball (rfs_view hs) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                (ts - (Tb - eta / &2) * inv(rfs_vscalar (rfs_view hs) ts x)) ts /\
              rfs_persists (rfs_view hs)
                (rfs_vball (rfs_view hs) ts x (A3 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                (ts - (Tb - eta / &2) * inv(rfs_vscalar (rfs_view hs) ts x)) ts /\
              (!s y. ts - (Tb - eta / &2) * inv(rfs_vscalar (rfs_view hs) ts x) < s /\ s <= ts /\
                     y IN rfs_vball (rfs_view hs) ts x (A3 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                     ==> rfs_vscalar (rfs_view hs) s y <= Kc * rfs_vscalar (rfs_view hs) ts x) /\
              (!z. z IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                   ==> rfs_vscalar (rfs_view hs) (ts - (Tb - eta) * inv(rfs_vscalar (rfs_view hs) ts x)) z <=
                       D * rfs_vscalar (rfs_view hs) ts x) /\
              ~(?y k j. y IN rfs_vball (rfs_view hs) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                        1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                        ts - (Tb + &1) * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\
                        hs_time hs k < ts /\
                        y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                        p3_flowline hs y (hs_time hs k) ts /\
                        (!s. hs_time hs k <= s /\ s <= ts
                             ==> rfs_vscalar (rfs_view hs) s y <=
                                 max (&2 * (D + &2)) Kc * rfs_vscalar (rfs_view hs) ts x))
              ==> rfs_persists (rfs_view hs)
                    (rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                    (ts - (Tb + inv(&16 * C * (D + &2)) / &2) * inv(rfs_vscalar (rfs_view hs) ts x)) ts /\
                  (!s y. ts - (Tb + inv(&16 * C * (D + &2)) / &2) * inv(rfs_vscalar (rfs_view hs) ts x) < s /\
                         s <= ts /\
                         y IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                         ==> rfs_vscalar (rfs_view hs) s y <=
                             max (&2 * (D + &2)) Kc * rfs_vscalar (rfs_view hs) ts x)`,
  (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_EXT_AT) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EX"))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "WORST")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "PW") (CONJUNCTS_THEN2 (LABEL_TAC "PW2")
    (CONJUNCTS_THEN2 (LABEL_TAC "PW3") (CONJUNCTS_THEN2 (LABEL_TAC "KC3")
    (CONJUNCTS_THEN2 (LABEL_TAC "RB") (LABEL_TAC "N17"))))))))))))))))))))))))))))) THEN
  (SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ p2c_regular_view (rfs_view hs) /\
                rfs_pinched (rfs_view hs)`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                     (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x /\
                &0 < inv(sqrt(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)) /\
                &0 < inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) /\
                &0 < inv(&2 * C * sqrt(D + &2))`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_SIMP_TAC[SQRT_POS_LT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)) =
                inv(&2 * C * sqrt(D + &2)) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))`
   (LABEL_TAC "RRF") THENL
   [REWRITE_TAC[SQRT_MUL; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 <= &2 * Kc + &12 + &2 * exp(&4)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&4` REAL_EXP_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!s y. ts - (Tb - eta / &2) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) < s /\
          s <= ts /\
          y IN rfs_vball (rfs_view hs) ts x (A3 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
          ==> p3_vrm (rfs_view hs) s y <=
              ((&2 * Kc + &12 + &2 * exp(&4)) * rfs_vscalar (rfs_view hs) ts x)`
   (LABEL_TAC "VRM") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at hs s)` ASSUME_TAC THENL
     [USE_THEN "PW3" (MP_TAC o SPEC `s:real` o REWRITE_RULE[P2AH_PERSISTS]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `u:A->bool` P3H_RM_FROM_R) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3H_TOPSPACE_TIME_POS THEN
      MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `y:A`] THEN ASM_REWRITE_TAC[];
      USE_THEN "KC3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!z:A. z IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
          ==> rfs_vball (rfs_view hs) (ts - (Tb - eta) * inv(rfs_vscalar (rfs_view hs) ts x)) z
                (inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view hs) ts x)))
              SUBSET rfs_vball (rfs_view hs) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`
   (LABEL_TAC "SBW") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`;
                   `rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A3 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`;
                   `ts - (Tb - eta / &2) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`;
                   `ts:real`;
                   `(&2 * Kc + &12 + &2 * exp(&4)) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x`;
                   `ts - (Tb - eta) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`;
                   `x:A`; `z:A`;
                   `A2 * inv(sqrt(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x))`;
                   `A * inv(sqrt(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x))`;
                   `inv(&2 * C * sqrt((D + &2) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x))`]
                  P2BU_VIEW_BALL_IN) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `b * q < a * q ==> t - a * q < t - b * q`) THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < b * q ==> t - b * q < t`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      REWRITE_TAC[P2AH_VIEW_PARTS] THEN MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3H_CLOSURE_VBALL_SUB THEN ASM_REWRITE_TAC[P2AH_VIEW_PARTS] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `&2 * ((&2 * Kc + &12 + &2 * exp(&4)) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) *
        (ts - (ts - (Tb - eta) * inv(rfs_vscalar (rfs_view hs) ts x))) =
        &2 * (&2 * Kc + &12 + &2 * exp(&4)) * (Tb - eta)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `!q k t b e. ~(q = &0) ==> &2 * (k * q) * (t - (t - (b - e) * inv q)) = &2 * k * (b - e)`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `e1 * (c * q) <= e2 * (c * q) ==> e1 * c * q <= (a + e2 * c) * q - a * q`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= k * e ==> &2 * k * (t - e) <= &2 * k * t`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `inv(&16 * C * (D + &2) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) =
                inv(&16 * C * (D + &2)) * inv(rfs_vscalar (rfs_view hs) ts x) /\
                &0 < inv(&16 * C * (D + &2)) /\ inv(&16 * C * (D + &2)) <= &1`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &16 * C * (D + &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&2 * &2 <= c * d ==> &1 <= &16 * c * d`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (USE_THEN "EX" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:real`;
     `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
     `ts:real`; `x:A`;
     `ts - (Tb - eta) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`; `D:real`;
     `ts - (Tb - eta / &2) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`;
     `rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`;
     `rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`;
     `Kc:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `b * q < a * q ==> t - a * q < t - b * q`) THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= b * q ==> t - b * q <= t`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
      REWRITE_TAC[GEN_ALL(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)))] THEN
      MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[P2AH_VIEW_PARTS]; STRIP_TAC] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN REWRITE_TAC[P2AH_VIEW_PARTS] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "KC3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
        can (find_term (fun t -> t = `y:A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_vball")) (concl th))) THEN
      REWRITE_TAC[GEN_ALL(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)))] THEN
      MATCH_MP_TAC(SET_RULE `!s t (y:A). s SUBSET t ==> y IN s ==> y IN t`) THEN
      MATCH_MP_TAC P2BC_BALL_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`y:A`; `k:num`; `j:num`] THEN
      STRIP_TAC THEN
      USE_THEN "N17" (MP_TAC o SPECL [`y:A`; `k:num`; `j:num`] o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `ts - (Tb - eta) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) -
                  inv(&16 * C * (D + &2)) * inv(rfs_vscalar (rfs_view hs) ts x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `(b - e + w) * q <= (b + &1) * q ==> t - (b + &1) * q <= t - (b - e) * q - w * q`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PE") (LABEL_TAC "RE")) THEN
  SUBGOAL_THEN `ts - (Tb - eta) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) -
                inv(&16 * C * (D + &2)) * inv(rfs_vscalar (rfs_view hs) ts x) <=
                ts - (Tb + inv(&16 * C * (D + &2)) / &2) * inv(rfs_vscalar (rfs_view hs) ts x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(b + w / &2) * q <= (b - e + w) * q ==> t - (b - e) * q - w * q <= t - (b + w / &2) * q`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`ts - (Tb - eta) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) -
       inv(&16 * C * (D + &2)) * inv(rfs_vscalar (rfs_view hs) ts x)`; `ts:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN USE_THEN "RE" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]));;

(* The time condition of EXT_B_AT for Q large. *)

let P3H_171_TIMECOND = prove
 (`!C D Tb eta T0 ts Q.
     &0 < C /\ &0 <= D /\ &0 < eta /\ &0 < T0 /\ T0 <= ts /\ &0 < Q /\
     (inv(&16 * C * (D + &2)) + Tb) / T0 < Q
     ==> inv(&16 * C * (D + &2) * Q) < ts - (Tb - eta) * inv Q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(&16 * C * (D + &2) * Q) = inv(&16 * C * (D + &2)) * inv Q` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(inv(&16 * C * (D + &2)) + Tb) * inv Q < T0` MP_TAC THENL
   [REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `(inv(&16 * C * (D + &2)) + Tb) / T0 < Q` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eta * inv Q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Step B for the sequence: given back(Tc) for all Tc < Tb, the region     *)
(* bound R <= Kc(Tc) Q on every A-ball over (ts - Tc/Q, ts] (Kc uniform in A,*)
(* the local-in-time clause of 11.8 transferred) and the bound R <= D(A) Q  *)
(* at each single time ts - Tc/Q, Tc < Tb (D uniform in Tc: the Cor 11.16   *)
(* clause transferred), every A-ball persists past Tb, with R <= K(A) Q     *)
(* there.                                                                   *)

let P3H_171_EXT_B = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa Tb.
              eps <= eps0 /\ &0 < Tb /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
              (!Tc. Tc < Tb ==> p3_blowup_back (kappa,eps) hs x ts Tc) /\
              (!Tc. &0 <= Tc /\ Tc < Tb
                    ==> ?Kc. &0 <= Kc /\
                             !A. &0 < A
                                 ==> ?N. !n s z. N <= n /\
                                           ts n - Tc * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                           s <= ts n /\
                                           z IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                                  (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                           ==> rfs_vscalar (rfs_view (hs n)) s z <=
                                               Kc * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
              (!A. &0 < A
                   ==> ?D. &0 <= D /\
                           !Tc. &0 <= Tc /\ Tc < Tb
                                ==> ?N. !n z. N <= n /\
                                          z IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                          ==> rfs_vscalar (rfs_view (hs n))
                                                (ts n - Tc * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))) z <=
                                              D * rfs_vscalar (rfs_view (hs n)) (ts n) (x n))
              ==> !A. &0 < A
                      ==> ?dl K N. &0 < dl /\ &0 <= K /\
                            !n. N <= n
                                ==> rfs_persists (rfs_view (hs n))
                                      (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                         (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                      (ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                      (ts n) /\
                                    !s y. ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                          s <= ts n /\
                                          y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                          ==> rfs_vscalar (rfs_view (hs n)) s y <=
                                              K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)`,
  (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_EXT_B_AT) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EB"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (CONJUNCTS_THEN2 (LABEL_TAC "BK")
    (CONJUNCTS_THEN2 (LABEL_TAC "RBL") (LABEL_TAC "RB0")))))) THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "CEX" (STRIP_ASSUME_TAC o REWRITE_RULE[p3h_cexseq])) THEN
  (SUBGOAL_THEN `&2 <= C /\ &0 < eps` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst] THEN SIMP_TAC[];
    ALL_TAC]) THEN
  (USE_THEN "RB0" (fun th -> X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RBD"))
    (MP (SPEC `A:real` th) (ASSUME `&0 < A`)))) THEN
  (SUBGOAL_THEN `?eta. &0 < eta /\ eta < Tb /\ eta <= inv(&16 * C * (D + &2)) / &2`
   (X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min (Tb / &2) (inv(&16 * C * (D + &2)) / &2)` THEN
    SUBGOAL_THEN `&0 < inv(&16 * C * (D + &2))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (USE_THEN "RBL" (MP_TAC o SPEC `Tb - eta / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RKC")))) THEN
  (ABBREV_TAC `A2 = A + exp(&2 * (&2 * Kc + &12 + &2 * exp(&4)) * Tb) * inv(&2 * C * sqrt(D + &2))` THEN
  ABBREV_TAC `A3 = A2 + &1`) THEN
  (SUBGOAL_THEN `&0 < A2 /\ &0 < A3` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= exp(&2 * (&2 * Kc + &12 + &2 * exp(&4)) * Tb) * inv(&2 * C * sqrt(D + &2))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC]];
      EXPAND_TAC "A3" THEN EXPAND_TAC "A2" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (USE_THEN "RKC" (fun th -> X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")
    (MP (SPEC `A3:real` th) (ASSUME `&0 < A3`))) THEN
  USE_THEN "RBD" (MP_TAC o SPEC `Tb - eta`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2"))) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`A2:real`; `max (&2 * (D + &2)) Kc`; `Tb + &1`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Dp:real`)) (concl th))) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MAX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3"))) THEN
  (USE_THEN "BK" (MP_TAC o REWRITE_RULE[p3_blowup_back] o SPEC `Tb - eta / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_THEN(LABEL_TAC "BKC") THEN
  USE_THEN "BKC" (X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4") o SPEC `A:real`) THEN
  USE_THEN "BKC" (X_CHOOSE_THEN `N5:num` (LABEL_TAC "N5") o SPEC `A2:real`) THEN
  USE_THEN "BKC" (X_CHOOSE_THEN `N6:num` (LABEL_TAC "N6") o SPEC `A3:real`)) THEN
  (FIRST_X_ASSUM(MP_TAC o SPEC `max (&1) ((inv(&16 * C * (D + &2)) + Tb) / p3_T i)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `B:real`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N7:num` (LABEL_TAC "N7"))) THEN
  (MAP_EVERY EXISTS_TAC [`inv(&16 * C * (D + &2)) / &2`; `max (&2 * (D + &2)) Kc`;
                        `N1 + N2 + N3 + N4 + N5 + N6 + N7:num`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LE_MAX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC) THEN
  (USE_THEN "N7" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MAX_LT] THEN STRIP_TAC) THEN
  (FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
  REWRITE_TAC[p3h_inst] THEN STRIP_TAC) THEN
  (USE_THEN "EB" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
     `(dlt:num->real) n`; `(rs':num->num->real) n`; `(ks':num->num->real) n`;
     `(dd:num->num->real) n`; `(hs:num->(A)rfs_history) n`; `(r:num->real) n`;
     `(ts:num->real) n`; `(x:num->A) n`; `Tb:real`; `eta:real`; `D:real`; `Kc:real`;
     `A:real`; `A2:real`; `A3:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC P3H_171_TIMECOND THEN EXISTS_TAC `p3_T i` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
      USE_THEN "N4" (fun th -> MP_TAC(SPEC `n:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "N5" (fun th -> MP_TAC(SPEC `n:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "N6" (fun th -> MP_TAC(SPEC `n:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      USE_THEN "N3" (fun th -> MP_TAC(SPEC `n:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    SIMP_TAC[]]));;

(* Step D for one counterexample: with R <= DU Q on the tt-balls (Claim      *)
(* 17.10 at -Tb, PIECE U) and the forward ball inclusion (RFA_171_BALL_FWD),*)
(* the A-ball persists past Tb by 1/(16 C (DU+2)), independent of A.         *)

let P3H_171_EXT_D_AT = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x
            Tb dm DU KA KA2 A A2.
              &2 <= C /\ &0 < eps /\ eps <= eps0 /\ rs' (SUC i) = r' /\ &0 < r' /\
              p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
              p3_T i <= ts /\ ts < rfs_horizon hs /\
              rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
              inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
              (!y. y IN topspace(rfs_top_at hs ts) /\
                   &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                   ==> p3_canon_at (rfs_view hs) C eps y ts) /\
              x IN topspace(rfs_top_at hs ts) /\ &1 <= rfs_vscalar (rfs_view hs) ts x /\
              &0 < A /\ &0 < DU /\ &0 <= KA /\ &0 <= KA2 /\ &0 < dm /\ &0 < Tb /\
              A2 = A + &2 * inv(&2 * C * sqrt(DU + &2)) + &1 /\
              inv(&16 * C * (DU + &2) * rfs_vscalar (rfs_view hs) ts x) <
              ts - Tb * inv(rfs_vscalar (rfs_view hs) ts x) /\
              rfs_persists (rfs_view hs)
                (rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                (ts - (Tb + dm) * inv(rfs_vscalar (rfs_view hs) ts x)) ts /\
              (!s y. ts - (Tb + dm) * inv(rfs_vscalar (rfs_view hs) ts x) < s /\ s <= ts /\
                     y IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                     ==> rfs_vscalar (rfs_view hs) s y <= KA * rfs_vscalar (rfs_view hs) ts x) /\
              rfs_persists (rfs_view hs)
                (rfs_vball (rfs_view hs) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                (ts - (Tb + dm) * inv(rfs_vscalar (rfs_view hs) ts x)) ts /\
              (!s y. ts - (Tb + dm) * inv(rfs_vscalar (rfs_view hs) ts x) < s /\ s <= ts /\
                     y IN rfs_vball (rfs_view hs) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                     ==> rfs_vscalar (rfs_view hs) s y <= KA2 * rfs_vscalar (rfs_view hs) ts x) /\
              (!y. y IN rfs_vball (rfs_view hs) (ts - Tb * inv(rfs_vscalar (rfs_view hs) ts x)) x
                          (exp(&2 * (&2 * KA + &12 + &2 * exp(&4)) * Tb) * A *
                           inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                   ==> rfs_vscalar (rfs_view hs) (ts - Tb * inv(rfs_vscalar (rfs_view hs) ts x)) y <=
                       DU * rfs_vscalar (rfs_view hs) ts x) /\
              (!z. z IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                   ==> rfs_vball (rfs_view hs) (ts - Tb * inv(rfs_vscalar (rfs_view hs) ts x)) z
                         (inv(&2 * C * sqrt(DU + &2)) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                       SUBSET rfs_vball (rfs_view hs) ts z
                         (&2 * inv(&2 * C * sqrt(DU + &2)) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))) /\
              ~(?y k j. y IN rfs_vball (rfs_view hs) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                        1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                        ts - (Tb + &1) * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\
                        hs_time hs k < ts /\
                        y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                        p3_flowline hs y (hs_time hs k) ts /\
                        (!s. hs_time hs k <= s /\ s <= ts
                             ==> rfs_vscalar (rfs_view hs) s y <=
                                 max (&2 * (DU + &2)) KA2 * rfs_vscalar (rfs_view hs) ts x))
              ==> rfs_persists (rfs_view hs)
                    (rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))))
                    (ts - (Tb + inv(&16 * C * (DU + &2))) * inv(rfs_vscalar (rfs_view hs) ts x)) ts /\
                  (!s y. ts - (Tb + inv(&16 * C * (DU + &2))) * inv(rfs_vscalar (rfs_view hs) ts x) < s /\
                         s <= ts /\
                         y IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                         ==> rfs_vscalar (rfs_view hs) s y <=
                             max (&2 * (DU + &2)) KA2 * rfs_vscalar (rfs_view hs) ts x)`,
  (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_EXT_AT) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EX"))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "WORST") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PWA") (CONJUNCTS_THEN2 (LABEL_TAC "RA") (CONJUNCTS_THEN2 (LABEL_TAC "PWA2") (CONJUNCTS_THEN2 (LABEL_TAC "RA2") (CONJUNCTS_THEN2 (LABEL_TAC "UTB") (CONJUNCTS_THEN2 (LABEL_TAC "FWD") (LABEL_TAC "N17"))))))))))))))))))))))))))))) THEN
  (SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ p2c_regular_view (rfs_view hs) /\
                rfs_pinched (rfs_view hs)`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                     (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x /\
                &0 < inv(sqrt(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)) /\
                &0 < inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) /\
                &0 < inv(&2 * C * sqrt(DU + &2)) /\
                &0 < inv(&16 * C * (DU + &2)) /\ inv(&16 * C * (DU + &2)) <= &1 /\
                inv(&16 * C * (DU + &2) * rfs_vscalar (rfs_view hs) ts x) =
                inv(&16 * C * (DU + &2)) * inv(rfs_vscalar (rfs_view hs) ts x) /\
                inv(&2 * C * sqrt((DU + &2) * rfs_vscalar (rfs_view hs) ts x)) =
                inv(&2 * C * sqrt(DU + &2)) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)) /\
                &0 <= &2 * KA + &12 + &2 * exp(&4)`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &16 * C * (DU + &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&2 * &2 <= c * d ==> &1 <= &16 * c * d`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[SQRT_POS_LT];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SQRT_MUL; REAL_INV_MUL] THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `&4` REAL_EXP_POS_LE) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!s y. ts - (Tb + dm) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) < s /\ s <= ts /\
          y IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
          ==> p3_vrm (rfs_view hs) s y <=
              ((&2 * KA + &12 + &2 * exp(&4)) * rfs_vscalar (rfs_view hs) ts x)`
   (LABEL_TAC "VRM") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at hs s)` ASSUME_TAC THENL
     [USE_THEN "PWA" (MP_TAC o SPEC `s:real` o REWRITE_RULE[P2AH_PERSISTS]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `u:A->bool` P3H_RM_FROM_R) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3H_TOPSPACE_TIME_POS THEN
      MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `y:A`] THEN ASM_REWRITE_TAC[];
      USE_THEN "RA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
    SUBSET rfs_vball (rfs_view hs) (ts - Tb * inv(rfs_vscalar (rfs_view hs) ts x)) x
             (exp(&2 * (&2 * KA + &12 + &2 * exp(&4)) * Tb) * A *
              inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`
   (LABEL_TAC "OUT") THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`;
                   `rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`;
                   `ts - (Tb + dm) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`; `ts:real`;
                   `(&2 * KA + &12 + &2 * exp(&4)) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x`;
                   `ts - Tb * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`; `x:A`;
                   `A * inv(sqrt(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x))`]
                  P2BU_VIEW_BALL_OUT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC(REAL_ARITH `b * q < a * q ==> t - a * q < t - b * q`) THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 < b * q ==> t - b * q < t`) THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GEN_ALL(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)))] THEN
        MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[P2AH_VIEW_PARTS]; STRIP_TAC] THEN
        ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN REWRITE_TAC[P2AH_VIEW_PARTS] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN
       `&2 * ((&2 * KA + &12 + &2 * exp(&4)) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) *
        (ts - (ts - Tb * inv(rfs_vscalar (rfs_view hs) ts x))) =
        &2 * (&2 * KA + &12 + &2 * exp(&4)) * Tb`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `!q k t b. ~(q = &0) ==> &2 * (k * q) * (t - (t - b * inv q)) = &2 * k * b`) THEN
        ASM_REAL_ARITH_TAC;
        SIMP_TAC[]]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!z:A. z IN rfs_vball (rfs_view hs) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
          ==> rfs_vball (rfs_view hs) (ts - Tb * inv(rfs_vscalar (rfs_view hs) ts x)) z
                (inv(&2 * C * sqrt((DU + &2) * rfs_vscalar (rfs_view hs) ts x)))
              SUBSET rfs_vball (rfs_view hs) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`
   (LABEL_TAC "SBW") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `inv(&2 * C * sqrt((DU + &2) * rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x))`
       then REWRITE_TAC[th] else NO_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) ts z
                  (&2 * inv(&2 * C * sqrt(DU + &2)) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))` THEN
    CONJ_TAC THENL
     [USE_THEN "FWD" (fun th -> ACCEPT_TAC(MP (SPEC `z:A` th)
        (ASSUME `(z:A) IN rfs_vball (rfs_view (hs:(A)rfs_history)) ts x
                     (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`)));
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[P2AH_VIEW_PARTS]; STRIP_TAC] THEN
    UNDISCH_TAC `(z:A) IN rfs_vball (rfs_view (hs:(A)rfs_history)) ts x
                   (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))` THEN
    REWRITE_TAC[GEN_ALL(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)))] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_vtop (rfs_view (hs:(A)rfs_history)) ts,rfs_vatlas (rfs_view hs) ts)
                  (rfs_vmetric (rfs_view hs) ts) x
                  (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)) +
                   &2 * inv(&2 * C * sqrt(DU + &2)) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AP_BALL_SHIFT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BC_BALL_MONO THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < inv(sqrt(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x))` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (USE_THEN "EX" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:real`;
     `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `r':real`;
     `ts:real`; `x:A`;
     `ts - Tb * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`; `DU:real`;
     `ts - (Tb + dm) * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)`;
     `rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`;
     `rfs_vball (rfs_view (hs:(A)rfs_history)) ts x (A2 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))`;
     `KA2:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `b * q < a * q ==> t - a * q < t - b * q`) THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= b * q ==> t - b * q <= t`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
      REWRITE_TAC[GEN_ALL(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)))] THEN
      MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `ts:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[P2AH_VIEW_PARTS]; STRIP_TAC] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN REWRITE_TAC[P2AH_VIEW_PARTS] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "UTB" MATCH_MP_TAC THEN
      USE_THEN "OUT" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`y:A`; `k:num`; `j:num`] THEN
      STRIP_TAC THEN
      USE_THEN "N17" (MP_TAC o SPECL [`y:A`; `k:num`; `j:num`] o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `ts - Tb * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) -
                  inv(&16 * C * (DU + &2)) * inv(rfs_vscalar (rfs_view hs) ts x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `(b + w) * q <= (b + &1) * q ==> t - (b + &1) * q <= t - b * q - w * q`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a <=> c) /\ (b <=> d) ==> a /\ b ==> c /\ d`) THEN
  SUBGOAL_THEN `ts - Tb * inv(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x) -
                inv(&16 * C * (DU + &2)) * inv(rfs_vscalar (rfs_view hs) ts x) =
                ts - (Tb + inv(&16 * C * (DU + &2))) * inv(rfs_vscalar (rfs_view hs) ts x)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[]]));;

(* Step D for the sequence: one window 1/(16 C (DU+2)) past Tb for all A,  *)
(* from Step B, the uniform bound at -Tb (PIECE U) and RFA_171_BALL_FWD.    *)

let P3H_171_EXT_D = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x Tb.
              eps <= eps0 /\ &0 < Tb /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
              (!A. &0 < A
                   ==> ?dl K N. &0 < dl /\ &0 <= K /\
                         !n. N <= n
                             ==> rfs_persists (rfs_view (hs n))
                                   (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                      (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                   (ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                   (ts n) /\
                                 !s y. ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                       s <= ts n /\
                                       y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                              (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                       ==> rfs_vscalar (rfs_view (hs n)) s y <=
                                           K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
              (?D. &0 < D /\
                   !A. &0 < A
                       ==> ?N. !n y. N <= n /\
                                 y IN rfs_vball (rfs_view (hs n))
                                        (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))) (x n)
                                        (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                 ==> rfs_vscalar (rfs_view (hs n))
                                       (ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))) y <=
                                     D * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
              (!A rho. &0 < A /\ &0 < rho
                       ==> ?N. !n z s. N <= n /\
                                 ts n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) <= s /\
                                 s <= ts n /\
                                 z IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                        (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                 ==> rfs_vball (rfs_view (hs n)) s z
                                       (rho * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                     SUBSET
                                     rfs_vball (rfs_view (hs n)) (ts n) z
                                       (&2 * rho * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
              ==> ?dl. &0 < dl /\
                       !A. &0 < A
                           ==> ?K N. &0 <= K /\
                                 !n. N <= n
                                     ==> rfs_persists (rfs_view (hs n))
                                           (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                              (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                                           (ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                                           (ts n) /\
                                         !s y. ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                               s <= ts n /\
                                               y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                                      (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                               ==> rfs_vscalar (rfs_view (hs n)) s y <=
                                                   K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)`,
  (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_EXT_D_AT) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ED"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (CONJUNCTS_THEN2 (LABEL_TAC "EXTB")
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `DU:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UTB")))
    (LABEL_TAC "FWD")))))) THEN
  USE_THEN "CEX" (STRIP_ASSUME_TAC o REWRITE_RULE[p3h_cexseq])) THEN
  (SUBGOAL_THEN `&2 <= C /\ &0 < eps` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
    REWRITE_TAC[p3h_inst] THEN SIMP_TAC[];
    ALL_TAC]) THEN
  (EXISTS_TAC `inv(&16 * C * (DU + &2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC) THEN
  (ABBREV_TAC `A2 = A + &2 * inv(&2 * C * sqrt(DU + &2)) + &1` THEN
  SUBGOAL_THEN `&0 < inv(&2 * C * sqrt(DU + &2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A2` ASSUME_TAC THENL [EXPAND_TAC "A2" THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (USE_THEN "EXTB" (fun th -> X_CHOOSE_THEN `dlA:real` (X_CHOOSE_THEN `KA:real`
    (X_CHOOSE_THEN `NA:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BA")))))
    (MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
  USE_THEN "EXTB" (fun th -> X_CHOOSE_THEN `dlA2:real` (X_CHOOSE_THEN `KA2:real`
    (X_CHOOSE_THEN `NA2:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BA2")))))
    (MP (SPEC `A2:real` th) (ASSUME `&0 < A2`)))) THEN
  (SUBGOAL_THEN `?dm. &0 < dm /\ dm <= dlA /\ dm <= dlA2` (X_CHOOSE_THEN `dm:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min dlA dlA2` THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (USE_THEN "UTB" (MP_TAC o SPEC `exp(&2 * (&2 * KA + &12 + &2 * exp(&4)) * Tb) * A`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `NU:num` (LABEL_TAC "NU")) THEN
  USE_THEN "FWD" (fun th -> MP_TAC(MP (SPECL [`A:real`; `inv(&2 * C * sqrt(DU + &2))`] th)
    (CONJ (ASSUME `&0 < A`) (ASSUME `&0 < inv(&2 * C * sqrt(DU + &2))`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `NF:num` (LABEL_TAC "NF"))) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`A2:real`; `max (&2 * (DU + &2)) KA2`; `Tb + &1`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Dp:real`)) (concl th))) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MAX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3"))) THEN
  (FIRST_X_ASSUM(MP_TAC o SPEC `max (&1) ((inv(&16 * C * (DU + &2)) + (Tb + &1)) / p3_T i)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `B:real`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N7:num` (LABEL_TAC "N7"))) THEN
  (MAP_EVERY EXISTS_TAC [`max (&2 * (DU + &2)) KA2`; `NA + NA2 + NU + NF + N3 + N7:num`] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LE_MAX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "N7" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MAX_LT] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
  REWRITE_TAC[p3h_inst] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `&0 < inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) ((ts:num->real) n) ((x:num->A) n)) /\
                ts n - (Tb + dlA) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) <=
                ts n - (Tb + dm) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
                ts n - (Tb + dlA2) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) <=
                ts n - (Tb + dm) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n))`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `b * q <= a * q ==> t - a * q <= t - b * q`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (USE_THEN "ED" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
     `(dlt:num->real) n`; `(rs':num->num->real) n`; `(ks':num->num->real) n`;
     `(dd:num->num->real) n`; `(hs:num->(A)rfs_history) n`; `(r:num->real) n`;
     `(ts:num->real) n`; `(x:num->A) n`; `Tb:real`; `dm:real`; `DU:real`; `KA:real`;
     `KA2:real`; `A:real`; `A2:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MP_TAC(ISPECL [`C:real`; `DU:real`; `Tb + &1`; `&1`; `p3_T i`; `(ts:num->real) n`;
                     `rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n)`]
                    P3H_171_TIMECOND) THEN
      REWRITE_TAC[REAL_ARITH `(Tb + &1) - &1 = Tb`] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
      USE_THEN "BA" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
      MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(ts:num->real) n - (Tb + dlA) * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n))`; `(ts:num->real) n`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REPEAT STRIP_TAC THEN USE_THEN "BA" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "BA2" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
      MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(ts:num->real) n - (Tb + dlA2) * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) (x n))`; `(ts:num->real) n`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REPEAT STRIP_TAC THEN USE_THEN "BA2" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "NU" MATCH_MP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "NF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      CONJ_TAC THENL
       [ASM_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= b * q ==> t - b * q <= t`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      USE_THEN "N3" (fun th -> MP_TAC(SPEC `n:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    SIMP_TAC[]]));;

(* ========================================================================= *)
(* Prop 17.1, the maximal backward time T' = infinity along a subsequence:  *)
(* the backward hypothesis p3_blowup_back as a property of subsequences     *)
(* (monotone in Tb, a tail property, true at 0) and P3H_SUBSEQ_SUP.        *)
(* ========================================================================= *)

let P3H_BACK_MONO = prove
 (`!kappa r0 (hs:num->(A)rfs_history) x t Tb Tc.
     (!n. &0 < rfs_vscalar (rfs_view (hs n)) (t n) (x n)) /\
     p3_blowup_back (kappa,r0) hs x t Tb /\ Tc <= Tb
     ==> p3_blowup_back (kappa,r0) hs x t Tc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_blowup_back] THEN STRIP_TAC THEN
  X_GEN_TAC `A:real` THEN FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:num->real) n - Tb * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (t n) ((x:num->A) n)) <=
                t n - Tc * inv(rfs_vscalar (rfs_view (hs n)) (t n) (x n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `b * q <= a * q ==> t - a * q <= t - b * q`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) n - Tb * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (t n) ((x:num->A) n))`; `(t:num->real) n`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let P3H_BACK_ZERO = prove
 (`!kappa r0 (hs:num->(A)rfs_history) x t. p3_blowup_back (kappa,r0) hs x t (&0)`,
  REWRITE_TAC[p3_blowup_back; REAL_MUL_LZERO; REAL_SUB_RZERO; P2AH_PERSISTS] THEN
  REPEAT GEN_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3H_BACK_SEL = prove
 (`!kappa r0 (hs:num->(A)rfs_history) x t Tb s1 s2 N.
     p3_blowup_back (kappa,r0) (hs o s1) (x o s1) (t o s1) Tb /\
     (!j. N <= j ==> ?j'. j <= j' /\ s2 j = s1 j')
     ==> p3_blowup_back (kappa,r0) (hs o s2) (x o s2) (t o s2) Tb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_blowup_back; o_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `A:real` THEN FIRST_X_ASSUM(X_CHOOSE_TAC `N1:num` o SPEC `A:real`) THEN
  EXISTS_TAC `N + N1:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* T' = infinity along one subsequence, from the extension property (START *)
(* at Tb = 0, the finite-T' extension at Tb > 0).                          *)

let P3H_171_TINF = prove
 (`!kappa r0 (hs:num->(A)rfs_history) x t.
     (!n. &0 < rfs_vscalar (rfs_view (hs n)) (t n) (x n)) /\
     (!s Tb. p3_subseq s /\ &0 <= Tb /\
             (!Tc. Tc < Tb ==> p3_blowup_back (kappa,r0) (hs o s) (x o s) (t o s) Tc)
             ==> ?k d. p3_subseq k /\ &0 < d /\
                       p3_blowup_back (kappa,r0) (hs o (s o k)) (x o (s o k)) (t o (s o k))
                         (Tb + d))
     ==> ?s. p3_subseq s /\ !Tb. p3_blowup_back (kappa,r0) (hs o s) (x o s) (t o s) Tb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\(s:num->num) Tb. p3_blowup_back (kappa,r0) ((hs:num->(A)rfs_history) o s)
                                    ((x:num->A) o s) ((t:num->real) o s) Tb` P3H_SUBSEQ_SUP) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_BACK_MONO THEN EXISTS_TAC `Tb:real` THEN
    ASM_REWRITE_TAC[o_THM];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_BACK_SEL THEN
    MAP_EVERY EXISTS_TAC [`s1:num->num`; `N:num`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[P3H_BACK_ZERO];
    FIRST_ASSUM ACCEPT_TAC]);;

(* T' = infinity gives the contradiction (PIECE INF): along a subsequence   *)
(* the blow-up limit is a kappa-solution (11.8, second part), so by Cor 9.95 *)
(* (canonv) some x n has a (C,eps)-canonv neighbourhood.                     *)

let P3H_171_INFTY = prove
 (`!u:A->bool.
     P2_THM_11_8_STATEMENT u (:real^3) /\ P2_COR_9_95_STATEMENT u (:real^3)
     ==> ?eps0. &0 < eps0 /\
           !eps. &0 < eps /\ eps <= eps0
             ==> ?C0. &1 < C0 /\
                   !C kappa r0 mu (hs:num->(A)rfs_history) x ts.
                      C0 <= C /\
                      p3_blowup_seq (C,eps,kappa,r0,mu) hs x ts /\
                      (!n. p2b_hs_sep (hs n) /\
                           !k. k <= hs_count (hs n)
                               ==> mfd_orientable (hs_top (hs n) k) (hs_atlas (hs n) k)) /\
                      (!Tb. &0 < Tb ==> p3_blowup_back (kappa,r0) hs x ts Tb)
                      ==> ?n. p3_canonv_at (rfs_view (hs n)) C eps (x n) (ts n)`,
  (GEN_TAC THEN REWRITE_TAC[P2_THM_11_8_STATEMENT; P2_COR_9_95_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e8:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T118")))
    (X_CHOOSE_THEN `e95:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C995")))) THEN
  EXISTS_TAC `min e8 e95` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `eps:real` THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  USE_THEN "C995" (fun th -> MP_TAC(MP (SPEC `eps:real` th)
    (CONJ (ASSUME `&0 < eps`) (ASSUME `eps <= e95`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `C95:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C95"))) THEN
  EXISTS_TAC `C95:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BS")
    (CONJUNCTS_THEN2 (LABEL_TAC "SO") (LABEL_TAC "BK"))))) THEN
  (USE_THEN "T118" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
     `hs:num->(A)rfs_history`; `x:num->A`; `ts:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "SO" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[p2b_hs_sep] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN USE_THEN "BK" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:(real^3)topology`
    (X_CHOOSE_THEN `atlas:((real^3->bool)#(real^3->real^3))->bool`
    (X_CHOOSE_THEN `g:real->real^3->real^3^3` (X_CHOOSE_THEN `xl:real^3` STRIP_ASSUME_TAC)))))) THEN
  (USE_THEN "C95" (MP_TAC o SPECL [`C:real`; `(hs:num->(A)rfs_history) o (sub:num->num)`;
     `(x:num->A) o (sub:num->num)`; `(ts:num->real) o (sub:num->num)`;
     `\n. rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) ((sub:num->num) n)))
            ((ts:num->real) (sub n)) ((x:num->A) (sub n))`;
     `top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
     `g:real->real^3->real^3^3`; `xl:real^3`; `kappa:real`]) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "SO" (MP_TAC o SPEC `(sub:num->num) n`) THEN SIMP_TAC[] THEN DISCH_TAC THEN
    USE_THEN "BS" (MP_TAC o REWRITE_RULE[p3_blowup_seq]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `(sub:num->num) N` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL]));;

(* ========================================================================= *)
(* Prop 17.1, the finite-T' extension step: Step B's hypotheses from the  *)
(* 11.8 flow limit (E1; the transfers of pc_p2c_bugq) and the assembly of  *)
(* the extension (E2).                                                     *)
(* ========================================================================= *)

let P3H_171_RB_FROM_LIMIT = prove
 (`!(hs:num->(A)rfs_history) ts x Tb (top:(real^3)topology) atlas g xl.
     (!n. p2c_regular_view (rfs_view (hs n))) /\ &0 < Tb /\
     p3_flow_limit (\n. rfs_view (hs n)) x ts
       (\n. rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) (top,atlas) g xl Tb /\
     mfd_complete (top,atlas) (g (&0)) /\
     (!a. --Tb < a
          ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                        ==> mfd_rm_norm atlas (g s) y <= K) /\
     (!A. ?K. !s y. --Tb < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                    ==> mfd_rm_norm atlas (g s) y <= K)
     ==> (!Tc. &0 <= Tc /\ Tc < Tb
               ==> ?Kc. &0 <= Kc /\
                        !A. &0 < A
                            ==> ?N. !n s z. N <= n /\
                                      ts n - Tc * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                                      s <= ts n /\
                                      z IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                             (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                      ==> rfs_vscalar (rfs_view (hs n)) s z <=
                                          Kc * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /\
         (!A. &0 < A
              ==> ?D. &0 <= D /\
                      !Tc. &0 <= Tc /\ Tc < Tb
                           ==> ?N. !n z. N <= n /\
                                     z IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                            (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                                     ==> rfs_vscalar (rfs_view (hs n))
                                           (ts n - Tc * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))) z <=
                                         D * rfs_vscalar (rfs_view (hs n)) (ts n) (x n))`,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RV") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "FL") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "LT") (LABEL_TAC "B79"))))))) THEN
  (SUBGOAL_THEN `smooth_manifold_atlas (top:(real^3)topology) atlas /\
                (!n. &0 < rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) ((ts:num->real) n) ((x:num->A) n)) /\
                (!a. --Tb < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)`
   STRIP_ASSUME_TAC THENL
   [USE_THEN "FL" (MP_TAC o REWRITE_RULE[p3_flow_limit]) THEN BETA_TAC THEN SIMP_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!s. --Tb < s /\ s <= &0 ==> riemannian_metric atlas ((g:real->real^3->real^3^3) s)`
   (LABEL_TAC "RM") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                   `(s - Tb) / &2`; `&0`; `g:real->real^3->real^3^3`; `s:real`] P2AP_UPTO_RIEM) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC]) THEN
  (USE_THEN "FL" (MP_TAC o MATCH_MP P2HN_FLOW_LIMIT_ON) THEN REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->real^3->bool` (X_CHOOSE_THEN `phi:num->real^3->A`
    (LABEL_TAC "FW")))) THEN
  (MP_TAC(INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_SCALAR_FROM_RMNORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cs:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CS")))) THEN
  (SUBGOAL_THEN
   `!c s:real n. --c <= &0 /\
                 (ts:num->real) n - c * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) ((x:num->A) n)) < s /\
                 s <= ts n
                 ==> --c <= (s - ts n) * rfs_vscalar (rfs_view (hs n)) (ts n) (x n) /\
                     (s - ts n) * rfs_vscalar (rfs_view (hs n)) (ts n) (x n) <= &0 /\
                     ts n + ((s - ts n) * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) /
                            rfs_vscalar (rfs_view (hs n)) (ts n) (x n) = s`
   (LABEL_TAC "CONV") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) ((ts:num->real) n) ((x:num->A) n)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < (s - ((ts:num->real) n - c * inv(rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) ((x:num->A) n)))) *
                       rfs_vscalar (rfs_view (hs n)) (ts n) (x n)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(s - (ts:num->real) n) * rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) ((x:num->A) n) =
                    (s - (ts n - c * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))) *
                    rfs_vscalar (rfs_view (hs n)) (ts n) (x n) - c` SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `!q s t c. ~(q = &0) ==> (s - t) * q = (s - (t - c * inv q)) * q - c`) THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 <= (t - s) * q ==> (s - t) * q <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_FIELD `!q s t. ~(q = &0) ==> t + ((s - t) * q) / q = s`) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!Kr Kl a b A.
      &0 <= Kr /\ --Tb < a /\ a <= b /\ b <= &0 /\ &0 < A /\
      (!s y. a <= s /\ s <= b /\ y IN topspace top ==> mfd_rm_norm atlas ((g:real->real^3->real^3^3) s) y <= Kr) /\
      (!s y. a <= s /\ s <= b /\ y IN mfd_ball (top,atlas) (g (&0)) xl (A + &1)
             ==> mfd_rm_norm atlas (g s) y <= Kl) /\ &0 <= Kl
      ==> ?N. !n s z. N <= n /\ a <= s /\ s <= b /\
                z IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) n)) ((ts:num->real) n) ((x:num->A) n)
                       (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                ==> rfs_vscalar (rfs_view (hs n)) (ts n + s / rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) z <=
                    (Cs * Kl + &1) * rfs_vscalar (rfs_view (hs n)) (ts n) (x n)`
   (LABEL_TAC "SOI") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `ts:num->real`;
                   `{s:real | --Tb < s /\ s <= &0}`; `top:(real^3)topology`;
                   `atlas:((real^3->bool)#(real^3->real^3))->bool`; `g:real->real^3->real^3^3`;
                   `xl:real^3`; `W:num->real^3->bool`; `phi:num->real^3->A`; `a:real`; `b:real`;
                   `A:real`; `Cs * Kl`; `Kr:real`] P2BU_SCALAR_ON_INT) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `abs r <= c ==> r <= c`) THEN USE_THEN "CS" MATCH_MP_TAC THEN
        EXISTS_TAC `top:(real^3)topology` THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          USE_THEN "RM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `(y:real^3) IN mfd_ball (top,atlas) ((g:real->real^3->real^3^3) (&0)) xl (A + &1)` THEN
          REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
          ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`; `z:A`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [X_GEN_TAC `Tc:real` THEN STRIP_TAC THEN
    USE_THEN "LT" (MP_TAC o SPEC `--Tc`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
    EXISTS_TAC `Cs * max (&0) K + &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 <= a + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "SOI" (MP_TAC o SPECL [`max (&0) K`; `max (&0) K`; `--Tc`; `&0`; `A:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN DISJ2_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN DISJ2_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `z:A`] THEN STRIP_TAC THEN
    USE_THEN "CONV" (MP_TAC o SPECL [`Tc:real`; `s:real`; `n:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`;
      `(s - (ts:num->real) n) * rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) n)) (ts n) ((x:num->A) n)`;
      `z:A`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "B79" (X_CHOOSE_THEN `KB:real` (LABEL_TAC "KB") o SPEC `A + &1`) THEN
  EXISTS_TAC `Cs * max (&0) KB + &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 <= a + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `Tc:real` THEN STRIP_TAC THEN
  USE_THEN "LT" (MP_TAC o SPEC `--Tc`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
  USE_THEN "SOI" (MP_TAC o SPECL [`max (&0) K`; `max (&0) KB`; `--Tc`; `--Tc`; `A:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN DISJ2_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN DISJ2_TAC THEN USE_THEN "KB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `--Tc`; `z:A`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; GSYM real_sub]));;

(* ========================================================================= *)
(* Prop 17.1, noncollapsing of one counterexample at all times up to its    *)
(* first bad time ts: Prop 16.1 (p3_noncoll_prop) on                        *)
(* the truncation p3h_trunc hs ts when ts > T_i (the step hypotheses pass   *)
(* by P3H_STEP_HYP_TRUNC, the canonv assumption is the first-bad-time       *)
(* property), the step hypothesis itself when ts = T_i; back to the view of *)
(* hs before ts (P3H_NONCOLL_UNTRUNC), kappa <= kappa(t) on [0,ts] for the *)
(* decreasing step sequence (P3H_NONCOLL_KAPPA_MONO), and at ts itself by   *)
(* closedness (P3H_NONCOLL_CLOSED).                                          *)
(* ========================================================================= *)

(* A copy of P3L_NONCOLL_UNTRUNC (unit pc_p3_s161).                         *)

let P3H_NONCOLL_UNTRUNC = prove
 (`!TM AT G (kp:real->real) r0 tau t x.
     p3_noncoll_all (rfs_trunc (TM:real->A topology,AT,G) tau) kp r0 /\
     &0 <= t /\ t < tau /\ x IN topspace(TM t)
     ==> p3_noncoll_at (TM,AT,G) (kp t) r0 x t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3_noncoll_all; p3_noncoll_at; rfs_trunc; rfs_vtop; rfs_vatlas;
              rfs_vmetric; rfs_parabolic_exists; rfs_persists; rfs_vball] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. s <= t ==> s < tau` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_SIMP_TAC[]);;

(* Noncollapsing is monotone in kappa (P2BU_NONCOLL_AT_MONO, pc_lim_knc_local, *)
(* is the monotonicity in the scale r0).                                      *)

let P3H_NONCOLL_KAPPA_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    kappa kappa' r0 x t.
     p3_noncoll_at V kappa r0 x t /\ kappa' <= kappa
     ==> p3_noncoll_at V kappa' r0 x t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_noncoll_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "NC") ASSUME_TAC) THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  REMOVE_THEN "NC" (MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kappa * r pow 3` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]);;

let P3H_171_NC_HIST = prove
 (`!(u:A->bool) C eps hf md g0 A0 i rs ks ds kappa dfun r' rs' ks' dd (hs:(A)rfs_history) ts.
     P2C_HISTORY_REGULAR_STATEMENT u /\
     p3_noncoll_prop u (C,eps,hf,md,g0,A0) i (rs,ks,ds) kappa dfun /\
     &0 < kappa /\ &0 < r' /\ r' <= rs i /\ rs' (SUC i) = r' /\ ks' (SUC i) = kappa /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dfun r') (rs',ks',dd) hs /\
     p3_T i <= ts /\ ts < rfs_horizon hs /\
     p3_canonv_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs')
     ==> !s y. s <= ts /\ y IN topspace(rfs_top_at hs s)
               ==> p3_noncoll_at (rfs_view hs) kappa eps y s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "REG") (CONJUNCTS_THEN2 (LABEL_TAC "NP")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p3_seq_ok (ks':num->real) /\ rfs_horizon (hs:(A)rfs_history) <= p3_T (SUC i) /\
                rfs_history_ok hs /\
                p3_noncoll_all (rfs_trunc (rfs_view hs) (p3_T i)) (p3_stepf ks') eps`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) ((dfun:real->real) r')
                   (rs',ks',dd) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_step_hyp; p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_noncoll_all (rfs_trunc (rfs_view (hs:(A)rfs_history)) ts) (p3_stepf ks') eps`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `p3_T i < ts` THENL
     [ALL_TAC;
      SUBGOAL_THEN `ts = p3_T i` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 < ts` ASSUME_TAC THENL
     [MP_TAC(SPEC `i:num` P3_T_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_TRUNC_VIEW) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
    REMOVE_THEN "NP" (MP_TAC o SPECL [`r':real`; `rs':num->real`; `ks':num->real`;
                                      `dd:num->real`; `p3h_trunc (hs:(A)rfs_history) ts`] o
                      REWRITE_RULE[p3_noncoll_prop]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC P3H_STEP_HYP_TRUNC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= ts ==> kappa <= p3_stepf (ks':num->real) s` (LABEL_TAC "KM") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`i:num`; `ks':num->real`; `kappa:real`; `ts:real`; `s:real`;
                   `hs:(A)rfs_history`] P3H_STEPF_AT_BAD) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s y. &0 <= s /\ s < ts /\ y IN topspace(rfs_top_at (hs:(A)rfs_history) s)
                      ==> p3_noncoll_at (rfs_view hs) kappa eps y s`
  (LABEL_TAC "LT") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_NONCOLL_KAPPA_MONO THEN
    EXISTS_TAC `p3_stepf (ks':num->real) s` THEN CONJ_TAC THENL
     [REWRITE_TAC[rfs_view] THEN MATCH_MP_TAC P3H_NONCOLL_UNTRUNC THEN
      EXISTS_TAC `ts:real` THEN ASM_REWRITE_TAC[GSYM rfs_view; ETA_AX];
      USE_THEN "KM" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s < ts` THENL
   [USE_THEN "LT" MATCH_MP_TAC THEN ASM_MESON_TAC[P3H_TOPSPACE_TIME_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `s = ts:real` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P3H_NONCOLL_CLOSED THEN REPEAT CONJ_TAC THENL
   [USE_THEN "REG" (MATCH_MP_TAC o REWRITE_RULE[P2C_HISTORY_REGULAR_STATEMENT]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_view; rfs_vtop] THEN ASM_SIMP_TAC[P3H_HIST_COMPACT_AT];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[rfs_view; rfs_vtop];
    REWRITE_TAC[rfs_view; rfs_vtop] THEN REWRITE_TAC[GSYM rfs_view] THEN
    MAP_EVERY X_GEN_TAC [`s':real`; `z:A`] THEN STRIP_TAC THEN
    USE_THEN "LT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[P3H_TOPSPACE_TIME_POS]]);;

(* ========================================================================= *)
(* Prop 17.1, the T' extension step (E2) and its packaging:                 *)
(* the blow-up sequence of the counterexamples (Thm 11.8's hypothesis), the *)
(* hypotheses of the counterexample sequence along subsequences, the Step B *)
(* form along subsequences; then E2: back(Tc) for all Tc < Tb gives         *)
(* back(Tb + d) along a subsequence (Tb = 0: START; Tb > 0: 11.8 first part *)
(* with Cor 11.16, E1, Step B, RFA_171_UTB and RFA_171_BALL_FWD, Step D,     *)
(* BACK_FROM_PERSIST).                                                       *)
(* ========================================================================= *)

let P3H_171_BLOWUP_CEX = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa.
              eps <= eps0 /\ &0 < kappa /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
              (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
                       ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s)
              ==> p3_blowup_seq (C,eps,kappa,eps,inv(&64 * C)) hs x ts`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_SEQ_FLOW) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FLW"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[p3h_cexseq] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3H_171_BLOWUP_SEQ THEN
  MAP_EVERY EXISTS_TAC
    [`hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`;
     `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`; `r:num->real`;
     `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "FLW" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
     `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* The hypotheses of the counterexample sequence pass to subsequences.       *)

let P3H_171_PKG_SUBSEQ = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa sub.
     p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
     (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
              ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
     (!a s. apx_sphere_sep (rfs_top_at (hs a) s) (rfs_atlas_at (hs a) s)) /\
     (!a. p2b_hs_sep (hs a)) /\
     p3_subseq sub
     ==> p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds)
           (dlt o sub,r o sub,rs' o sub,ks' o sub,dd o sub,hs o sub,ts o sub,x o sub) /\
         (!a s y. s <= (ts o sub) a /\ y IN topspace(rfs_top_at ((hs o sub) a) s)
                  ==> p3_noncoll_at (rfs_view ((hs o sub) a)) kappa eps y s) /\
         (!a s. apx_sphere_sep (rfs_top_at ((hs o sub) a) s) (rfs_atlas_at ((hs o sub) a) s)) /\
         (!a. p2b_hs_sep ((hs o sub) a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC P3H_CEXSEQ_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM]);;

(* The Step B form (A-dependent extension past Tb) passes to subsequences.  *)

let P3H_EXTB_SUBSEQ = prove
 (`!(hs:num->(A)rfs_history) ts x Tb sub.
     p3_subseq sub /\
     (!A. &0 < A
          ==> ?dl K N. &0 < dl /\ &0 <= K /\
                !n. N <= n
                    ==> rfs_persists (rfs_view (hs n))
                          (rfs_vball (rfs_view (hs n)) (ts n) (x n)
                             (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))))
                          (ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)))
                          (ts n) /\
                        !s y. ts n - (Tb + dl) * inv(rfs_vscalar (rfs_view (hs n)) (ts n) (x n)) < s /\
                              s <= ts n /\
                              y IN rfs_vball (rfs_view (hs n)) (ts n) (x n)
                                     (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (ts n) (x n))))
                              ==> rfs_vscalar (rfs_view (hs n)) s y <=
                                  K * rfs_vscalar (rfs_view (hs n)) (ts n) (x n))
     ==> (!A. &0 < A
          ==> ?dl K N. &0 < dl /\ &0 <= K /\
                !n. N <= n
                    ==> rfs_persists (rfs_view ((hs o sub) n))
                          (rfs_vball (rfs_view ((hs o sub) n)) ((ts o sub) n) ((x o sub) n)
                             (A * inv(sqrt(rfs_vscalar (rfs_view ((hs o sub) n)) ((ts o sub) n)
                                                ((x o sub) n)))))
                          ((ts o sub) n - (Tb + dl) *
                             inv(rfs_vscalar (rfs_view ((hs o sub) n)) ((ts o sub) n) ((x o sub) n)))
                          ((ts o sub) n) /\
                        !s y. (ts o sub) n - (Tb + dl) *
                                inv(rfs_vscalar (rfs_view ((hs o sub) n)) ((ts o sub) n)
                                      ((x o sub) n)) < s /\
                              s <= (ts o sub) n /\
                              y IN rfs_vball (rfs_view ((hs o sub) n)) ((ts o sub) n) ((x o sub) n)
                                     (A * inv(sqrt(rfs_vscalar (rfs_view ((hs o sub) n))
                                                     ((ts o sub) n) ((x o sub) n))))
                              ==> rfs_vscalar (rfs_view ((hs o sub) n)) s y <=
                                  K * rfs_vscalar (rfs_view ((hs o sub) n)) ((ts o sub) n)
                                        ((x o sub) n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  REMOVE_THEN "E" (MP_TAC o SPEC `A:real`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EN"))) THEN
  ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "EN" MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[P3H_SUBSEQ_GE]);;

