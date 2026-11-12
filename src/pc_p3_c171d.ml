(* ========================================================================= *)
(* Unit pc_p3_c171d: MT Prop 17.1, the assembly.  The extension step of the  *)
(* T' argument (Thm 11.8 first part with its Cor 11.16 clause, the region    *)
(* bounds of its limit, Steps B and D, RFA_171_UTB and RFA_171_BALL_FWD),    *)
(* the T' conclusion (some x_n has a canonv neighbourhood), the              *)
(* counterexample sequence S1 (Lemma 17.2 at r_a, Lemma 17.7 at              *)
(* A' = D' = t' = a + 1, the worst bad point, no fresh cap, Prop 16.1 with   *)
(* ks up to i and kappa after), P3H_PROP_17_1_CORE and the route theorem     *)
(* P3_PROP_17_1_ROUTE (at w = (:real^3)).                                    *)
(* ========================================================================= *)

needs "src/pc_p3_c171c.ml";;
needs "src/pc_rfa_171u.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Prop 17.1, E2 one step: along the counterexample sequence,                *)
(* if back(Tc) holds for every Tc < Tb then back(Tb + d) holds along a       *)
(* subsequence, d > 0.  Tb = 0: P3H_171_START.  Tb > 0: Thm 11.8 first part  *)
(* at T0 = Tb with the Cor 11.16 clause (sub), E1 (P3H_171_RB_FROM_LIMIT),   *)
(* Step B (P3H_171_EXT_B), RFA_171_UTB (sub2, uniform D at -Tb),             *)
(* RFA_171_BALL_FWD, Step D (P3H_171_EXT_D) and P3H_BACK_FROM_PERSIST.       *)
(* ========================================================================= *)

let P3H_171_EXT_ONE = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_THM_11_8_STATEMENT u (:real^3)
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa Tb.
              eps <= eps0 /\ &0 < kappa /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
              (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
                       ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
              (!a s. apx_sphere_sep (rfs_top_at (hs a) s) (rfs_atlas_at (hs a) s)) /\
              (!a. p2b_hs_sep (hs a)) /\
              &0 <= Tb /\ (!Tc. Tc < Tb ==> p3_blowup_back (kappa,eps) hs x ts Tc)
              ==> ?k d. p3_subseq k /\ &0 < d /\
                        p3_blowup_back (kappa,eps) (hs o k) (x o k) (ts o k) (Tb + d)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_START) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "START"))) THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_EXT_B) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EXTB"))) THEN
  MP_TAC(ISPEC `u:A->bool` RFA_171_UTB) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UTB"))) THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_EXT_D) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EXTD"))) THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_BLOWUP_CEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BCEX"))) THEN
  UNDISCH_TAC `P2_THM_11_8_STATEMENT (u:A->bool) (:real^3)` THEN REWRITE_TAC[P2_THM_11_8_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T118"))) THEN
  EXISTS_TAC `min (min e1 (min e2 e3)) (min e4 (min e5 e6))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (CONJUNCTS_THEN2 (LABEL_TAC "NC")
    (CONJUNCTS_THEN2 (LABEL_TAC "SEP") (CONJUNCTS_THEN2 (LABEL_TAC "SO")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BK")))))))) THEN
  USE_THEN "CEX" (fun th -> MP_TAC(MATCH_MP (SPEC_ALL (MP (ISPEC `u:A->bool` RFA_171_CEX_VF)
    (ASSUME `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)`))) th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "VF") (LABEL_TAC "QINF")) THEN
  SUBGOAL_THEN `&2 <= C /\ &0 < eps` STRIP_ASSUME_TAC THENL
   [USE_THEN "CEX" (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[p3h_cexseq]) THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[p3h_inst] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `Tb = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "START" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`; `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`; `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `kappa:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num->num` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`k:num->num`; `d:real`] THEN ASM_REWRITE_TAC[REAL_ADD_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Tb` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "BCEX" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`; `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`; `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `kappa:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "T118" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `eps:real`;
    `inv(&64 * C)`; `hs:num->(A)rfs_history`; `x:num->A`; `ts:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "SO" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[p2b_hs_sep] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Tb:real` o CONJUNCT1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "BK" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:(real^3)topology`
    (X_CHOOSE_THEN `atlas:((real^3->bool)#(real^3->real^3))->bool`
    (X_CHOOSE_THEN `g:real->real^3->real^3^3` (X_CHOOSE_THEN `xl:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FLIM")
       (CONJUNCTS_THEN2 (LABEL_TAC "CPL") (CONJUNCTS_THEN2 (LABEL_TAC "LOC")
        (LABEL_TAC "B79")))))))))) THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) o (sub:num->num)`; `(ts:num->real) o (sub:num->num)`;
                 `(x:num->A) o (sub:num->num)`; `Tb:real`; `top:(real^3)topology`;
                 `atlas:((real^3->bool)#(real^3->real^3))->bool`; `g:real->real^3->real^3^3`;
                 `xl:real^3`] P3H_171_RB_FROM_LIMIT) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "CPL" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RBL") (LABEL_TAC "RB0"))] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`; `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`; `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `kappa:real`; `sub:num->num`] P3H_171_PKG_SUBSEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CEX1") (LABEL_TAC "PK1")) THEN
  SUBGOAL_THEN `!Tc. Tc < Tb ==> p3_blowup_back (kappa,eps) ((hs:num->(A)rfs_history) o (sub:num->num))
                                   ((x:num->A) o sub) ((ts:num->real) o sub) Tc`
  (LABEL_TAC "BK1") THENL
   [X_GEN_TAC `Tc:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `eps:real`; `hs:num->(A)rfs_history`; `x:num->A`;
                   `ts:num->real`; `Tc:real`; `I:num->num`; `sub:num->num`; `0`] P3H_BACK_SEL) THEN
    REWRITE_TAC[I_O_ID; I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [USE_THEN "BK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXISTS_TAC `(sub:num->num) j` THEN
    ASM_SIMP_TAC[P3H_SUBSEQ_GE];
    ALL_TAC] THEN
  USE_THEN "EXTB" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `(dlt:num->real) o (sub:num->num)`; `(r:num->real) o (sub:num->num)`; `(rs':num->(num->real)) o (sub:num->num)`; `(ks':num->(num->real)) o (sub:num->num)`; `(dd:num->(num->real)) o (sub:num->num)`; `(hs:num->(A)rfs_history) o (sub:num->num)`; `(ts:num->real) o (sub:num->num)`; `(x:num->A) o (sub:num->num)`; `kappa:real`; `Tb:real`]) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "EB1")] THEN
  USE_THEN "UTB" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `(dlt:num->real) o (sub:num->num)`; `(r:num->real) o (sub:num->num)`; `(rs':num->(num->real)) o (sub:num->num)`; `(ks':num->(num->real)) o (sub:num->num)`; `(dd:num->(num->real)) o (sub:num->num)`; `(hs:num->(A)rfs_history) o (sub:num->num)`; `(ts:num->real) o (sub:num->num)`; `(x:num->A) o (sub:num->num)`; `kappa:real`; `Tb:real`]) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `DU:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DUB"))))) THEN
  SUBGOAL_THEN `p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds)
                  (((dlt:num->real) o (sub:num->num)) o (sub2:num->num),
                   ((r:num->real) o sub) o sub2,((rs':num->num->real) o sub) o sub2,
                   ((ks':num->num->real) o sub) o sub2,((dd:num->num->real) o sub) o sub2,
                   ((hs:num->(A)rfs_history) o sub) o sub2,((ts:num->real) o sub) o sub2,
                   ((x:num->A) o sub) o sub2)`
  (LABEL_TAC "CEX2") THENL
   [MATCH_MP_TAC P3H_CEXSEQ_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) o (sub:num->num)`; `(ts:num->real) o (sub:num->num)`;
                 `(x:num->A) o (sub:num->num)`; `Tb:real`; `sub2:num->num`] P3H_EXTB_SUBSEQ) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "EB2")] THEN
  MP_TAC(SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `((dlt:num->real) o (sub:num->num)) o (sub2:num->num)`; `((r:num->real) o (sub:num->num)) o (sub2:num->num)`; `((rs':num->(num->real)) o (sub:num->num)) o (sub2:num->num)`; `((ks':num->(num->real)) o (sub:num->num)) o (sub2:num->num)`; `((dd:num->(num->real)) o (sub:num->num)) o (sub2:num->num)`; `((hs:num->(A)rfs_history) o (sub:num->num)) o (sub2:num->num)`; `((ts:num->real) o (sub:num->num)) o (sub2:num->num)`; `((x:num->A) o (sub:num->num)) o (sub2:num->num)`; `Tb:real`] (MP (ISPEC `u:A->bool` RFA_171_BALL_FWD)
    (ASSUME `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)`))) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "FW2")] THEN
  USE_THEN "EXTD" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `((dlt:num->real) o (sub:num->num)) o (sub2:num->num)`; `((r:num->real) o (sub:num->num)) o (sub2:num->num)`; `((rs':num->(num->real)) o (sub:num->num)) o (sub2:num->num)`; `((ks':num->(num->real)) o (sub:num->num)) o (sub2:num->num)`; `((dd:num->(num->real)) o (sub:num->num)) o (sub2:num->num)`; `((hs:num->(A)rfs_history) o (sub:num->num)) o (sub2:num->num)`; `((ts:num->real) o (sub:num->num)) o (sub2:num->num)`; `((x:num->A) o (sub:num->num)) o (sub2:num->num)`; `Tb:real`]) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `DU:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PD"))) THEN
  MAP_EVERY EXISTS_TAC [`(sub:num->num) o (sub2:num->num)`; `dl:real`] THEN
  ASM_REWRITE_TAC[o_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3H_SUBSEQ_COMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P3H_BACK_FROM_PERSIST THEN REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "PD" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `n:num` THEN
    USE_THEN "VF" (MP_TAC o SPEC `(sub:num->num) ((sub2:num->num) n)`) THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "NC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Prop 17.1: back(Tb) for every Tb along a subsequence of the counterexample *)
(* sequence (E2 one step + P3H_171_TINF), and the T' = infinity conclusion:  *)
(* some x_n has a canonical neighbourhood (Thm 11.8 second part, Cor 9.95,   *)
(* P3H_171_INFTY).                                                          *)
(* ========================================================================= *)

let P3H_171_ALL_BACK = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_THM_11_8_STATEMENT u (:real^3)
     ==> ?eps0. &0 < eps0 /\
           !C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa.
              eps <= eps0 /\ &0 < kappa /\
              p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
              (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
                       ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
              (!a s. apx_sphere_sep (rfs_top_at (hs a) s) (rfs_atlas_at (hs a) s)) /\
              (!a. p2b_hs_sep (hs a))
              ==> ?s. p3_subseq s /\
                      !Tb. p3_blowup_back (kappa,eps) (hs o s) (x o s) (ts o s) Tb`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_171_EXT_ONE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ONE"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (CONJUNCTS_THEN2 (LABEL_TAC "NC")
    (CONJUNCTS_THEN2 (LABEL_TAC "SEP") (LABEL_TAC "SO")))))) THEN
  MATCH_MP_TAC P3H_171_TINF THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "CEX" (fun th -> MP_TAC(MATCH_MP (SPEC_ALL (MP (ISPEC `u:A->bool` RFA_171_CEX_VF)
      (CONJUNCT1 (CONJUNCT2 (ASSUME `P2_LEMMA_11_2_STATEMENT (u:A->bool) /\
                                    P2C_HISTORY_REGULAR_STATEMENT u /\
                                    P2_THM_11_8_STATEMENT u (:real^3)`))))) th)) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT1) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num->num`; `Tb:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`; `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`; `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `kappa:real`; `s:num->num`] P3H_171_PKG_SUBSEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  USE_THEN "ONE" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `(dlt:num->real) o (s:num->num)`; `(r:num->real) o (s:num->num)`; `(rs':num->(num->real)) o (s:num->num)`; `(ks':num->(num->real)) o (s:num->num)`; `(dd:num->(num->real)) o (s:num->num)`; `(hs:num->(A)rfs_history) o (s:num->num)`; `(ts:num->real) o (s:num->num)`; `(x:num->A) o (s:num->num)`; `kappa:real`; `Tb:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_ASSOC]);;

let P3H_171_CEX_CANONV = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_THM_11_8_STATEMENT u (:real^3) /\ P2_COR_9_95_STATEMENT u (:real^3)
     ==> ?eps0. &0 < eps0 /\
           !eps. &0 < eps /\ eps <= eps0
             ==> ?C0. &1 < C0 /\
                   !C hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x kappa.
                      C0 <= C /\ &0 < kappa /\
                      p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
                      (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
                               ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
                      (!a s. apx_sphere_sep (rfs_top_at (hs a) s) (rfs_atlas_at (hs a) s)) /\
                      (!a. p2b_hs_sep (hs a))
                      ==> ?n. p3_canonv_at (rfs_view (hs n)) C eps (x n) (ts n)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_ALL_BACK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AB"))) THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_BLOWUP_CEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BC"))) THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_INFTY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "INF"))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LE_MIN] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "INF" (fun th -> MP_TAC(MP (SPEC `eps:real` th)
    (CONJ (ASSUME `&0 < eps`) (ASSUME `eps <= e3`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C0"))) THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CEX") (CONJUNCTS_THEN2 (LABEL_TAC "NC")
    (CONJUNCTS_THEN2 (LABEL_TAC "SEP") (LABEL_TAC "SO")))))) THEN
  USE_THEN "AB" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`; `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`; `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `kappa:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`; `r:num->real`; `rs':num->(num->real)`; `ks':num->(num->real)`; `dd:num->(num->real)`; `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `kappa:real`; `s:num->num`] P3H_171_PKG_SUBSEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  USE_THEN "BC" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `(dlt:num->real) o (s:num->num)`; `(r:num->real) o (s:num->num)`; `(rs':num->(num->real)) o (s:num->num)`; `(ks':num->(num->real)) o (s:num->num)`; `(dd:num->(num->real)) o (s:num->num)`; `(hs:num->(A)rfs_history) o (s:num->num)`; `(ts:num->real) o (s:num->num)`; `(x:num->A) o (s:num->num)`; `kappa:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "C0" (MP_TAC o SPECL [`C:real`; `kappa:real`; `eps:real`; `inv(&64 * C)`;
    `(hs:num->(A)rfs_history) o (s:num->num)`; `(x:num->A) o (s:num->num)`;
    `(ts:num->real) o (s:num->num)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "CEX" (MP_TAC o SPEC `(s:num->num) n` o CONJUNCT1 o CONJUNCT2 o
                    REWRITE_RULE[p3h_cexseq]) THEN
    REWRITE_TAC[p3h_inst; p3_step_hyp; p3_struct] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `(s:num->num) n` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Prop 17.1, S1 bookkeeping: the step hypothesis is monotone in the control *)
(* bound dlt, and the kappa-sequence may be replaced by ks up to i and kappa *)
(* after (Prop 16.1 needs ks'(SUC i) = kappa; the counterexample histories   *)
(* come with arbitrary ks'); noncollapsing of a truncation at tau only reads *)
(* kappa(t) for t < tau.                                                     *)
(* ========================================================================= *)

let P3H_STEP_HYP_DLT_MONO = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt dlt' rs' ks' dd (hs:(A)rfs_history).
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\ dlt <= dlt'
     ==> p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt' (rs',ks',dd) hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_step_hyp] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dlt:real` THEN
  ASM_REWRITE_TAC[]);;

let P3H_TRUNC_KP_EQ = prove
 (`!(TM:real->A topology) (AT:real->((A->bool)#(A->real^3))->bool) (G:real->A->real^3^3)
    tau kp kp' r0.
     (!t. &0 <= t /\ t < tau ==> kp' t = kp t)
     ==> (rfs_noncollapsed (rfs_trunc (TM,AT,G) tau) kp' r0 <=>
          rfs_noncollapsed (rfs_trunc (TM,AT,G) tau) kp r0) /\
         (p3_noncoll_all (rfs_trunc (TM,AT,G) tau) kp' r0 <=>
          p3_noncoll_all (rfs_trunc (TM,AT,G) tau) kp r0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t (x:A). &0 <= t /\ x IN topspace (if t < tau then TM t else discrete_topology {})
                         ==> (kp':real->real) t = kp t`
  (LABEL_TAC "EQ") THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_trunc] THEN REWRITE_TAC[rfs_noncollapsed; p3_noncoll_all; rfs_vtop] THEN
  CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(kp':real->real) t = kp t` ASSUME_TAC THENL
    [USE_THEN "EQ" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    (let a = can (find_term (fun t -> t = `kp':real->real`)) (concl th)
     and b = can (find_term (fun t -> t = `kp:real->real`)) (concl th) in
     (a || b) && not (a && b)))) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  TRY(DISCH_THEN(MP_TAC o SPEC `r:real`)) THEN
  ASM_REWRITE_TAC[]);;

let P3H_STEP_HYP_KS = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) kappa ksi.
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
     &0 < kappa /\ kappa <= ks i /\
     (!j. j <= i ==> ksi j = ks j) /\ (!j. i < j ==> ksi j = kappa)
     ==> p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ksi,dd) hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_step_hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < p3_T i ==> p3_stepf (ksi:num->real) t = p3_stepf ks' t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p3_stepf] THEN
    SUBGOAL_THEN `p3_step t <= i` ASSUME_TAC THENL
     [MATCH_MP_TAC P3_STEP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history)`; `rfs_atlas_at (hs:(A)rfs_history)`;
                 `rfs_metric_at (hs:(A)rfs_history)`; `p3_T i`; `p3_stepf ks'`;
                 `p3_stepf (ksi:num->real)`; `eps:real`] P3H_TRUNC_KP_EQ) THEN
  ASM_REWRITE_TAC[GSYM rfs_view] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `p3_seq_ok (ks':num->real)` THEN REWRITE_TAC[p3_seq_ok] THEN
  DISCH_TAC THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j < i:num` THENL
   [SUBGOAL_THEN `j <= i /\ SUC j <= i` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `j:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(ksi:num->real) i = ks i /\ ksi (SUC i) = kappa` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ksi:num->real) j = kappa /\ ksi (SUC j) = kappa` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ========================================================================= *)
(* Prop 17.1, S1 per counterexample history: noncollapsing up to the first  *)
(* bad time for an arbitrary kappa-sequence ks' (P3H_171_NC_HIST applied to *)
(* ks up to i and kappa after), and the worst bad point as an instance      *)
(* p3h_inst (P3H_171_WORST_BAD with good = canonv at ts).                   *)
(* ========================================================================= *)

let P3H_171_NC_CEX = prove
 (`!(u:A->bool) C eps hf md g0 A0 i rs ks ds kappa dfun r' dnew rs' ks' dd
    (hs:(A)rfs_history) ts.
     P2C_HISTORY_REGULAR_STATEMENT u /\
     p3_noncoll_prop u (C,eps,hf,md,g0,A0) i (rs,ks,ds) kappa dfun /\
     &0 < kappa /\ kappa <= ks i /\ &0 < r' /\ r' <= rs i /\ rs' (SUC i) = r' /\
     dnew <= dfun r' /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dnew (rs',ks',dd) hs /\
     p3_T i <= ts /\ ts < rfs_horizon hs /\
     p3_canonv_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs')
     ==> !s y. s <= ts /\ y IN topspace(rfs_top_at hs s)
               ==> p3_noncoll_at (rfs_view hs) kappa eps y s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `kappa:real`; `dfun:real->real`; `r':real`; `rs':num->real`;
                 `\j. if j <= i then (ks:num->real) j else kappa`; `dd:num->real`;
                 `hs:(A)rfs_history`; `ts:real`] P3H_171_NC_HIST) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `~(SUC i <= i)`] THEN
  MATCH_MP_TAC P3H_STEP_HYP_KS THEN
  MAP_EVERY EXISTS_TAC [`ks':num->real`; `kappa:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3H_STEP_HYP_DLT_MONO THEN EXISTS_TAC `dnew:real` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[];
    SIMP_TAC[ARITH_RULE `!i j:num. i < j ==> ~(j <= i)`]]);;

let P3H_171_INST_FROM_BAD = prove
 (`!C eps hf md g0 A0 i rs ks ds dnew r' rs' ks' dd (hs:(A)rfs_history) ts x0.
     &2 <= C /\ &0 < eps /\ rs' (SUC i) = r' /\ &0 < r' /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dnew (rs',ks',dd) hs /\
     p3_T i <= ts /\ ts < rfs_horizon hs /\
     p3_canonv_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
     x0 IN topspace(rfs_top_at hs ts) /\
     inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x0 /\
     ~p3_canonv_at (rfs_view hs) C eps x0 ts
     ==> ?x. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dnew,r',rs',ks',dd,hs,ts,x) /\
             ~p3_canonv_at (rfs_view hs) C eps x ts`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dnew (rs',ks',dd)
                   (hs:(A)rfs_history)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`; `r':real`;
                 `\y:A. p3_canonv_at (rfs_view hs) C eps y ts`; `x0:A`] P3H_171_WORST_BAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[p3h_inst] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3_CANONV_ASSUMPTION_IMP THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN MATCH_MP_TAC P3_CANONV_AT_IMP THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Prop 17.1, S1 per counterexample history: the slice at an event time is *)
(* the new stage; the Lemma 17.7 configuration is monotone in (A', D', t');  *)
(* no fresh cap at ts in the A-ball of a bad point once the control is      *)
(* below dbar(C, md, A, D) (P3H_171_FRESH: such a cap makes x canonical).    *)
(* ========================================================================= *)

let P3H_VIEW_AT_EVENT = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ k <= hs_count hs /\ &0 <= hs_time hs k
     ==> rfs_top_at hs (hs_time hs k) = hs_top hs k /\
         rfs_atlas_at hs (hs_time hs k) = hs_atlas hs k /\
         rfs_metric_at hs (hs_time hs k) = hs_metric hs k (hs_time hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_time hs k < hs_time (hs:(A)rfs_history) (k + 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) (hs_time hs k) /\ rfs_slab hs (hs_time hs k) = k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[rfs_live] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) (k + 1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC RFS_SLAB_UNIQUE THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at]);;

let P3H_171_CFG_MONO = prove
 (`!(hs:(A)rfs_history) ts x Ap Dp tp A1 D1 t1.
     &0 < rfs_vscalar (rfs_view hs) ts x /\ Ap <= A1 /\ Dp <= D1 /\ tp <= t1 /\
     ~(?y k j. y IN rfs_vball (rfs_view hs) ts x
                      (A1 * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
               1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
               ts - t1 * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\
               hs_time hs k < ts /\
               y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
               p3_flowline hs y (hs_time hs k) ts /\
               (!s. hs_time hs k <= s /\ s <= ts
                    ==> rfs_vscalar (rfs_view hs) s y <= D1 * rfs_vscalar (rfs_view hs) ts x))
     ==> ~(?y k j. y IN rfs_vball (rfs_view hs) ts x
                          (Ap * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                   1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                   ts - tp * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\
                   hs_time hs k < ts /\
                   y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                   p3_flowline hs y (hs_time hs k) ts /\
                   (!s. hs_time hs k <= s /\ s <= ts
                        ==> rfs_vscalar (rfs_view hs) s y <= Dp * rfs_vscalar (rfs_view hs) ts x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`y:A`; `k:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `&0 < inv Q /\ &0 < inv(sqrt Q)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view hs) ts x (Ap * inv(sqrt Q))` THEN
    REWRITE_TAC[rfs_vball; rfs_view] THEN
    MATCH_MP_TAC(SET_RULE `!s t (y:A). s SUBSET t ==> y IN s ==> y IN t`) THEN
    MATCH_MP_TAC P2BC_BALL_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ts - tp * inv Q` THEN
    ASM_REWRITE_TAC[REAL_ARITH `ts - a <= ts - b <=> b <= a`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Dp * Q` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]]);;

let P3H_171_HF_AT = prove
 (`P2_THM_12_32_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_PROP_12_31_STATEMENT /\
   P3_STD_C2_BOUND_STATEMENT /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)
   ==> ?eps0. &0 < eps0 /\
         !eps g0 A0. &0 < eps /\ eps <= eps0 /\ p3_std_initial g0 A0
           ==> ?C0. &1 < C0 /\
                 !C hf md A D. C0 <= C /\ p3_hfun C hf /\ p3_modulus md /\ &0 < A /\ &0 < D
                   ==> ?dbar. &0 < dbar /\
                         !i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) ts x.
                            p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                            p2c_regular_view (rfs_view hs) /\ dlt <= dbar /\
                            p3_T i <= ts /\ ts < rfs_horizon hs /\
                            x IN topspace(rfs_top_at hs ts) /\
                            &0 < rfs_vscalar (rfs_view hs) ts x /\
                            ~p3_canonv_at (rfs_view hs) C eps x ts /\
                            (!y. y IN rfs_vball (rfs_view hs) ts x
                                        (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                                 ==> rfs_vscalar (rfs_view hs) ts y <=
                                     D * rfs_vscalar (rfs_view hs) ts x)
                            ==> ~(?k j y. 1 <= k /\ k <= hs_count hs /\
                                          j IN ev_index(hs_event hs k) /\
                                          hs_time hs k = ts /\
                                          y IN rfs_vball (rfs_view hs) ts x
                                                 (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                                          y IN IMAGE (ev_capm (hs_event hs k) j)
                                                     (cball(vec 0,&1)))`,
  DISCH_THEN(MP_TAC o MATCH_MP P3H_171_FRESH) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FR"))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "FR" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FR"))) THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `hf:real->real->real`; `md:real->real`; `A:real`; `D:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "FR" (MP_TAC o SPECL [`C:real`; `md:real->real`; `A:real`; `D:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dbar:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FR"))) THEN
  EXISTS_TAC `dbar:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`k:num`; `j:num`; `y:A`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `~p3_canonv_at (rfs_view (hs:(A)rfs_history)) C eps x ts` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= ts` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_TOPSPACE_TIME_POS THEN
    MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `x:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                 (hs:(A)rfs_history)` THEN
  REWRITE_TAC[p3_step_hyp; p3_struct] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3H_VIEW_AT_EVENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3_stepf (dd:num->real) ts <= dbar` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`i:num`; `dd:num->real`; `(dd:num->real) (SUC i)`; `ts:real`; `ts:real`;
                   `hs:(A)rfs_history`] P3H_STEPF_AT_BAD) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_ok")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[p3_cap_ok] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_TAC `xi:real^3->real^3`)) THEN
  REMOVE_THEN "FR" (MP_TAC o SPECL
    [`p3_stepf (dd:num->real)`;
     `p3_hscale hf (p3_stepf (rs':num->real)) (p3_stepf (dd:num->real))`;
     `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`;
     `x:A`; `y:A`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN REWRITE_TAC[p3_canonv_at; p3_strong_canonv] THENL
     [EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `Y:A->bool` THEN
      ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric];
      EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN DISJ1_TAC THEN
      EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `&0 < p3_stepf (rs':num->real) ts /\ &0 < p3_stepf (dd:num->real) ts`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      is_imp(snd(dest_forall(concl th))) &&
      can (find_term (fun t -> t = `p3_stepf (dd:num->real)`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts y <=
                D * rfs_vscalar (rfs_view hs) ts x`
  MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(y:A) IN rfs_vball (rfs_view hs) ts x
                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x)))` THEN
  UNDISCH_TAC `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  UNDISCH_TAC `(x:A) IN topspace(rfs_top_at hs ts)` THEN
  REWRITE_TAC[rfs_vball; rfs_view; rfs_vscalar; mfd_ball; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_neck2_ok")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p3_hscale] THEN UNDISCH_TAC `p3_hfun C hf` THEN REWRITE_TAC[p3_hfun] THEN
    DISCH_THEN(MP_TAC o SPECL [`p3_stepf (dd:num->real) ts * p3_stepf (rs':num->real) ts`;
                               `p3_stepf (dd:num->real) ts`]) THEN
    ASM_SIMP_TAC[REAL_LT_MUL]]);;

(* ========================================================================= *)
(* Prop 17.1, S1 per index a: if no (r', dnew) works, then                   *)
(* for every a there is a counterexample history at r <= 1/(a+1) with      *)
(* control dnew <= 1/(a+1), its first bad time (Lemma 17.2) and worst bad   *)
(* point (an instance p3h_inst, not canonv), no Lemma 17.7 configuration    *)
(* with A' = D' = t' = a + 1, kappa-noncollapsed up to ts (Prop 16.1) and   *)
(* stage separation.  H172 and H177 are Lemmas 17.2 and 17.7 (the canonv    *)
(* forms) at fixed eps, g0, A0, C, hf, md, i, rs, ks, ds.                   *)
(* ========================================================================= *)

let P3H_171_S1_ONE = prove
 (`!(u:A->bool) C eps hf md g0 A0 i rs ks ds kappa dfun.
     P2C_HISTORY_REGULAR_STATEMENT u /\ APX_SC_SPHERE_SEP_STATEMENT (:A) /\
     RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\
     &2 <= C /\ &0 < eps /\ &0 < rs i /\ &0 < kappa /\ kappa <= ks i /\
     (!r'. &0 < r' /\ r' <= rs i ==> &0 < dfun r' /\ dfun r' <= ds i) /\
     p3_noncoll_prop u (C,eps,hf,md,g0,A0) i (rs,ks,ds) kappa dfun /\
     (!r'. &0 < r' /\ r' <= rs i
              ==> ?dlt. &0 < dlt /\
                        !rs' ks' dd (hs:(A)rfs_history).
                           rs' (SUC i) = r' /\
                           p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                           ~p3_canonv_assumption (rfs_view hs) C eps (p3_stepf rs')
                           ==> ?ts x. p3_T i <= ts /\ ts < rfs_horizon hs /\
                                      p3_canonv_assumption (rfs_trunc (rfs_view hs) ts)
                                        C eps (p3_stepf rs') /\
                                      x IN topspace(rfs_top_at hs ts) /\
                                      inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                                      ~p3_canonv_at (rfs_view hs) C eps x ts) /\
     (!Ap Dp tp. &0 < Ap /\ &0 < Dp /\ &0 < tp
              ==> ?rstar. &0 < rstar /\
                    !r'. &0 < r' /\ r' <= rstar /\ r' <= rs i
                      ==> ?dlt. &0 < dlt /\
                            !rs' ks' dd (hs:(A)rfs_history) ts x y k j.
                               rs' (SUC i) = r' /\
                               p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                               p3_T i <= ts /\ ts < rfs_horizon hs /\
                               p3_canonv_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
                               x IN topspace(rfs_top_at hs ts) /\
                               inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                               y IN rfs_vball (rfs_view hs) ts x
                                      (Ap * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                               1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                               ts - tp * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\
                               hs_time hs k < ts /\
                               y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                               p3_flowline hs y (hs_time hs k) ts /\
                               (!s. hs_time hs k <= s /\ s <= ts
                                    ==> rfs_vscalar (rfs_view hs) s y <=
                                        Dp * rfs_vscalar (rfs_view hs) ts x)
                               ==> p3_canonv_at (rfs_view hs) C eps x ts) /\
     ~(?r' dnew. &0 < r' /\ r' <= rs i /\ &0 < dnew /\ dnew <= dfun r' /\
                  p3_canon_prop u (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dnew)
     ==> !a. ?dnew r rs' ks' dd (hs:(A)rfs_history) ts x.
                p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dnew,r,rs',ks',dd,hs,ts,x) /\
                ~p3_canonv_at (rfs_view hs) C eps x ts /\
                r <= inv(&a + &1) /\ dnew <= inv(&a + &1) /\
                ~(?y k j. y IN rfs_vball (rfs_view hs) ts x ((&a + &1) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                      1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                      ts - (&a + &1) * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\
                      hs_time hs k < ts /\
                      y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                      p3_flowline hs y (hs_time hs k) ts /\
                      (!s. hs_time hs k <= s /\ s <= ts
                           ==> rfs_vscalar (rfs_view hs) s y <= (&a + &1) * rfs_vscalar (rfs_view hs) ts x)) /\
                (!s y. s <= ts /\ y IN topspace(rfs_top_at hs s)
                       ==> p3_noncoll_at (rfs_view hs) kappa eps y s) /\
                p2b_hs_sep hs`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "DF") (CONJUNCTS_THEN2 (LABEL_TAC "NP")
    (CONJUNCTS_THEN2 (LABEL_TAC "H172") (CONJUNCTS_THEN2 (LABEL_TAC "H177")
     (LABEL_TAC "NEG"))))))))))))) THEN
  X_GEN_TAC `a:num` THEN
  SUBGOAL_THEN `&0 < &a + &1 /\ &0 < inv(&a + &1)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[REAL_LT_INV_EQ]];
    ALL_TAC] THEN
  REMOVE_THEN "H177" (MP_TAC o SPECL [`&a + &1`; `&a + &1`; `&a + &1`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rstar:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R7"))) THEN
  SUBGOAL_THEN `?r. &0 < r /\ r <= (rs:num->real) i /\ r <= rstar /\ r <= inv(&a + &1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min ((rs:num->real) i) (min rstar (inv(&a + &1)))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "R7" (MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt7:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D7"))) THEN
  REMOVE_THEN "H172" (MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
  REMOVE_THEN "DF" (MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?dnew. &0 < dnew /\ dnew <= (dfun:real->real) r /\ dnew <= dlt2 /\ dnew <= dlt7 /\
                       dnew <= inv(&a + &1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min ((dfun:real->real) r) (min dlt2 (min dlt7 (inv(&a + &1))))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "NEG" (MP_TAC o REWRITE_RULE[NOT_EXISTS_THM] ) THEN
  DISCH_THEN(MP_TAC o SPECL [`r:real`; `dnew:real`]) THEN
  ASM_REWRITE_TAC[p3_canon_prop; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `rs':num->real` (X_CHOOSE_THEN `ks':num->real`
    (X_CHOOSE_THEN `dd:num->real` (X_CHOOSE_THEN `hs:(A)rfs_history` STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "D2" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
                                    `hs:(A)rfs_history`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3H_STEP_HYP_DLT_MONO THEN
    EXISTS_TAC `dnew:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `dnew:real`; `r:real`; `rs':num->real`; `ks':num->real`;
                 `dd:num->real`; `hs:(A)rfs_history`; `ts:real`; `x0:A`] P3H_171_INST_FROM_BAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`dnew:real`; `r:real`; `rs':num->real`; `ks':num->real`;
                        `dd:num->real`; `hs:(A)rfs_history`; `ts:real`; `x:A`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3h_inst] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_inst")) (concl th))) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`y:A`; `k:num`; `j:num`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~p3_canonv_at (rfs_view (hs:(A)rfs_history)) C eps x ts` THEN REWRITE_TAC[] THEN
    REMOVE_THEN "D7" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `y:A`;
                          `k:num`; `j:num`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3H_STEP_HYP_DLT_MONO THEN
    EXISTS_TAC `dnew:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3H_171_NC_CEX THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `C:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
      `ds:num->real`; `dfun:real->real`; `r:real`; `dnew:real`; `rs':num->real`;
      `ks':num->real`; `dd:num->real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3_STRUCT_SPHERE_SEP THEN
    UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dnew (rs',ks',dd)
                   (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_step_hyp] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `p3_stepf (rs':num->real)`; `p3_stepf (dd:num->real)`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Prop 17.1, S1 sequence: numeric facts, and the                           *)
(* counterexample sequence from the per-index choices (P3H_171_S1_ONE) by   *)
(* SKOLEM: p3h_cexseq (Q to infinity, Thm 10.2 ball bounds, no 17.7         *)
(* configuration by monotonicity, no fresh cap by P3H_171_HF_AT), with      *)
(* noncollapsing, separation and badness of x a.  BB and HF are the Thm     *)
(* 10.2 and fresh-cap lemmas at fixed eps, C (and g0, A0, hf, md for HF).   *)
(* ========================================================================= *)

let P3H_ARCH_LE1 = prove
 (`!x. ?N. !a. N <= a ==> x <= &a + &1`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let P3H_INV_SUC_SMALL = prove
 (`!d. &0 < d ==> ?N. !a. N <= a ==> inv(&a + &1) <= d`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `inv d` P3H_ARCH_LE1) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3H_INV_SQ_LARGE = prove
 (`!r:num->real. (!a. &0 < r a /\ r a <= inv(&a + &1))
                 ==> !B. ?N. !a. N <= a ==> B < inv(r a pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `B:real` THEN
  MP_TAC(SPEC `B + &1` P3H_ARCH_LE1) THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (r:num->real) a /\ r a <= inv(&a + &1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&a + &1 <= inv((r:num->real) a)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `B + &1 <= &a + &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `a:num` REAL_POS) THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(&a + &1) pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&a + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

let P3H_171_S1_SEQ = prove
 (`!(u:A->bool) C eps hf md g0 A0 i rs ks ds kappa.
     P2C_HISTORY_REGULAR_STATEMENT u /\
     (!A. &0 < A
          ==> ?D0 D. &0 < D0 /\ &0 < D /\
                !hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x.
                   rs' (SUC i) = r' /\ &0 < r' /\ D0 <= inv(r' pow 2) /\
                   p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                   p3_T i <= ts /\ ts < rfs_horizon hs /\
                   rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps
                     (p3_stepf rs') /\
                   x IN topspace(rfs_top_at hs ts) /\
                   inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                   (!y. y IN topspace(rfs_top_at hs ts) /\
                        &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
                        ==> p3_canon_at (rfs_view hs) C eps y ts)
                   ==> !y. y IN rfs_vball (rfs_view hs) ts x
                                  (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                           ==> rfs_vscalar (rfs_view hs) ts y <=
                               D * rfs_vscalar (rfs_view hs) ts x) /\
     (!A D. &0 < A /\ &0 < D
            ==> ?dbar. &0 < dbar /\
                  !i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) ts x.
                     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                     p2c_regular_view (rfs_view hs) /\ dlt <= dbar /\
                     p3_T i <= ts /\ ts < rfs_horizon hs /\
                     x IN topspace(rfs_top_at hs ts) /\
                     &0 < rfs_vscalar (rfs_view hs) ts x /\
                     ~p3_canonv_at (rfs_view hs) C eps x ts /\
                     (!y. y IN rfs_vball (rfs_view hs) ts x
                                 (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x)))
                          ==> rfs_vscalar (rfs_view hs) ts y <=
                              D * rfs_vscalar (rfs_view hs) ts x)
                     ==> ~(?k j y. 1 <= k /\ k <= hs_count hs /\
                                   j IN ev_index(hs_event hs k) /\
                                   hs_time hs k = ts /\
                                   y IN rfs_vball (rfs_view hs) ts x
                                          (A * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                                   y IN IMAGE (ev_capm (hs_event hs k) j)
                                              (cball(vec 0,&1)))) /\
     (!a. ?dnew r rs' ks' dd (hs:(A)rfs_history) ts x.
            p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dnew,r,rs',ks',dd,hs,ts,x) /\
                ~p3_canonv_at (rfs_view hs) C eps x ts /\
                r <= inv(&a + &1) /\ dnew <= inv(&a + &1) /\
                ~(?y k j. y IN rfs_vball (rfs_view hs) ts x ((&a + &1) * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                      1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                      ts - (&a + &1) * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\
                      hs_time hs k < ts /\
                      y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                      p3_flowline hs y (hs_time hs k) ts /\
                      (!s. hs_time hs k <= s /\ s <= ts
                           ==> rfs_vscalar (rfs_view hs) s y <= (&a + &1) * rfs_vscalar (rfs_view hs) ts x)) /\
                (!s y. s <= ts /\ y IN topspace(rfs_top_at hs s)
                       ==> p3_noncoll_at (rfs_view hs) kappa eps y s) /\
                p2b_hs_sep hs)
     ==> ?dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x.
           p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\
           (!a s y. s <= ts a /\ y IN topspace(rfs_top_at (hs a) s)
                    ==> p3_noncoll_at (rfs_view (hs a)) kappa eps y s) /\
           (!a s. apx_sphere_sep (rfs_top_at (hs a) s) (rfs_atlas_at (hs a) s)) /\
           (!a. p2b_hs_sep (hs a)) /\
           (!a. ~p3_canonv_at (rfs_view (hs a)) C eps (x a) (ts a))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "REG") (CONJUNCTS_THEN2 (LABEL_TAC "BB")
    (CONJUNCTS_THEN2 (LABEL_TAC "HF") MP_TAC))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt:num->real` (X_CHOOSE_THEN `r:num->real`
    (X_CHOOSE_THEN `rs':num->num->real` (X_CHOOSE_THEN `ks':num->num->real`
    (X_CHOOSE_THEN `dd:num->num->real` (X_CHOOSE_THEN `hs:num->(A)rfs_history`
    (X_CHOOSE_THEN `ts:num->real` (X_CHOOSE_THEN `x:num->A` (LABEL_TAC "PA"))))))))) THEN
  MAP_EVERY EXISTS_TAC [`dlt:num->real`; `r:num->real`; `rs':num->num->real`;
    `ks':num->num->real`; `dd:num->num->real`; `hs:num->(A)rfs_history`; `ts:num->real`;
    `x:num->A`] THEN
  SUBGOAL_THEN
   `!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
          ((dlt:num->real) a,(r:num->real) a,(rs':num->num->real) a,(ks':num->num->real) a,
           (dd:num->num->real) a,(hs:num->(A)rfs_history) a,(ts:num->real) a,(x:num->A) a)`
  (LABEL_TAC "INST") THENL [USE_THEN "PA" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `!a. &0 < (r:num->real) a /\ r a <= inv(&a + &1) /\
                    inv(r a pow 2) <= rfs_vscalar (rfs_view ((hs:num->(A)rfs_history) a))
                                        ((ts:num->real) a) ((x:num->A) a) /\
                    rfs_history_ok (hs a) /\ p2c_regular_view (rfs_view (hs a)) /\
                    &0 < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)`
  (LABEL_TAC "BAS") THENL
   [X_GEN_TAC `a:num` THEN
    USE_THEN "PA" (MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
    SUBGOAL_THEN `rfs_history_ok ((hs:num->(A)rfs_history) a)` ASSUME_TAC THENL
     [UNDISCH_TAC `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) ((dlt:num->real) a)
                     ((rs':num->num->real) a,(ks':num->num->real) a,(dd:num->num->real) a)
                     ((hs:num->(A)rfs_history) a)` THEN SIMP_TAC[p3_step_hyp; p3_struct];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "REG" (MATCH_MP_TAC o REWRITE_RULE[P2C_HISTORY_REGULAR_STATEMENT]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((r:num->real) a pow 2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!B. ?N. !a. N <= a ==> B < inv((r:num->real) a pow 2)` (LABEL_TAC "RINF") THENL
   [MATCH_MP_TAC P3H_INV_SQ_LARGE THEN USE_THEN "BAS" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?D N. &0 < D /\
                  !a z. N <= a /\
                        z IN rfs_vball (rfs_view ((hs:num->(A)rfs_history) a)) ((ts:num->real) a)
                               ((x:num->A) a)
                               (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                        ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                            D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)`
  (LABEL_TAC "BBA") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "BB" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B1"))))) THEN
    USE_THEN "RINF" (X_CHOOSE_TAC `N:num` o SPEC `D0:real`) THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `z:A`] THEN STRIP_TAC THEN
    USE_THEN "PA" (MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
    REMOVE_THEN "B1" (MP_TAC o SPECL
      [`hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `i:num`;
       `rs:num->real`; `ks:num->real`; `ds:num->real`; `(dlt:num->real) a`;
       `(rs':num->num->real) a`; `(ks':num->num->real) a`; `(dd:num->num->real) a`;
       `(hs:num->(A)rfs_history) a`; `(r:num->real) a`; `(ts:num->real) a`; `(x:num->A) a`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `N:num`)) (concl th))) THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "PA" (fun th -> REWRITE_TAC[th]);
    REPEAT GEN_TAC THEN MATCH_MP_TAC P2B_HS_SEP_SLICES THEN
    USE_THEN "PA" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "BAS" (fun th -> REWRITE_TAC[th]);
    USE_THEN "PA" (fun th -> REWRITE_TAC[th]);
    USE_THEN "PA" (fun th -> REWRITE_TAC[th])] THEN
  REWRITE_TAC[p3h_cexseq] THEN USE_THEN "INST" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[P3_T_POS] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `B:real` THEN USE_THEN "RINF" (MP_TAC o SPEC `B:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv((r:num->real) a pow 2)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "BAS" (fun th -> REWRITE_TAC[th])];
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "BBA" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `N:num`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MAP_EVERY X_GEN_TAC [`Ap:real`; `Dp:real`; `tp:real`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `max Ap (max Dp tp)` P3H_ARCH_LE1) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3H_171_CFG_MONO THEN
    MAP_EVERY EXISTS_TAC [`&a + &1`; `&a + &1`; `&a + &1`] THEN
    SUBGOAL_THEN `max Ap (max Dp tp) <= &a + &1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MAX_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "PA" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "BAS" (fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "BBA" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `N1:num`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))) THEN
    REMOVE_THEN "HF" (MP_TAC o SPECL [`A:real`; `D:real`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `dbar:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H1"))) THEN
    MP_TAC(SPEC `dbar:real` P3H_INV_SUC_SMALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    USE_THEN "PA" (MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[p3h_inst] THEN STRIP_TAC THEN
    REMOVE_THEN "H1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
      `(dlt:num->real) a`; `(rs':num->num->real) a`; `(ks':num->num->real) a`;
      `(dd:num->num->real) a`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "BAS" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&a + &1)` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "N2" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "N1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* ========================================================================= *)
(* Prop 17.1 (MT p. 395), the core: from Lemmas 17.2 and 17.7 (the canonv    *)
(* forms), Thm 10.2, the fresh-cap lemma, Lemma 11.2, Thm 11.8 (with its     *)
(* Cor 11.16 clause), Cor 9.95 (canonv) and regularity: by contradiction, a  *)
(* sequence of                                                               *)
(* counterexamples (S1), whose worst bad points would get canonical          *)
(* neighbourhoods by the T' argument (P3H_171_CEX_CANONV).                   *)
(* ========================================================================= *)

let P3H_PROP_17_1_CORE = prove
 (`!u:A->bool.
     P3_LEMMA_17_2_STATEMENT u /\ P3_LEMMA_17_7_STATEMENT u /\
     P2_THM_10_2_STATEMENT u /\ APX_SC_SPHERE_SEP_STATEMENT (:A) /\
     RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\
     P2_THM_12_32_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_PROP_12_31_STATEMENT /\
     P3_STD_C2_BOUND_STATEMENT /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2_LEMMA_11_2_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_THM_11_8_STATEMENT u (:real^3) /\ P2_COR_9_95_STATEMENT u (:real^3)
     ==> P3_PROP_17_1_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `P3_LEMMA_17_2_STATEMENT (u:A->bool)` THEN REWRITE_TAC[P3_LEMMA_17_2_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L172"))) THEN
  UNDISCH_TAC `P3_LEMMA_17_7_STATEMENT (u:A->bool)` THEN REWRITE_TAC[P3_LEMMA_17_7_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e7:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L177"))) THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_BALL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LBB"))) THEN
  MP_TAC P3H_171_HF_AT THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ef:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LHF"))) THEN
  MP_TAC(ISPEC `u:A->bool` P3H_171_CEX_CANONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ex:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LCX"))) THEN
  REWRITE_TAC[P3_PROP_17_1_STATEMENT] THEN
  EXISTS_TAC `min (min e2 e7) (min eb (min ef ex))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LE_MIN] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "L172" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L172"))) THEN
  REMOVE_THEN "L177" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C7:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L177"))) THEN
  REMOVE_THEN "LHF" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LHF"))) THEN
  REMOVE_THEN "LCX" (MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CX:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LCX"))) THEN
  MAP_EVERY EXISTS_TAC [`max (max C2 C7) (max CF (max CX (&2)))`; `&1`] THEN
  REWRITE_TAC[REAL_LT_01; REAL_MAX_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MAX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `hf:real->real->real`; `md:real->real`] THEN STRIP_TAC THEN
  REMOVE_THEN "L172" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L172") THEN
  REMOVE_THEN "L177" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L177") THEN
  REMOVE_THEN "LHF" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "LHF") THEN
  REMOVE_THEN "LBB" (MP_TAC o SPECL [`eps:real`; `C:real`]) THEN
  SUBGOAL_THEN `&1 < C /\ &2 <= C` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "LBB") THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
                       `kappa:real`; `dfun:real->real`] THEN
  STRIP_TAC THEN REFUTE_THEN(LABEL_TAC "NEG") THEN
  REMOVE_THEN "L172" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L172") THEN
  REMOVE_THEN "L177" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L177") THEN
  SUBGOAL_THEN `&0 < (rs:num->real) i` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_seq_upto i (rs:num->real)` THEN REWRITE_TAC[p3_seq_upto] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `kappa:real`; `dfun:real->real`] P3H_171_S1_ONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `kappa:real`] P3H_171_S1_SEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt:num->real` (X_CHOOSE_THEN `r:num->real`
    (X_CHOOSE_THEN `rs':num->num->real` (X_CHOOSE_THEN `ks':num->num->real`
    (X_CHOOSE_THEN `dd:num->num->real` (X_CHOOSE_THEN `hs:num->(A)rfs_history`
    (X_CHOOSE_THEN `ts:num->real` (X_CHOOSE_THEN `x:num->A` STRIP_ASSUME_TAC)))))))) THEN
  REMOVE_THEN "LCX" (MP_TAC o SPECL
    [`C:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`;
     `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `dlt:num->real`;
     `r:num->real`; `rs':num->num->real`; `ks':num->num->real`; `dd:num->num->real`;
     `hs:num->(A)rfs_history`; `ts:num->real`; `x:num->A`; `kappa:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canonv_at")) (concl th) &&
    is_neg(snd(dest_forall(concl th))))) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The route theorem: P3_PROP_17_1_ROUTE_STATEMENT at w = (:real^3) (the     *)
(* final composition instantiates P3_FULL_CHAIN at (:real^3)).               *)
(* ========================================================================= *)

let P3_PROP_17_1_ROUTE = prove
 (`!u:A->bool. P3_PROP_17_1_ROUTE_STATEMENT u (:real^3)`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_17_1_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3H_PROP_17_1_CORE THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APX_SC_SPHERE_SEP_STATEMENT; RFS_CUTCAP_SC_STATEMENT]) THEN
  ASM_REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT; RFS_CUTCAP_SC_STATEMENT]);;

