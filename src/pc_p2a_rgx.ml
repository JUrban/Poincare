(* ========================================================================= *)
(* pc_p2a_rgx: regularity of minimizers among curves with singular corners.  *)
(* A p2a_minx curve in a smooth view setting with locally constant slice     *)
(* atlases is a corner-free L-geodesic away from tau = 0, hence p2a_adm and  *)
(* a p2a_min minimizer (P2AXR_MINX_MIN).  The proof is that of pc_p2a_reg    *)
(* (MT Lemma 7.2 regularity), which uses the curve class only through the    *)
(* two-sided C^1 off the corner set, finite energy and competitors obtained  *)
(* by replacing short pieces: the lemmas are re-proved for                   *)
(* p2a_admx/p2a_minx, and the local C^1 of L-geodesics (P2A_LGEOD_LOCAL_C1)  *)
(* is re-proved pointwise, without the base point (no p2a_bsmooth needed).   *)
(*                                                                           *)
(* First: restriction and gluing of p2a_pc1x curves.                         *)
(* ========================================================================= *)

needs "src/pc_p2a_defs4.ml";;
needs "src/pc_p2a_reg.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AXR_PC1X_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) a b b' P.
     p2a_pc1x V tt gamma a b P /\ b' <= b ==> p2a_pc1x V tt gamma a b' P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1x] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G")) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T")) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "T" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Gluing gamma' on [0,b'] and gamma on [a,b] (a <= b') at b': b' becomes a  *)
(* corner, nothing is asked there.                                            *)

let P2AXR_GLUE_PC1X_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) gamma' gg a b b' P P'.
     p2a_pc1x V tt gamma a b P /\ p2a_pc1x V tt gamma' (&0) b' P' /\
     a <= b' /\ &0 < b' /\ b' < b /\
     (!tau. tau <= b' ==> gg tau = gamma' tau) /\
     (!tau. b' <= tau ==> gg tau = gamma tau)
     ==> p2a_pc1x V tt gg (&0) b (b' INSERT (P UNION P'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1x] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))
   (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G'"))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "E2"))))))) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s0 < b'` THENL
   [SUBGOAL_THEN `(gamma':real->A) s0 IN FST(c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) s0 = gamma' s0` (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "G'" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1"))) THEN
    MP_TAC(SPECL [`d1:real`; `(b' - s0) / &2`] REAL_DOWN2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "T1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma'(drop s)` SUBST_ALL_TAC THENL
      [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b' < s0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s0 IN FST(c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real->A) s0 = gamma s0` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1"))) THEN
  MP_TAC(SPECL [`d1:real`; `(s0 - b') / &2`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "T1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma(drop s)` SUBST_ALL_TAC THENL
    [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AXR_GLUE_PC1X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) gamma' gg b b' P P'.
     p2a_pc1x V tt gamma (&0) b P /\ p2a_pc1x V tt gamma' (&0) b' P' /\
     &0 < b' /\ b' < b /\
     (!tau. tau <= b' ==> gg tau = gamma' tau) /\
     (!tau. b' <= tau ==> gg tau = gamma tau)
     ==> p2a_pc1x V tt gg (&0) b (b' INSERT (P UNION P'))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AXR_GLUE_PC1X_GEN THEN
  MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`; `&0`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P2AXR_SEG_GLUE_PC1X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) gamma' gg b b' P P'.
     p2a_pc1x V tt gamma b' b P /\ p2a_pc1x V tt gamma' (&0) b' P' /\
     &0 < b' /\ b' < b /\
     (!tau. tau <= b' ==> gg tau = gamma' tau) /\
     (!tau. b' <= tau ==> gg tau = gamma tau)
     ==> p2a_pc1x V tt gg (&0) b (b' INSERT (P UNION P'))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AXR_GLUE_PC1X_GEN THEN
  MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`; `b':real`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Restriction, length splitting, gluing and piece replacement for p2a_admx  *)
(* curves, and the comparison of a p2a_minx curve with a C^1 chart curve on  *)
(* a short piece (copies of P2A_ADM_RESTRICT, P2A_LENGTH_SPLIT, P2A_GLUE,    *)
(* P2A_SEG_GLUE, P2A_REPLACE, P2A_MIN_CHART_PIECE).                          *)
(* ------------------------------------------------------------------------- *)

let P2AXR_ADMX_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x b b' (gamma:real->A).
        p2a_admx V tt x b gamma /\ &0 < b' /\ b' <= b
        ==> p2a_admx V tt x b' gamma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tau0:real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `P:real->bool` THEN MATCH_MP_TAC P2AXR_PC1X_RESTRICT THEN
    EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt (gamma:real->A) b`;
      `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt (gamma:real->A) b'`;
      `&0`; `b':real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `b':real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;
let P2AXR_LENGTH_SPLIT_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) b b'.
        p2a_admx V tt x b gamma /\ &0 < b' /\ b' <= b
        ==> p2a_L_length V tt gamma b =
            p2a_L_length V tt gamma b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_L_length] THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b'`;
    `&0`; `b':real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
let P2AXR_GLUE_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) gamma' gg b b'.
        p2a_admx V tt x b gamma /\ p2a_admx V tt x b' gamma' /\ b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_admx V tt x b gg /\
            p2a_L_length V tt gg b =
            p2a_L_length V tt gamma' b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_admx] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "E1")
    (LABEL_TAC "E2"))))) THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gg:real->A) b
      real_integrable_on real_interval[&0,b] /\
    p2a_L_length V tt gg b =
    p2a_L_length V tt gamma' b' +
    real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_GLUE_LINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS `(gamma':real->A)(&0)` THEN CONJ_TAC THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC P2A_GLUE_CONT THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`; `b':real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `b' INSERT ((P:real->bool) UNION P')` THEN
    MATCH_MP_TAC P2AXR_GLUE_PC1X THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;
let P2AXR_SEG_GLUE_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) gamma' gg b b'.
        p2a_admx V tt x b' gamma' /\ p2a_lseg V tt b' b gamma /\ gamma' b' = gamma b' /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_admx V tt x b gg /\
            p2a_L_length V tt gg b =
            p2a_L_length V tt gamma' b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_admx; p2a_lseg] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "E1")
    (LABEL_TAC "E2"))))) THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gg:real->A) b
      real_integrable_on real_interval[&0,b] /\
    p2a_L_length V tt gg b =
    p2a_L_length V tt gamma' b' +
    real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_SEG_GLUE_LINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    TRANS_TAC EQ_TRANS `(gamma':real->A)(&0)` THEN CONJ_TAC THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2A_SEG_GLUE_CONT THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`; `b':real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `b' INSERT ((P':real->bool) UNION P)` THEN
    MATCH_MP_TAC P2AXR_SEG_GLUE_PC1X THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`] THEN
    ASM_SIMP_TAC[P2AX_PC1_IMP];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;
let P2AXR_REPLACE_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) sig b b1 b2.
        p2a_admx V tt x b gamma /\ p2a_lseg V tt b1 b2 sig /\ b2 < b /\
        sig b1 = gamma b1 /\ sig b2 = gamma b2
        ==> p2a_admx V tt x b
              (\tau. if tau <= b1 then gamma tau else if tau <= b2 then sig tau
                     else gamma tau) /\
            p2a_L_length V tt
              (\tau. if tau <= b1 then gamma tau else if tau <= b2 then sig tau
                     else gamma tau) b =
            p2a_L_length V tt gamma b -
            real_integral (real_interval[b1,b2]) (p2a_L_integrand V tt gamma b) +
            real_integral (real_interval[b1,b2]) (p2a_L_integrand V tt sig b2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b1 /\ b1 < b2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_lseg]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `sig:real->A`; `gamma:real->A`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else sig tau`;
                 `b2:real`; `b1:real`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AXR_ADMX_RESTRICT THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau:real = b1` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else sig tau`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else if tau <= b2 then sig tau
                        else gamma tau`; `b:real`; `b2:real`] P2AXR_GLUE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(tau <= b1)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      (SUBGOAL_THEN `tau:real = b2` SUBST1_TAC THENL
        [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]])];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `b:real`;
                 `b1:real`] P2AXR_LENGTH_SPLIT_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gamma:real->A) b
      real_integrable_on real_interval[b1,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[p2a_admx]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt (gamma:real->A) b`;
                 `b1:real`; `b:real`; `b2:real`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;
let P2AXR_MINX_CHART_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) (sol:real^1->real^N) s1 s2 sa sb.
     p2a_svs V /\ p2a_minx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s2 /\ s2 pow 2 < b /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     (!s. s1 <= s /\ s <= s2
          ==> sol(lift s) IN IMAGE phi (U INTER W) /\
              sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s))) /\
     gamma(s1 pow 2) IN U INTER W /\ gamma(s2 pow 2) IN U INTER W /\
     sol(lift s1) = phi(gamma(s1 pow 2)) /\ sol(lift s2) = phi(gamma(s2 pow 2))
     ==> real_integral (real_interval[s1 pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b)
         <= p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt sol s1 s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`; `sol:real^1->real^N`; `s1:real`; `s2:real`;
                 `sa:real`; `sb:real`] P2A_CHART_CURVE_SEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N)
                                    ((sol:real^1->real^N)(lift(sqrt tau)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `s1 pow 2 < s2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sig:real->A)(s1 pow 2) = gamma(s1 pow 2) /\ sig(s2 pow 2) = gamma(s2 pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN
    SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2a_minx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_minx")) (concl th))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `sig:real->A`;
                 `b:real`; `s1 pow 2`; `s2 pow 2`] P2AXR_REPLACE_X) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau
                                   else if tau <= s2 pow 2 then (sig:real->A) tau
                                   else gamma tau` o CONJUNCT2 o REWRITE_RULE[p2a_minx] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "p2a_minx")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b <= s1 pow 2) /\ ~(b <= s2 pow 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_integral")) (concl th))) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The regularity of p2a_minx curves at interior times (copies of the        *)
(* pc_p2a_reg chain P2A_PC1_TAU_C1 ... P2A_MIN_LOC_END for p2a_pc1x,         *)
(* p2a_admx and p2a_minx).                                                   *)
(* ------------------------------------------------------------------------- *)

let P2AXR_PC1X_TAU_C1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b P tau1 e0 W a' b'' U (phi:A->real^N).
     p2a_pc1x V tt gamma (&0) b P /\ &0 < tau1 /\ tau1 < b /\ ~(tau1 IN P) /\
     &0 < e0 /\
     (!tau. abs(tau - tau1) < e0 ==> p2a_vatlas V (tt - tau) = p2a_vatlas V (tt - tau1)) /\
     (!O. open_in (p2a_vtop V (tt - tau1)) O /\ gamma tau1 IN O
          ==> ?d. &0 < d /\
                  !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau1) < d ==> gamma tau IN O) /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     a' < tt - tau1 /\ tt - tau1 <= b'' /\ gamma tau1 IN U INTER W
     ==> ?e. &0 < e /\
             (!tau. abs(tau - tau1) < e
                    ==> (\t. phi(gamma(drop t))) differentiable (at (lift tau))) /\
             (\t. vector_derivative (\t. phi(gamma(drop t))) (at t))
               continuous (at (lift tau1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `tt - tau1`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) tau1 IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - tau1))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                       (real->A->real^N^N)) (tt - tau1)) W`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - tau1)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - tau1)`;
                 `(gamma:real->A) tau1`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau1))
                   ((gamma:real->A) tau1)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - tau1)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - tau1)`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - tau1`; `c:(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `Oc = IMAGE (SND (c:(A->bool)#(A->real^N))) ((U INTER W) INTER FST c)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `Tr = chart_trans (c:(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - tau1))
                        ((U INTER W) INTER FST(c:(A->bool)#(A->real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b''`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b''`;
                   `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U INTER W) INTER FST(c:(A->bool)#(A->real^N))` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`tau1:real`; `c:(A->bool)#(A->real^N)`] o CONJUNCT2 o
    REWRITE_RULE[p2a_pc1x] o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2a_pc1x")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ABBREV_TAC `e = min (min d1 d2) (min e0 (min tau1 (b - tau1)))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= d1 /\ e <= d2 /\ e <= e0 /\ e <= tau1 /\ e <= b - tau1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^1. t IN ball(lift tau1,e)
               ==> &0 < drop t /\ drop t < b /\
                   (gamma:real->A)(drop t) IN (U INTER W) INTER FST(c:(A->bool)#(A->real^N)) /\
                   p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) (tt - drop t) =
                   p2a_vatlas V (tt - tau1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ball(lift tau1,e)` o
             MATCH_MP (REWRITE_RULE[IMP_CONJ] P2A_CD1_OPEN)) THEN
  REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `(t:real^1) IN ball(lift tau1,e)` THEN
    REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN (ASM_REAL_ARITH_TAC ORELSE ASM SET_TAC[]);
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!y:real^1. y IN ball(lift tau1,e)
               ==> ((Tr:real^N->real^N) o (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))) y =
                   (\t. (phi:A->real^N)(gamma(drop t))) y /\
                   SND c (gamma(drop y)) IN Oc`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th) &&
      can (find_term ((=) `b:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXPAND_TAC "Tr" THEN EXPAND_TAC "Oc" THEN REWRITE_TAC[o_THM; chart_trans; SND] THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^1. y IN ball(lift tau1,e)
               ==> ((\t. (phi:A->real^N)((gamma:real->A)(drop t))) has_vector_derivative
                    frechet_derivative (Tr:real^N->real^N) (at (SND (c:(A->bool)#(A->real^N)) (gamma(drop y))))
                      (vector_derivative (\s. SND c (gamma(drop s))) (at y))) (at y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`(Tr:real^N->real^N) o (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))`;
      `ball(lift tau1,e)`] THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`Tr:real^N->real^N`; `Oc:real^N->bool`;
                   `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`; `y:real^1`]
                  P2A_CHAIN_SMOOTH_VD) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN
    EXISTS_TAC `frechet_derivative (Tr:real^N->real^N) (at (SND (c:(A->bool)#(A->real^N))
                  ((gamma:real->A)(drop(lift tau)))))
                  (vector_derivative (\s. SND c (gamma(drop s))) (at (lift tau)))` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`\y:real^1. frechet_derivative (Tr:real^N->real^N) (at (SND (c:(A->bool)#(A->real^N))
                  ((gamma:real->A)(drop y))))
                  (vector_derivative (\s. SND c (gamma(drop s))) (at y))`;
    `ball(lift tau1,e)`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_FRECHET_COMPOSE_CONT THEN EXISTS_TAC `Oc:real^N->bool` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN EXPAND_TAC "Oc" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_on")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL]);;
let P2AXR_ADMX_SCONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A).
     p2a_admx V tt x b gamma
     ==> !s O. &0 <= s /\ s pow 2 <= b /\ open_in (p2a_vtop V (tt - s pow 2)) O /\
               gamma(s pow 2) IN O
               ==> ?e. &0 < e /\
                       !r. &0 <= r /\ r pow 2 <= b /\ abs(r - s) < e ==> gamma(r pow 2) IN O`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `O:A->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s pow 2`; `O:A->bool`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  SUBGOAL_THEN `(\x:real. x pow 2) real_continuous atreal s` MP_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN REWRITE_TAC[REAL_CONTINUOUS_AT_ID]; ALL_TAC] THEN
  REWRITE_TAC[real_continuous_atreal] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  USE_THEN "D" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LE_POW_2]);;
let P2AXR_MINX_ODE_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) p q sa sb K M.
     p2a_svs V /\ p2a_minx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < p /\ p < q /\ q pow 2 < b /\ sa < p /\ q < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     (!s. p <= s /\ s <= q ==> gamma(s pow 2) IN U INTER W) /\
     FINITE K /\
     (!s. p < s /\ s < q /\ ~(s IN K)
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift s)) /\
              norm(vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))) <= M)
     ==> !s. p < s /\ s < q
             ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative
                  vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s)))
                 (at (lift s)) /\
                 ((\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                  has_vector_derivative
                  p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt s
                           (phi(gamma(s pow 2)))
                           (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))))
                 (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2a_minx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_minx")) (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AXR_ADMX_SCONT) THEN
  SUBGOAL_THEN `!s. p <= s /\ s <= q
                    ==> (gamma:real->A)(s pow 2) IN U INTER W /\
                        a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a < x /\ x < b ==> a < x /\ x <= b`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift p,lift q]` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_ADM_CHART_CONT THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `tt:real`; `b:real`; `W:A->bool`;
                          `a':real`; `b'':real`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`] P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Y = \v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `Gt = p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (* the local boundary value problem on [p,q] *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `a':real`; `b'':real`;
                 `Gt:real->real^N->real^N^N`; `tt:real`;
                 `IMAGE (Y:real^1->real^N) (interval[lift p,lift q])`;
                 `(q - p) * abs M pow 2 + &1`; `p:real`; `q:real`] P2A_LOC_BVP_PW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `q:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `sol0:real->real->real^N->real^N->real^1->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "BVP") (K ALL_TAC))))))) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:real^1->real^N`; `p:real`; `q:real`; `s:real`; `delta:real`; `rho:real`]
                P2A_SHORT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "BVP" (MP_TAC o SPECL [`s1:real`; `s2:real`; `(Y:real^1->real^N)(lift s1)`;
                                     `(Y:real^1->real^N)(lift s2)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `sol = (sol0:real->real->real^N->real^N->real^1->real^N) s1 s2
                    ((Y:real^1->real^N)(lift s1)) (Y(lift s2))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "E1") (CONJUNCTS_THEN2 (LABEL_TAC "E2")
    (CONJUNCTS_THEN2 (LABEL_TAC "SOLU") (CONJUNCTS_THEN2 (LABEL_TAC "SOLD")
      (LABEL_TAC "SOLMIN"))))) THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < s2 /\ s2 pow 2 < b /\ sa < s1 /\ s2 < sb` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `q pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift p,lift q]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s1 pow 2) IN U INTER W /\ gamma(s2 pow 2) IN U INTER W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sol:real^1->real^N)(lift s1) = (phi:A->real^N)((gamma:real->A)(s1 pow 2)) /\
                sol(lift s2) = phi(gamma(s2 pow 2))` STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "E1" SUBST1_TAC THEN REMOVE_THEN "E2" SUBST1_TAC THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP];
    REMOVE_THEN "E1" (K ALL_TAC) THEN REMOVE_THEN "E2" (K ALL_TAC)] THEN
  SUBGOAL_THEN
   `!r. s1 <= r /\ r <= s2
        ==> (sol:real^1->real^N)(lift r) IN IMAGE (phi:A->real^N) (U INTER W) /\
            sol differentiable (at (lift r)) /\
            (\v. vector_derivative sol (at v)) continuous (at (lift r))`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "SOLD" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "SOLU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* Y is a competitor for the boundary value problem *)
  REMOVE_THEN "SOLMIN" (MP_TAC o SPECL [`Y:real^1->real^N`; `K:real->bool`; `abs M`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `M:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s2 - s1) * abs M pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2A_ENERGY_PW_BOUND THEN EXISTS_TAC `K:real->bool` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `M:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC]];
    STRIP_TAC] THEN
  (* the L-length of the piece of gamma *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                 `s1:real`; `s2:real`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `K:real->bool`; `sa:real`; `sb:real`; `M:real`]
                P2A_LINT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a < x /\ x < b ==> a < x /\ x <= b`) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `O:A->bool`] THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s2 pow 2` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE)] THEN
  (* the solution is a competitor for the minimizer *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `sol:real^1->real^N`; `s1:real`; `s2:real`; `sa:real`; `sb:real`]
                P2AXR_MINX_CHART_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `!r. s1 <= r /\ r <= s2
                    ==> (Y:real^1->real^N)(lift r) = (sol:real^1->real^N)(lift r)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term ((=) `Y:real^1->real^N`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* conclusion at s *)
  USE_THEN "SOLD" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`Y:real^1->real^N`; `sol:real^1->real^N`; `s1:real`; `s2:real`; `s:real`]
                P2A_VDERIV_AGREE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop(v:real^1)` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sol:real^1->real^N`)) (concl th) &&
        can (find_term ((=) `Y:real^1->real^N`)) (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A)(s pow 2)) = (sol:real^1->real^N)(lift s)`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `(Y:real^1->real^N)(lift s)` THEN CONJ_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\v. vector_derivative (sol:real^1->real^N) (at v)`;
                        `min (s - s1) (s2 - s)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`Y:real^1->real^N`; `sol:real^1->real^N`; `s1:real`; `s2:real`; `drop(v:real^1)`]
                P2A_VDERIV_AGREE) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `drop(w:real^1)` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sol:real^1->real^N`)) (concl th) &&
        can (find_term ((=) `Y:real^1->real^N`)) (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "SOLD" (MP_TAC o SPEC `drop(v:real^1)`) THEN REWRITE_TAC[LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN MESON_TAC[]];
    SIMP_TAC[]]);;
let P2AXR_MINX_ODE_OPEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) p0 q0.
     p2a_svs V /\ p2a_minx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 <= p0 /\ p0 < q0 /\ q0 pow 2 <= b /\
     (!s. p0 < s /\ s < q0
          ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'' /\ gamma(s pow 2) IN U INTER W /\
              (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift s)))
     ==> !s. p0 < s /\ s < q0
             ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative
                  vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s)))
                 (at (lift s)) /\
                 ((\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                  has_vector_derivative
                  p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt s
                           (phi(gamma(s pow 2)))
                           (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))))
                 (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\v. vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (at v))
    continuous_on interval[lift((p0 + s) / &2),lift((s + q0) / &2)]`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `b'':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC o BETA_RULE o MATCH_MP P2A_CONT_BOUNDED) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `(p0 + s) / &2`; `(s + q0) / &2`; `p0:real`; `q0:real`; `{}:real->bool`;
                 `M:real`] P2AXR_MINX_ODE_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `q0 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b'':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b'':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b'':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;
let P2AXR_MINX_ENERGY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) p q sa sb.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 <= p /\ p < q /\ q pow 2 <= b /\ sa < p /\ q < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'') /\
     (!s. p <= s /\ s <= q ==> gamma(s pow 2) IN U INTER W) /\
     (!s. p < s /\ s < q
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative
               vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s)))
              (at (lift s)) /\
              ((\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
               has_vector_derivative
               p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt s
                        (phi(gamma(s pow 2)))
                        (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))))
              (at (lift s)))
     ==> (\s. norm(vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))) pow 2)
         real_integrable_on real_interval[p,q]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AXR_ADMX_SCONT) THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. p <= s /\ s <= q
                    ==> (gamma:real->A)(s pow 2) IN U INTER W /\
                        a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift p,lift q]` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_ADM_CHART_CONT THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `tt:real`; `b:real`; `W:A->bool`;
                          `a':real`; `b'':real`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) sa sb
                 (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Y = \v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `Gt = p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!s. p <= s /\ s <= q
                    ==> (Y:real^1->real^N)(lift s) IN IMAGE (phi:A->real^N) (U INTER W)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Fs = \s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                                (vector_derivative Y (at (lift s)))` THEN
  (* the pointwise identity *)
  SUBGOAL_THEN `!s. p < s /\ s < q
                    ==> &2 * s * p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b (s pow 2) =
                        (Fs:real->real) s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `b'':real`)) (concl th) &&
      can (find_term ((=) `q:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `vector_derivative (Y:real^1->real^N) (at (lift s))`] P2A_LINT_REGION) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "Fs" THEN EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  (* continuity of Fs on (p,q) *)
  SUBGOAL_THEN `!s. p < s /\ s < q ==> (Fs:real->real) real_continuous atreal s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "Fs" THEN
    MATCH_MP_TAC P2A_LLAG_CONT_AT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb:real`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* continuity of the L-integrand at tau = s^2 *)
  SUBGOAL_THEN `!s. p < s /\ s < q
                    ==> p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b real_continuous
                        (atreal (s pow 2)) within real_interval[p pow 2,q pow 2]`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\t. (Fs:real->real)(sqrt t) * inv(&2 * sqrt t)` THEN
    SUBGOAL_THEN `p pow 2 < s pow 2 /\ s pow 2 < q pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `min (s pow 2 - p pow 2) (q pow 2 - s pow 2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `p pow 2 < t /\ t < q pow 2` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= p pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < t /\ p < sqrt t /\ sqrt t < q /\ sqrt t pow 2 = t /\ &0 < sqrt t`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(p pow 2)` THEN CONJ_TAC THENL
           [ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL];
            MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[]];
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(q pow 2)` THEN CONJ_TAC THENL
           [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `sqrt t` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_L_integrand")) (concl th) &&
        can (find_term ((=) `Fs:real->real`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "real_continuous"))
               (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `&0 < sqrt t` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\t. (Fs:real->real)(sqrt t)) = Fs o sqrt` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN
      REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT] THEN
      SUBGOAL_THEN `sqrt(s pow 2) = s` SUBST1_TAC THENL
       [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_INV_ATREAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT];
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `sqrt(s pow 2) = s` SUBST1_TAC THENL
         [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  (* the substitution tau = s^2 *)
  SUBGOAL_THEN `p pow 2 <= q pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b`; `\s:real. s pow 2`;
                 `\s:real. &2 * s`; `p:real`; `q:real`; `p pow 2`; `q pow 2`;
                 `{p:real,q}`] HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_INSERT; FINITE_EMPTY]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real` THEN
      REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(ISPECL [`\x:real. x`; `&1`; `y:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN REWRITE_TAC[REAL_POW_1; REAL_MUL_RID];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Fs:real->real) real_integrable_on real_interval[p,q]` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SPIKE THEN
    EXISTS_TAC `{p:real,q}` THEN
    SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_L_integrand")) (concl th) &&
      can (find_term ((=) `Fs:real->real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "real_continuous"))
             (concl th)))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scalar curvature term *)
  SUBGOAL_THEN `(\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                              (vec 0)) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb:real`;
                   `Gt:real->real^N->real^N^N`; `tt:real`; `Y:real^1->real^N`;
                   `\v:real^1. vec 0:real^N`; `p:real`; `q:real`]
                  P2A_LLAG_CURVE_CONTINUOUS) THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  (* the lower bound of the metrics along the chart curve *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb:real`;
                 `Gt:real->real^N->real^N^N`; `tt:real`;
                 `IMAGE (Y:real^1->real^N) (interval[lift p,lift q])`; `p:real`; `q:real`]
                P2A_UNIFORM_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real`
    (X_CHOOSE_THEN `BR:real` STRIP_ASSUME_TAC)))) THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\s. &2 / lam * ((Fs:real->real) s -
                  p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s)) (vec 0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_measurable_on; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[ARITH_EQ] THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN
    MATCH_MP_TAC P2A_PW_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `{}:real->bool`] THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN EXPAND_TAC "Fs" THEN
  REWRITE_TAC[p2a_llag] THEN MATCH_MP_TAC P2A_ENERGY_ARITH THEN
  ASM_REWRITE_TAC[DOT_LZERO] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `(Y:real^1->real^N)(lift s)`;
    `(Y:real^1->real^N)(lift s)`; `vector_derivative (Y:real^1->real^N) (at (lift s))`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `lam:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_REFL; SING_SUBSET] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;
let P2AXR_MINX_EXTEND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) p q sa sb.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 <= p /\ p < q /\ q pow 2 <= b /\ sa < p /\ q < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'') /\
     (!s. p <= s /\ s <= q ==> gamma(s pow 2) IN U INTER W) /\
     (!s. p < s /\ s < q
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative
               vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s)))
              (at (lift s)) /\
              ((\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
               has_vector_derivative
               p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt s
                        (phi(gamma(s pow 2)))
                        (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))))
              (at (lift s)))
     ==> ?A'. (!s. p < s /\ s < q
                   ==> A'(lift s) =
                       vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))) /\
              A' continuous_on interval[lift p,lift q] /\
              (!s. p <= s /\ s <= q
                   ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A'(lift s))
                         (at (lift s) within interval[lift p,lift q]) /\
                       (A' has_vector_derivative
                          p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt s
                                   (phi(gamma(s pow 2))) (A'(lift s)))
                         (at (lift s) within interval[lift p,lift q]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `p:real`; `q:real`; `sa:real`; `sb:real`] P2AXR_MINX_ENERGY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AXR_ADMX_SCONT) THEN
  SUBGOAL_THEN `!s. p <= s /\ s <= q
                    ==> (gamma:real->A)(s pow 2) IN U INTER W /\
                        a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift p,lift q]` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_ADM_CHART_CONT THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `tt:real`; `b:real`; `W:A->bool`;
                          `a':real`; `b'':real`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) sa sb
                 (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb:real`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `p:real`; `q:real`;
                 `IMAGE (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                        (interval[lift p,lift q])`;
                 `\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                 `\v. vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                        (at v)`] P2A_LODE_EXTEND) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `lift s` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;
let P2AXR_MINX_PUNCT_C1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) s0.
     p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 <= s0 /\ s0 pow 2 <= b /\ gamma(s0 pow 2) IN U INTER W /\
     a' < tt - s0 pow 2 /\ (tt - s0 pow 2 < b'' \/ (s0 = &0 /\ b'' = tt))
     ==> ?h. &0 < h /\
             (!s. abs(s - s0) < h
                  ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'' /\
                      (~(s = &0) ==> tt - s pow 2 < b'')) /\
             (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < h
                  ==> gamma(s pow 2) IN U INTER W) /\
             (!s. &0 < s /\ s pow 2 < b /\ ~(s = s0) /\ abs(s - s0) < h
                  ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
                      (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                        continuous (at (lift s)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WIN"))))))))) THEN
  (* the time window near s0 *)
  SUBGOAL_THEN
   `?h0. &0 < h0 /\
         !s. abs(s - s0) < h0
             ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'' /\
                 (~(s = &0) ==> tt - s pow 2 < b'')`
  STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "WIN" DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [`s0:real`; `min (tt - s0 pow 2 - a') (b'' - (tt - s0 pow 2))`]
                   P2A_SQ_NEAR) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h0:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      MP_TAC(SPECL [`&0`; `tt - &0 pow 2 - a'`] P2A_SQ_NEAR) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h0:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_LT_POW_2] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `h0:real`)) (concl th))) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2a_admx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
  (* gamma stays in U INTER W near s0^2 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `b'':real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `tt - s0 pow 2`;
                 `U INTER W:A->bool`] P2A_REGION_OPEN_BACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b''`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b''`;
                   `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[FST];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s0 pow 2`; `U INTER W:A->bool`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  (* the slice atlas near tt - s0^2 *)
  FIRST_ASSUM(MP_TAC o SPEC `tt - s0 pow 2` o REWRITE_RULE[p2a_atlas_lc] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_atlas_lc")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "AL") (LABEL_TAC "AR")))) THEN
  (* the corners away from s0^2 *)
  MP_TAC(ISPECL [`s0 pow 2`; `P:real->bool`] P2A_REAL_FINITE_AVOID) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p2a_pc1x]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DP"))) THEN
  MP_TAC(SPECL [`s0:real`; `min d1 (min dl dP)`] P2A_SQ_NEAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H1"))) THEN
  EXISTS_TAC `min h0 h1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `h0:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "D1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    USE_THEN "H1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "H1" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `h0:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ ~(s pow 2 = s0 pow 2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(s:real = s0)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN U INTER W` ASSUME_TAC THENL
   [USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                 `P:real->bool`; `s pow 2`;
                 `min (abs(s pow 2 - s0 pow 2)) (dl - abs(s pow 2 - s0 pow 2))`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`]
                P2AXR_PC1X_TAU_C1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN USE_THEN "DP" (MP_TAC o SPEC `s pow 2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN ASM_CASES_TAC `s0 pow 2 < s pow 2` THENL
       [USE_THEN "AL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "AR" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\t:real^1. (phi:A->real^N)((gamma:real->A)(drop t))`; `s:real`; `e:real`]
                P2A_SQ_CURVE_C1) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;
let P2AXR_MINX_LOC_INT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) s0.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_minx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s0 /\ s0 pow 2 < b /\ gamma(s0 pow 2) IN U INTER W /\
     a' < tt - s0 pow 2 /\ tt - s0 pow 2 < b''
     ==> ?d A. &0 < d /\
               (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < d
                    ==> gamma(s pow 2) IN U INTER W /\ a' < tt - s pow 2 /\
                        tt - s pow 2 <= b'') /\
               (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d
                    ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A u)
                          (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                        (A has_vector_derivative
                           p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt (drop u)
                                    (phi(gamma(drop u pow 2))) (A u))
                          (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2a_minx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_minx")) (concl th))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `s0:real`]
                P2AXR_MINX_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HW") (CONJUNCTS_THEN2 (LABEL_TAC "HU") (LABEL_TAC "HC"))))) THEN
  SUBGOAL_THEN `&0 < b /\ s0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
     [MP_TAC(SPEC `s0:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k = min h (min s0 (sqrt b - s0)) / &3` THEN
  SUBGOAL_THEN `&0 < k /\ &3 * k <= h /\ &3 * k <= s0 /\ &3 * k <= sqrt b - s0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < &2 * k
        ==> &0 < s /\ s pow 2 < b /\ a' < tt - s pow 2 /\ tt - s pow 2 < b'' /\
            tt - s pow 2 <= b'' /\ (gamma:real->A)(s pow 2) IN U INTER W /\
            (~(s = s0)
             ==> (\v. (phi:A->real^N)(gamma(drop v pow 2))) differentiable (at (lift s)) /\
                 (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                   continuous (at (lift s)))`
  (LABEL_TAC "K2") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < s /\ s pow 2 < b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    USE_THEN "HW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "HU" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN USE_THEN "HC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - &2 * k < s /\ s < s0 + &2 * k
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - &2 * k < s /\ s < s0 + &2 * k
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 < b''`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!s. s0 - k <= s /\ s <= s0 ==> (gamma:real->A)(s pow 2) IN U INTER W) /\
                (!s. s0 <= s /\ s <= s0 + k ==> gamma(s pow 2) IN U INTER W) /\
                (!s. s0 - k <= s /\ s <= s0 + k ==> gamma(s pow 2) IN U INTER W)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `s:real`) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(s0 + k) pow 2 < b` ASSUME_TAC THENL
   [USE_THEN "K2" (MP_TAC o SPEC `s0 + k`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the system on both punctured sides *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - k`; `s0:real`] P2AXR_MINX_ODE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN P2A_ARITH_CONJS_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "OL")] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `s0 + k`] P2AXR_MINX_ODE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN P2A_ARITH_CONJS_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "OR")] THEN
  (* the one-sided extensions to s0 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - k`; `s0:real`; `s0 - &2 * k`; `s0 + &2 * k`] P2AXR_MINX_EXTEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Al:real^1->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "AL1")
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `s0 + k`; `s0 - &2 * k`; `s0 + &2 * k`] P2AXR_MINX_EXTEND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ar:real^1->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "AR1")
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`Al:real^1->real^N`; `s0 - k`; `s0:real`] P2A_CONT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ml:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "ML"))) THEN
  MP_TAC(ISPECL [`Ar:real^1->real^N`; `s0:real`; `s0 + k`] P2A_CONT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Mr:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "MR"))) THEN
  (* the boundary value problem across s0 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - k`; `s0 + k`; `s0 - &2 * k`; `s0 + &2 * k`; `{s0:real}`; `Ml + Mr`]
                P2AXR_MINX_ODE_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_SING] THEN P2A_ARITH_CONJS_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s < s0` THENL
     [USE_THEN "AL1" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      USE_THEN "ML" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      USE_THEN "AR1" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      USE_THEN "MR" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    DISCH_THEN(LABEL_TAC "OD")] THEN
  EXISTS_TAC `k:real` THEN
  EXISTS_TAC `\v. vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (at v)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    USE_THEN "OD" (MP_TAC o SPEC `drop(u:real^1)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[]]);;
let P2AXR_MINX_LOC_END = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) s0.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_minx V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s0 /\ s0 pow 2 = b /\ gamma(s0 pow 2) IN U INTER W /\
     a' < tt - s0 pow 2 /\ tt - s0 pow 2 < b''
     ==> ?d A. &0 < d /\
               (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < d
                    ==> gamma(s pow 2) IN U INTER W /\ a' < tt - s pow 2 /\
                        tt - s pow 2 <= b'') /\
               (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d
                    ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A u)
                          (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                        (A has_vector_derivative
                           p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt (drop u)
                                    (phi(gamma(drop u pow 2))) (A u))
                          (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2a_minx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_minx")) (concl th))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `s0:real`]
                P2AXR_MINX_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HW") (CONJUNCTS_THEN2 (LABEL_TAC "HU") (LABEL_TAC "HC"))))) THEN
  ABBREV_TAC `k = min h s0 / &3` THEN
  SUBGOAL_THEN `&0 < k /\ &3 * k <= h /\ &3 * k <= s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < s0 ==> s pow 2 < b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - &2 * k < s /\ s < s0 + &2 * k
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "HW" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - k <= s /\ s <= s0 ==> (gamma:real->A)(s pow 2) IN U INTER W`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "HU" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - k`; `s0:real`] P2AXR_MINX_ODE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN P2A_ARITH_CONJS_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < b` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "HW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "HC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - k`; `s0:real`; `s0 - &2 * k`; `s0 + &2 * k`] P2AXR_MINX_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Al:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AL3")))) THEN
  EXISTS_TAC `k:real` THEN EXISTS_TAC `Al:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "HU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `drop(u:real^1) <= s0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "AL3" (MP_TAC o SPEC `drop(u:real^1)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC P2A_HVD_DOMAIN_LEFT THEN
  MAP_EVERY EXISTS_TAC [`s0:real`; `k:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* L-geodesics pointwise.  p2axr_lgeod_at V tt gamma b s0 is the local       *)
(* condition of p2a_Lgeod at the single time s0 (s = sqrt tau);              *)
(* P2A_LGEOD_CONT, P2A_LGEOD_PIECE, P2A_LGEOD_CHART_UNIQUE and               *)
(* P2A_LGEOD_LOCAL_C1 use p2a_Lgeod only through that condition, and are     *)
(* re-proved from it (the last one from the condition at all s0 > 0, which   *)
(* does not involve the base point).                                         *)
(* ------------------------------------------------------------------------- *)

let p2axr_lgeod_at = new_definition
 `p2axr_lgeod_at (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) (tt:real) (gamma:real->A) (b:real) (s0:real) <=>
    ?W a' b' c d (A:real^1->real^N).
       p2a_region V W a' b' /\
       c IN restrict_atlas (p2a_vatlas V b') W /\ &0 < d /\
       (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < d
            ==> gamma(s pow 2) IN FST c /\
                a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
       (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d
            ==> ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative A u)
                  (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                (A has_vector_derivative
                   p2a_lacc (p2a_rlocal V W b' c) tt (drop u)
                            (SND c (gamma(drop u pow 2))) (A u))
                  (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}))`;;

let P2AXR_LGEOD_CONT_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s0 O.
     p2axr_lgeod_at V tt gamma b s0 /\ &0 <= s0 /\ s0 pow 2 <= b /\
     open_in (p2a_vtop V (tt - s0 pow 2)) O /\ gamma(s0 pow 2) IN O
     ==> ?e. &0 < e /\
             !s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < e ==> gamma(s pow 2) IN O`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2axr_lgeod_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN `d:real`
    (X_CHOOSE_THEN `Av:real^1->real^N` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `(gamma:real->A)(s0 pow 2) IN FST(c:(A->bool)#(A->real^N)) /\
                a' < tt - s0 pow 2 /\ tt - s0 pow 2 <= b'`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
      can (term_match [] `!s. P s ==> (gamma:real->A)(s pow 2) IN FST(c:(A->bool)#(A->real^N)) /\ Q s`)
          (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  UNDISCH_TAC `(c:(A->bool)#(A->real^N)) IN
               restrict_atlas (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') W` THEN
  SUBST1_TAC(SYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `phi = SND(c:(A->bool)#(A->real^N))` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `tt - s0 pow 2`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `tt - s0 pow 2`; `O:A->bool`] P2A_REGION_OPEN_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER (W INTER O)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) b'` THEN
    EXISTS_TAC `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) b'` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. (phi:A->real^N) ((gamma:real->A)(drop v pow 2))) continuous
    (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % (Av:real^1->real^N) (lift s0)` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u")) THEN
    EXPAND_TAC "phi" THEN ASM_SIMP_TAC[LIFT_DROP; REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(phi:A->real^N)((gamma:real->A)(s0 pow 2))` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gamma:real->A)(s0 pow 2)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_within] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 d` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
  ASM_REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A)(s pow 2)) IN IMAGE phi (U INTER (W INTER O))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN FST(c:(A->bool)#(A->real^N))` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      can (term_match [] `!s. P s ==> (gamma:real->A)(s pow 2) IN FST(c:(A->bool)#(A->real^N)) /\ Q s`)
          (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b'`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `z:A` th) THEN MP_TAC(SPEC `(gamma:real->A)(s pow 2)` th)) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[]);;

let P2AXR_LGEOD_PIECE_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s0.
     p2axr_lgeod_at V tt gamma b s0 /\ &0 <= s0 /\ s0 pow 2 <= b
     ==> ?W a' b' U (phi:A->real^N) d (A:real^1->real^N).
           p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\ &0 < d /\
           p2a_lsmooth (IMAGE phi (U INTER W)) (s0 - d) (s0 + d)
                       (\s. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) /\
           (!s. abs(s - s0) < d ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
           (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < d
                ==> gamma(s pow 2) IN U INTER W) /\
           (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d
                ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A u)
                      (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                    (A has_vector_derivative
                       p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt (drop u)
                                (phi(gamma(drop u pow 2))) (A u))
                      (at u within {v | &0 <= drop v /\ drop v pow 2 <= b})) /\
           ode_solution (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
             (interval(lift(s0 - d),lift(s0 + d)) PCROSS
              (IMAGE phi (U INTER W) PCROSS (:real^N)))
             {u | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d}
             (\u. pastecart (phi(gamma(drop u pow 2))) (A u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2axr_lgeod_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN `d0:real`
    (X_CHOOSE_THEN `A:real^1->real^N` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `?U (phi:A->real^N).
                  (U,phi) IN p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b' /\
                  c = (U INTER W,phi)`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THENL
   [UNDISCH_TAC `(c:(A->bool)#(A->real^N)) IN
                 restrict_atlas (p2a_vatlas (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') W` THEN
    SUBST1_TAC(SYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
    REWRITE_TAC[IN_RESTRICT_ATLAS; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  (* the time window *)
  SUBGOAL_THEN `?e0. &0 < e0 /\
                     !s. abs(s - s0) < e0 ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_TIME_WINDOW THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a' < tt - s0 pow 2 /\ tt - s0 pow 2 <= b'` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
        is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s")) THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s0 - min d0 s0 / &2` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s")) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s0 pow 2` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `tt - (s0 - min d0 s0 / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x < y ==> tt - y < tt - x`) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = min d0 e0` THEN
  SUBGOAL_THEN `&0 < d /\ d <= d0 /\ d <= e0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                        `d:real`; `A:real^1->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the s-family *)
    MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b') W`;
      `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b') W`;
      `a':real`; `b':real`; `p2a_rmetric (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'`;
      `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `s0 - d`; `s0 + d`]
     P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) W a' b'` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s" &&
      can (find_term (fun t -> t = `FST(c:(A->bool)#(A->real^N))`)) (concl th) = false &&
      can (find_term (fun t -> t = `U INTER W:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[P2A_LSOL_ODE; P2A_SWIN_INTERVAL] THEN
  X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop u` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s" &&
      can (find_term (fun t -> t = `U INTER W:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
    is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]);;

let P2AXR_LGEOD_CHART_UNIQUE_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s0 W1 a1 b1 U1 (phi1:A->real^N) sa sb (Y1:real^1->real^N) A1 J1 r.
     p2axr_lgeod_at V tt gamma b s0 /\ &0 < b /\ &0 <= s0 /\ s0 pow 2 <= b /\
     p2a_region V W1 a1 b1 /\ (U1,phi1) IN p2a_vatlas V b1 /\
     sa < s0 /\ s0 < sb /\
     (!s. sa < s /\ s < sb ==> a1 < tt - s pow 2 /\ tt - s pow 2 <= b1) /\
     ode_solution (p2a_lfield (p2a_rlocal V W1 b1 (U1 INTER W1,phi1)) tt)
       (interval(lift sa,lift sb) PCROSS (IMAGE phi1 (U1 INTER W1) PCROSS (:real^N))) J1
       (\u. pastecart (Y1 u) (A1 u)) /\
     &0 < r /\
     (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < r ==> u IN J1) /\
     gamma(s0 pow 2) IN U1 INTER W1 /\ Y1(lift s0) = phi1(gamma(s0 pow 2)) /\
     ((\v. phi1(gamma(drop v pow 2))) has_vector_derivative A1(lift s0))
       (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> ?e. &0 < e /\
             !s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < e
                 ==> phi1(gamma(s pow 2)) = Y1(lift s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`]
                P2AXR_LGEOD_PIECE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W2:A->bool` (X_CHOOSE_THEN `a2:real` (X_CHOOSE_THEN `b2:real`
    (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N` (X_CHOOSE_THEN `d2:real`
    (X_CHOOSE_THEN `A2:real^1->real^N` STRIP_ASSUME_TAC))))))) THEN
  ABBREV_TAC `t0 = tt - s0 pow 2` THEN
  ABBREV_TAC `p = (gamma:real->A)(s0 pow 2)` THEN
  SUBGOAL_THEN `a1 < t0 /\ t0 <= b1 /\ a2 < t0 /\ t0 <= b2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN U2 INTER W2` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) t0) (U1 INTER W1) /\
    open_in (p2a_vtop V t0) (U2 INTER W2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_OPEN_BACK THENL
     [MAP_EVERY EXISTS_TAC [`W1:A->bool`; `a1:real`; `b1:real`];
      MAP_EVERY EXISTS_TAC [`W2:A->bool`; `a2:real`; `b2:real`]] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b1`;
                     `(U1:A->bool,phi1:A->real^N)`] MFDM_CHART);
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b2`;
                     `(U2:A->bool,phi2:A->real^N)`] MFDM_CHART)] THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  ABBREV_TAC `O = (U1 INTER W1) INTER (U2 INTER W2):A->bool` THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) t0) (O:A->bool) /\ (p:A) IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`;
                 `O:A->bool`] P2AXR_LGEOD_CONT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (min d2 e2) (min r (min (s0 - sa) (sb - s0)))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= d2 /\ e <= e2 /\ e <= r /\ e <= s0 - sa /\ e <= sb - s0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) (U1 INTER W1,phi1)` THEN
  SUBGOAL_THEN `!q:A. q IN U1 INTER W1 /\ q IN U2 INTER W2 ==> (h:real^N->real^N)(phi2 q) = phi1 q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans; SND] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b2`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                   `U2:A->bool`; `phi2:A->real^N`; `W2:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = {u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < e}` THEN
  SUBGOAL_THEN `is_interval (J:real^1->bool) /\
                J SUBSET {v | &0 <= drop v /\ drop v pow 2 <= b} /\ lift s0 IN J /\
                J SUBSET J1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[P2A_SWIN_INTERVAL; SUBSET; IN_ELIM_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* gamma's piece moved to chart c1 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `U1:A->bool`; `phi1:A->real^N`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`;
                 `t0:real`; `tt:real`; `gamma:real->A`; `b:real`; `A2:real^1->real^N`;
                 `J:real^1->bool`; `sa:real`; `sb:real`] P2A_TRANS_ODE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `u:real^1` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(gamma:real->A)(drop u pow 2) IN O` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "O" THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a1 < tt - drop(u:real^1) pow 2 /\ tt - drop u pow 2 <= b1) /\
                  (a2 < tt - drop u pow 2 /\ tt - drop u pow 2 <= b2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `sb:real`)) (concl th) &&
          can (find_term ((=) `b1:real`)) (concl th)));
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `d2:real`)) (concl th) &&
          can (find_term ((=) `b2:real`)) (concl th)))] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
      can (find_term ((=) `A2:real^1->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  (* the velocities agree at s0 *)
  ABBREV_TAC `B2 = frechet_derivative (h:real^N->real^N) (at ((phi2:A->real^N) p))
                                      ((A2:real^1->real^N)(lift s0))` THEN
  SUBGOAL_THEN `(B2:real^N) = (A1:real^1->real^N)(lift s0)` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC
     [`\v:real^1. (phi1:A->real^N)((gamma:real->A)(drop v pow 2))`;
      `vec 0:real^1`; `lift(sqrt b)`; `lift s0`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP P2A_SDOM_INTERVAL
      (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < b`))]) THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
    ASM_SIMP_TAC[SQRT_POS_LT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`\r:real^1. (h:real^N->real^N)((phi2:A->real^N)((gamma:real->A)(drop r pow 2)))`;
      `e:real`] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBGOAL_THEN `(gamma:real->A)(drop v pow 2) IN O` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
         [MATCH_MP_TAC P2A_SQRT_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          UNDISCH_TAC `dist(v:real^1,lift s0) < e` THEN
          REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
        EXPAND_TAC "O" THEN SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `J:real^1->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_solution")) (concl th)))) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN
      SUBGOAL_THEN `interval[vec 0,lift(sqrt b)] = {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_SDOM_INTERVAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the s-family of region 1 on (sa,sb) *)
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi1:A->real^N) (U1 INTER W1)) sa sb
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 b1 (U1 INTER W1,phi1) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1) W1`; `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1) W1`;
      `a1:real`; `b1:real`; `p2a_rmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 b1`;
      `(U1 INTER W1:A->bool,phi1:A->real^N)`; `tt:real`; `sa:real`; `sb:real`]
     P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 a1 b1` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U1:A->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (phi1:A->real^N) (U1 INTER W1)`; `sa:real`; `sb:real`;
    `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 b1 (U1 INTER W1,phi1)`; `tt:real`; `J:real^1->bool`; `J:real^1->bool`;
    `Y1:real^1->real^N`; `A1:real^1->real^N`;
    `\u:real^1. (h:real^N->real^N)((phi2:A->real^N)((gamma:real->A)(drop u pow 2)))`;
    `\u:real^1. frechet_derivative (h:real^N->real^N)
                  (at ((phi2:A->real^N)((gamma:real->A)(drop u pow 2))))
                  ((A2:real^1->real^N) u)`;
    `lift s0`] P2A_LSOL_UNIQUE) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN EXISTS_TAC `J1:real^1->bool` THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `A1:real^1->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
    can (find_term ((=) `J:real^1->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "J" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN O` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "O" THEN SET_TAC[]]);;

let P2AXR_LGEOD_LOCAL_C1_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b tau0.
     &0 < b /\ (!s0. &0 < s0 /\ s0 pow 2 <= b ==> p2axr_lgeod_at V tt gamma b s0) /\
     &0 < tau0 /\ tau0 <= b
     ==> ?dd. &0 < dd /\
              !S c. S SUBSET {s | tau0 - dd <= drop s /\ drop s <= tau0 + dd /\
                                  &0 <= drop s /\ drop s <= b /\
                                  c IN p2a_vatlas V (tt - drop s) /\ gamma(drop s) IN FST c}
                    ==> continuously_differentiable 1 S (\s. SND c (gamma(drop s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN

  SUBGOAL_THEN `?s0. &0 < s0 /\ tau0 = s0 pow 2`
    (X_CHOOSE_THEN `s0:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [EXISTS_TAC `sqrt tau0` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2axr_lgeod_at (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) tt gamma b s0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`]
                P2AXR_LGEOD_PIECE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `d:real`
      (X_CHOOSE_THEN `A:real^1->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "WIN")
            (CONJUNCTS_THEN2 (LABEL_TAC "MEM") (CONJUNCTS_THEN2 (LABEL_TAC "ODE")
              (K ALL_TAC))))))))))))))) THEN
  SUBGOAL_THEN `a' < b'` ASSUME_TAC THENL
   [USE_THEN "WIN" (MP_TAC o SPEC `s0:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s0 pow 2) IN U INTER W` ASSUME_TAC THENL
   [USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - d`; `s0 + d`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `s0:real`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`;
                 `(A:real^1->real^N)(lift s0)`] P2A_LSOL_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN P2A_ARITH_CONJS_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^1->bool` (X_CHOOSE_THEN `Y1:real^1->real^N`
    (X_CHOOSE_THEN `A1:real^1->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `lift s0` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open (J:real^1->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - d`; `s0 + d`; `Y1:real^1->real^N`; `A1:real^1->real^N`;
                 `J:real^1->bool`; `r:real`] P2AXR_LGEOD_CHART_UNIQUE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN P2A_ARITH_CONJS_TAC THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "WIN" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
      REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "ODE" (MP_TAC o SPEC `lift s0`) THEN
    REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL; REAL_ABS_0] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQ")))] THEN
  ABBREV_TAC `e' = min (min d r) (min e s0) / &2` THEN
  SUBGOAL_THEN `&0 < e' /\ &2 * e' <= d /\ &2 * e' <= r /\ &2 * e' <= e /\ &2 * e' <= s0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "e'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s0 - e') pow 2 < s0 pow 2 /\ s0 pow 2 < (s0 + e') pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* facts on [(s0 - e')^2, (s0 + e')^2] *)
  SUBGOAL_THEN
   `!tau. (s0 - e') pow 2 <= tau /\ tau <= (s0 + e') pow 2
          ==> &0 < tau /\ s0 - e' <= sqrt tau /\ sqrt tau <= s0 + e' /\
              sqrt tau pow 2 = tau /\ lift(sqrt tau) IN J /\
              a' < tt - tau /\ tt - tau <= b' /\
              (Y1:real^1->real^N)(lift(sqrt tau)) IN IMAGE (phi:A->real^N) (U INTER W) /\
              (Y1 has_vector_derivative A1(lift(sqrt tau))) (at (lift(sqrt tau))) /\
              A1 differentiable (at (lift(sqrt tau)))`
  (LABEL_TAC "TF") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(s0 - e') pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `s0 - e' <= sqrt tau /\ sqrt tau <= s0 + e' /\ sqrt tau pow 2 = tau`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `lift(sqrt tau) IN J` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
      REWRITE_TAC[IN_BALL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `a' < tt - tau /\ tt - tau <= b'` STRIP_ASSUME_TAC THENL
     [USE_THEN "WIN" (MP_TAC o SPEC `sqrt tau`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`;
                   `tt:real`;
                   `interval(lift(s0 - d),lift(s0 + d)) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `J:real^1->bool`; `Y1:real^1->real^N`; `A1:real^1->real^N`;
                   `lift(sqrt tau)`] P2A_LSOL_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_solution")) (concl th))) THEN
      REWRITE_TAC[P2A_LSOL_ODE] THEN DISCH_THEN(MP_TAC o SPEC `lift(sqrt tau)` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[];
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the chart curves of the solution in slice charts *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\t:real^1. (Y1:real^1->real^N)(lift(sqrt(drop t)))`;
                 `\t:real^1. inv(&2 * sqrt(drop t)) %
                             vector_derivative (Y1:real^1->real^N) (at (lift(sqrt(drop t))))`;
                 `(s0 - e') pow 2`; `(s0 + e') pow 2`] P2A_CHART_CURVE_PC1) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN USE_THEN "TF" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN USE_THEN "TF" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_SQRT_CURVE_DERIV THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `vector_derivative (Y1:real^1->real^N) (at (lift(sqrt tau))) = A1(lift(sqrt tau))`
    SUBST1_TAC THENL [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`A1:real^1->real^N`; `J:real^1->bool`] THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT] THEN
    X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`;
                   `tt:real`;
                   `interval(lift(s0 - d),lift(s0 + d)) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `J:real^1->bool`; `Y1:real^1->real^N`; `A1:real^1->real^N`;
                   `y:real^1`] P2A_LSOL_AT) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(LABEL_TAC "CD")] THEN
  (* gamma is the chart inverse of the solution near s0^2 *)
  EXISTS_TAC `min (s0 pow 2 - (s0 - e') pow 2) ((s0 + e') pow 2 - s0 pow 2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`S:real^1->bool`; `c:(A->bool)#(A->real^N)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!s. s IN S ==> (gamma:real->A)(drop s) =
                   chart_inv (U INTER W,phi:A->real^N) ((Y1:real^1->real^N)(lift(sqrt(drop s))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s0 pow 2 - min (s0 pow 2 - (s0 - e') pow 2) ((s0 + e') pow 2 - s0 pow 2)
                    <= drop y /\
                  drop y <= s0 pow 2 + min (s0 pow 2 - (s0 - e') pow 2) ((s0 + e') pow 2 - s0 pow 2) /\
                  &0 <= drop y /\ drop y <= b`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "TF" (MP_TAC o SPEC `drop(y:real^1)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A)(sqrt(drop y) pow 2) IN U INTER W /\
                  (phi:A->real^N)(gamma(sqrt(drop y) pow 2)) =
                  (Y1:real^1->real^N)(lift(sqrt(drop y)))`
    MP_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `Y1:real^1->real^N`)) (concl th) &&
      can (find_term ((=) `y:real^1`)) (concl th))) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b':real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ THEN
  EXISTS_TAC `\s. SND (c:(A->bool)#(A->real^N))
                    (chart_inv (U INTER W,phi:A->real^N) ((Y1:real^1->real^N)(lift(sqrt(drop s)))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "CD" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s0 pow 2 - min (s0 pow 2 - (s0 - e') pow 2) ((s0 + e') pow 2 - s0 pow 2)
                  <= drop y /\
                drop y <= s0 pow 2 + min (s0 pow 2 - (s0 - e') pow 2) ((s0 + e') pow 2 - s0 pow 2) /\
                (c:(A->bool)#(A->real^N)) IN
                p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - drop y) /\
                (gamma:real->A)(drop y) IN FST c`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `S:real^1->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A p2a_minx curve satisfies the local L-geodesic condition at every time   *)
(* s0 > 0 (a region at gamma(s0^2) from its smooth points), hence is C^1 in  *)
(* every slice chart near every tau0 in (0,b]: it is p2a_pc1 with no         *)
(* corners, p2a_adm, and a p2a_min minimizer (P2AXR_MINX_MIN).               *)
(* ------------------------------------------------------------------------- *)

let P2AXR_REGION_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) s0.
     p2a_admx V tt x b gamma /\ &0 < s0 /\ s0 pow 2 <= b
     ==> ?W a' b'' U (phi:A->real^N).
           p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
           gamma(s0 pow 2) IN U INTER W /\ a' < tt - s0 pow 2 /\ tt - s0 pow 2 < b''`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?W a' b''. (gamma:real->A)(s0 pow 2) IN W /\ a' < tt - s0 pow 2 /\
               p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) W a' b'' /\
               tt - s0 pow 2 < b''`
  MP_TAC THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s0 pow 2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_smooth")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p2a_smooth] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
      STRIP_ASSUME_TAC)))] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `b'':real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b''`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b''`;
                 `(gamma:real->A)(s0 pow 2)`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                       (real->A->real^N^N)) b'') W`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`W:A->bool`; `a':real`; `b'':real`;
    `FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) b'') ((gamma:real->A)(s0 pow 2)))`;
    `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) b'') ((gamma:real->A)(s0 pow 2)))`] THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER]);;

let P2AXR_MINX_LGEOD_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) s0.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_minx V tt x b gamma /\ &0 < s0 /\ s0 pow 2 <= b
     ==> p2axr_lgeod_at V tt gamma b s0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2axr_lgeod_at] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2a_minx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_minx")) (concl th))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `s0:real`] P2AXR_REGION_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `?d (A:real^1->real^N).
       &0 < d /\
       (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < d
            ==> (gamma:real->A)(s pow 2) IN U INTER W /\ a' < tt - s pow 2 /\
                tt - s pow 2 <= b'') /\
       (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d
            ==> ((\v. (phi:A->real^N)(gamma(drop v pow 2))) has_vector_derivative A u)
                  (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                (A has_vector_derivative
                   p2a_lacc (p2a_rlocal V W b'' (U INTER W,phi)) tt (drop u)
                            (phi(gamma(drop u pow 2))) (A u))
                  (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}))`
  MP_TAC THENL
   [ASM_CASES_TAC `s0 pow 2 = b` THENL
     [MATCH_MP_TAC P2AXR_MINX_LOC_END THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2AXR_MINX_LOC_INT THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `A:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b'':real`;
                        `(U INTER W:A->bool,phi:A->real^N)`; `d:real`;
                        `A:real^1->real^N`] THEN
  ASM_REWRITE_TAC[FST; SND; IN_RESTRICT_ATLAS] THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]);;

let P2AXR_MINX_PC1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A).
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_minx V tt x b gamma
     ==> p2a_pc1 V tt gamma (&0) b {}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_minx; p2a_admx]; ALL_TAC] THEN
  SUBGOAL_THEN `!s0. &0 < s0 /\ s0 pow 2 <= b
                     ==> p2axr_lgeod_at (V:(real->A topology)#
                           (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                           tt gamma b s0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AXR_MINX_LGEOD_AT THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`tau0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `tau0:real`]
                P2AXR_LGEOD_LOCAL_C1_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `dd:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Headline: minimizers among curves with singular corners are minimizers   *)
(* (and corner-free).                                                         *)

let P2AXR_MINX_MIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A).
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_minx V tt x b gamma
     ==> p2a_min V tt x b gamma /\ p2a_pc1 V tt gamma (&0) b {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_pc1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt gamma (&0) b {}` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AXR_MINX_PC1 THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AX_MINX_MIN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AX_ADMX_ADM THEN EXISTS_TAC `{}:real->bool` THEN
  ASM_MESON_TAC[p2a_minx]);;

