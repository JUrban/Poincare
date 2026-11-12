(* ========================================================================= *)
(* Unit pc_p3_s13thm (Part 3 proofs; MT Thm 13.2 with Claim                 *)
(* 13.1): P3_THM_13_2_STATEMENT of pc_p3_route, unconditionally, and the    *)
(* route obligation P3_THM_13_2_ROUTE_STATEMENT.  For p3_std_initial g0 A0  *)
(* the constants are r0 and Q0 of the cap (P3S_CAP_GS), q = max Q0 8, C0 of *)
(* the neck region (P3S_NECK_GS), d0 below the neck and pinching thresholds, *)
(* cm / C0 and 1 / (2 (A0 + 4)), h0 = 1 and md = p3s_md g0 A0 q C0 r0.  The *)
(* surgery metric is gS = p3s_gs g0 A0 (C0 dl) q r0 dl h gN and the        *)
(* collapse is p3s_xi g0 A0 e, e from P3S_XI_E_CHOICE.                        *)
(* ========================================================================= *)

needs "src/pc_p3_s13close.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* P3_THM_13_2 and P3_THM_13_2_ROUTE.  Clauses: riemannian                  *)
(* (P3S_GS_RIEMANNIAN), gS = nc^* gN where s1 < 0 (P3S_GS_NECK), positive   *)
(* curvature where s1 >= 1 (P3S_NECK_GS for s1 <= 2, P3S_CAP_GS beyond),     *)
(* pinching (P3S_PINCH_CLAUSE), closeness (P3S_MD), the collapse            *)
(* (P3S_XI_CLAUSES).                                                         *)
(* ========================================================================= *)

let P3_THM_13_2 = prove
 (`P3_THM_13_2_STATEMENT`,
  REWRITE_TAC[P3_THM_13_2_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3S_CAP_GS) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Q0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `max Q0 (&8)`)))))) THEN
  REWRITE_TAC[REAL_ARITH `Q0 <= max Q0 (&8)`] THEN
  ABBREV_TAC `q = max Q0 (&8)` THEN
  DISCH_THEN(X_CHOOSE_THEN `cm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAP"))) THEN
  SUBGOAL_THEN `&8 <= q /\ &0 < q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`] P3S_NECK_GS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `C0:real`))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `dm1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NECK")))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`; `C0:real`] P3S_PINCH_CLAUSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dm2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PINCH")))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`; `C0:real`; `r0:real`] P3S_MD) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MD")) THEN
  ABBREV_TAC `d0 = min (min dm1 dm2) (min (cm / C0) (inv(&2 * (A0 + &4))))` THEN
  SUBGOAL_THEN `&0 < inv(&2 * (A0 + &4)) /\ (A0 + &4) * inv(&2 * (A0 + &4)) = &1 / &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < A0` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d0 /\ d0 <= dm1 /\ d0 <= dm2 /\ d0 <= cm / C0 /\
                d0 <= inv(&2 * (A0 + &4))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d0:real`; `&1`; `p3s_md g0 A0 q C0 r0`] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(A0 + &4) * inv(&2 * (A0 + &4))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`dl:real`; `h:real`; `t:real`; `gN:real^3->real^3^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `dl <= dm1 /\ dl <= dm2 /\ dl <= cm / C0 /\ dl < &1 / &4`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (gN:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN ASM_REWRITE_TAC[P3S_NECK_DOM_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C0 * dl /\ C0 * dl <= cm` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL] THEN
    UNDISCH_TAC `dl <= cm / C0` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`C0 * dl`; `q:real`] P3S_XI_E_CHOICE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`p3s_gs g0 A0 (C0 * dl) q r0 dl h gN`; `p3s_xi g0 A0 e`] THEN
  SUBGOAL_THEN
   `!x u v. &1 <= A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
            ==> &0 < mfd_sectional
                       (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                       (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) x u v`
  (LABEL_TAC "POS") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `A0 + &4 - p3_std_dist g0 (x:real^3) <= &2` THENL
     [USE_THEN "NECK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "CAP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `C0 * dl`; `q:real`; `r0:real`; `dl:real`;
                `h:real`; `gN:real^3->real^3^3`; `e:real`] P3S_XI_CLAUSES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3S_GS_RIEMANNIAN THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC P3S_GS_NECK THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "PINCH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `dd:real` THEN STRIP_TAC THEN USE_THEN "MD" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3_THM_13_2_ROUTE = prove
 (`P3_THM_13_2_ROUTE_STATEMENT`,
  REWRITE_TAC[P3_THM_13_2_ROUTE_STATEMENT; P3_THM_13_2]);;

