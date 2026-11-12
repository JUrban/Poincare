(* ========================================================================= *)
(* Unit pc_p2b_l925 (Part 2B): MT Lemma 9.25 for kappa-solutions, the route  *)
(* P2B_LEMMA_9_25_ROUTE_STATEMENT of the statements-only unit pc_p2b_w920g,  *)
(* from FL9, FL8 (pc_p2a_fldefs), Cor 9.10 (P2B_COR_9_10_STATEMENT) and the  *)
(* local distance distortion DIST_LOCAL (pc_p2b_distreq).  MT's proof at a   *)
(* general backward time T: the distance                                     *)
(* f(s) = d_{g(-s)}(gamma1 s, gamma2 s) of the two minimizers of FL9 has     *)
(* upper right Dini derivative at most A s^(-3/4) and is lower               *)
(* semicontinuous from the left, so f(T) <= 4 A T^(1/4).                     *)
(*                                                                           *)
(* First a Dini-derivative integration lemma, the fourth root and traces of  *)
(* positive semidefinite forms.                                              *)
(* ========================================================================= *)

needs "src/pc_p2b_c910.ml";;
needs "src/pc_grg_distcont.ml";;
needs "src/pc_rf_unique_a14.ml";;

prioritize_real();;
type_invention_error := true;;

(* Right Dini derivative below e / 2 and lower semicontinuity from the left *)
(* give f b <= f a + e (b - a).                                             *)

let P2BX_DINI_MONO_E = prove
 (`!(f:real->real) a b e.
     a <= b /\ &0 < e /\
     (!s. a <= s /\ s < b
          ==> ?d. &0 < d /\
                  !h. &0 < h /\ h < d /\ s + h <= b ==> f(s + h) <= f s + e / &2 * h) /\
     (!s ee. a < s /\ s <= b /\ &0 < ee
             ==> ?d. &0 < d /\ !h. &0 < h /\ h < d /\ a <= s - h ==> f s <= f(s - h) + ee)
     ==> f b <= f a + e * (b - a)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "RD") (LABEL_TAC "LSC")))) THEN
  MP_TAC(ISPEC `{s | a <= s /\ s <= b /\
                     !u. a <= u /\ u <= s ==> (f:real->real) u <= f a + e * (u - a)}` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `u:real = a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      EXISTS_TAC `b:real` THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `m = sup {s | a <= s /\ s <= b /\
                           !u. a <= u /\ u <= s ==> (f:real->real) u <= f a + e * (u - a)}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UB") (LABEL_TAC "LUB")) THEN
  SUBGOAL_THEN `a <= m /\ m <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "UB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `u:real = a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      USE_THEN "LUB" MATCH_MP_TAC THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. a <= u /\ u < m ==> (f:real->real) u <= f a + e * (u - a)`
  (LABEL_TAC "BELOW") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?s. a <= s /\ s <= b /\
                      (!u'. a <= u' /\ u' <= s ==> (f:real->real) u' <= f a + e * (u' - a)) /\
                      u < s`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      USE_THEN "LUB" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) m <= f a + e * (m - a)` (LABEL_TAC "ATM") THENL
   [ASM_CASES_TAC `m:real = a` THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "LSC" (MP_TAC o SPECL [`m:real`;
                                   `((f:real->real) m - (f a + e * (m - a))) / &2`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LD"))) THEN
    ABBREV_TAC `h = min (d / &2) ((m - a) / &2)` THEN
    SUBGOAL_THEN `&0 < h /\ h < d /\ a <= m - h /\ m - h < m` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "LD" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "BELOW" (MP_TAC o SPEC `m - h:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= e * h` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `f a + e * (m - a) < (f:real->real) m` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `m:real = b` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN USE_THEN "ATM" ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "RD" (MP_TAC o SPEC `m:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RDm"))) THEN
  ABBREV_TAC `h = min (d / &2) (b - m)` THEN
  SUBGOAL_THEN `&0 < h /\ h < d /\ m + h <= b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "UB" (MP_TAC o SPEC `m + h:real`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `u < m` THENL
     [USE_THEN "BELOW" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `u:real = m` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "RDm" (MP_TAC o SPEC `u - m:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `m + (u - m) = u`] THEN
    SUBGOAL_THEN `&0 <= e * (u - m)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ATM" MP_TAC THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BX_DINI_MONO = prove
 (`!(f:real->real) a b.
     a <= b /\
     (!s e. a <= s /\ s < b /\ &0 < e
            ==> ?d. &0 < d /\
                    !h. &0 < h /\ h < d /\ s + h <= b ==> f(s + h) <= f s + e * h) /\
     (!s e. a < s /\ s <= b /\ &0 < e
            ==> ?d. &0 < d /\ !h. &0 < h /\ h < d /\ a <= s - h ==> f s <= f(s - h) + e)
     ==> f b <= f a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "RD") (LABEL_TAC "LSC"))) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `q = ((f:real->real) b - f a) / (b - a + &1)` THEN
  SUBGOAL_THEN `&0 < q /\ q * (b - a + &1) = (f:real->real) b - f a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `q:real`] P2BX_DINI_MONO_E) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "RD" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `q * (b - a + &1) = (f:real->real) b - f a` THEN
  UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC);;

(* A real derivative gives a lower bound for right increments. *)

let P2BX_DERIV_RIGHT_LOWER = prove
 (`!(ff:real->real) ff' s e.
     (ff has_real_derivative ff') (atreal s) /\ &0 < e
     ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> ff s + h * (ff' - e) <= ff(s + h)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o REWRITE_RULE[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s + h:real`) THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(ff' - e) * h <= ((ff:real->real)(s + h) - ff s) / h * h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC);;

(* The fourth root and its derivative. *)

let P2BX_QRT_DERIV = prove
 (`!s. &0 < s
       ==> ((\x. sqrt(sqrt x)) has_real_derivative inv(&4 * sqrt(sqrt s) pow 3)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt s /\ &0 < sqrt(sqrt s)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&4 * sqrt(sqrt s) pow 3) = inv(&2 * sqrt(sqrt s)) * inv(&2 * sqrt s)`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `sqrt s` SQRT_POW_2) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sqrt(sqrt s)` THEN
    SPEC_TAC(`sqrt(sqrt s)`,`q:real`) THEN SPEC_TAC(`sqrt s`,`r:real`) THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt`; `sqrt`; `inv(&2 * sqrt s)`; `inv(&2 * sqrt(sqrt s))`; `s:real`]
         REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT; o_DEF]);;

(* A positive semidefinite form is at most its trace times the square norm. *)

let P2BX_PSD_TRACE = prove
 (`!(A:real^N^N) x. positive_semidefinite A ==> x dot (A ** x) <= trace A * (x dot x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = (lambda i j. (x:real^N)$i * x$j):real^N^N` THEN
  SUBGOAL_THEN `!y:real^N. y dot ((B:real^N^N) ** y) = (x dot y) pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN EXPAND_TAC "B" THEN
    SIMP_TAC[dot; matrix_vector_mul; LAMBDA_BETA; REAL_POW_2] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `positive_semidefinite(B:real^N^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[positive_semidefinite; symmetric_matrix; REAL_LE_POW_2] THEN
    EXPAND_TAC "B" THEN SIMP_TAC[CART_EQ; transp; LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^N^N`; `B:real^N^N`] TRACE_MUL_POSITIVE_SEMIDEFINITE_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `trace((A:real^N^N) ** B) = x dot (A ** x) /\ trace(B:real^N^N) = x dot x`
  (fun th -> REWRITE_TAC[th]) THEN
  EXPAND_TAC "B" THEN SIMP_TAC[trace; matrix_mul; dot; matrix_vector_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Nonnegative sectional curvature gives 0 <= Ric <= R g.                    *)
(* ------------------------------------------------------------------------- *)

let P2BX_RIEM_TERM_NONNEG = prove
 (`!U (G:real^N->real^N^N) y e v.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> &0 <= e dot (G y ** lriemann G y e v v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sect"))) THEN
  SUBGOAL_THEN
   `(!v w. linear (\u. lriemann (G:real^N->real^N^N) y u v w)) /\
    (!u w. linear (\v. lriemann G y u v w)) /\
    (!u v. linear (\w. lriemann G y u v w))`
  (CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "L2") (LABEL_TAC "L3"))) THENL
   [MATCH_MP_TAC LRIEMANN_TRILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `collinear {vec 0,e:real^N,v}` THENL
   [SUBGOAL_THEN `lriemann (G:real^N->real^N^N) y e v v = vec 0`
     (fun th -> REWRITE_TAC[th; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL]) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[COLLINEAR_LEMMA]) THEN STRIP_TAC THENL
     [USE_THEN "L1" (MP_TAC o MATCH_MP LINEAR_0 o SPECL [`v:real^N`; `v:real^N`]) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "L2" (MP_TAC o MATCH_MP LINEAR_0 o SPECL [`e:real^N`; `vec 0:real^N`]) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "L2" (MP_TAC o MATCH_MP LINEAR_CMUL o SPECL [`e:real^N`; `c % e:real^N`]) THEN
      DISCH_THEN(MP_TAC o SPECL [`c:real`; `e:real^N`]) THEN REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `e:real^N`;
                     `e:real^N`; `c % e:real^N`] LRIEMANN_ANTISYM) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(x:real^N) = --x <=> x = vec 0`] THEN
      SIMP_TAC[VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  USE_THEN "sect" (fun th -> MP_TAC(MATCH_MP (SPECL [`e:real^N`; `v:real^N`] th)
                                     (ASSUME `~collinear {vec 0,e:real^N,v}`))) THEN
  REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `e:real^N`; `v:real^N`]
                APX_SECT_DEN_POS) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO]);;

let P2BX_LRICCI_NONNEG = prove
 (`!U (G:real^N->real^N^N) y w.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> &0 <= lricci G y w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`;
                 `w:real^N`] P2B_LRICCI_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2BX_RIEM_TERM_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2BX_LRICCI_LE_SCALAR = prove
 (`!U (G:real^N->real^N^N) y w.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> lricci G y w w <= lscalar G y * (w dot (G y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Rm = (lambda i j. lricci (G:real^N->real^N^N) y (basis i) (basis j)):real^N^N` THEN
  SUBGOAL_THEN `!p q:real^N. p dot ((Rm:real^N^N) ** q) = lricci (G:real^N->real^N^N) y p q`
  (LABEL_TAC "DF") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "Rm" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LRG_LRICCI_DOT_FORM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(Rm:real^N^N) = Rm` ASSUME_TAC THENL
   [EXPAND_TAC "Rm" THEN SIMP_TAC[CART_EQ; transp; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Mi = matrix_inv(M:real^N^N)` THEN
  SUBGOAL_THEN `(Mi:real^N^N) ** M = mat 1 /\ M ** Mi = mat 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Mi" THEN ASM_SIMP_TAC[MATRIX_INV]; ALL_TAC] THEN
  ABBREV_TAC `A = transp(Mi:real^N^N) ** (Rm:real^N^N) ** Mi` THEN
  SUBGOAL_THEN `!x:real^N. x dot ((A:real^N^N) ** x) =
                           lricci (G:real^N->real^N^N) y (Mi ** x) (Mi ** x)`
  (LABEL_TAC "QA") THENL
   [GEN_TAC THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    USE_THEN "DF" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `positive_semidefinite(A:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN CONJ_TAC THENL
     [EXPAND_TAC "A" THEN
      REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN USE_THEN "QA" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC P2BX_LRICCI_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `trace(A:real^N^N) = lscalar (G:real^N->real^N^N) y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LSCALAR_TRACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN
    SUBGOAL_THEN `matrix_inv(transp M ** M:real^N^N) = (Mi:real^N^N) ** transp Mi` SUBST1_TAC THENL
     [EXPAND_TAC "Mi" THEN ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((M:real^N^N) ** w) dot (M ** w) = w dot ((G:real^N->real^N^N) y ** w)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^N^N`; `(M:real^N^N) ** w`] P2BX_PSD_TRACE) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "QA" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

(* The manifold forms at a point (preferred chart). *)

let P2BX_MFD_RICCI_BOUNDS = prove
 (`!top atlas (g:A->real^N^N) x w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> &0 <= mfd_ricci atlas g x w w /\
         mfd_ricci atlas g x w w <= mfd_scalar atlas g x * (w dot (g x ** w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sect")))) THEN
  REWRITE_TAC[mfd_ricci; mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:A->real^N^N) x =
                metric_local atlas (chart_at atlas x) g (SND(chart_at atlas x) x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x)))
                  (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                                (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0,u,v}
          ==> &0 <= lsectional (metric_local atlas (chart_at atlas x) (g:A->real^N^N))
                               (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x) u v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sect" (MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[mfd_sectional]];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC P2BX_LRICCI_NONNEG; MATCH_MP_TAC P2BX_LRICCI_LE_SCALAR] THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* The metrics of a kappa-solution are nonincreasing in time                 *)
(* (Ric >= 0) and comparable over short time intervals (bounded curvature,  *)
(* RFU_FLOW_EQUIV); the corresponding distance comparisons.                 *)
(* ------------------------------------------------------------------------- *)

let P2BX_KSOL_QFORM_MONO = prove
 (`!kappa top atlas (g:real->B->real^3^3) x v t1 t2.
     p2b_kappa_solution kappa (top,atlas) g /\ x IN topspace top /\ t1 <= t2 /\ t2 < &0
     ==> v dot (g t2 x ** v) <= v dot (g t1 x ** v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ASM_CASES_TAC `t1:real = t2` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (t1 - &1) (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `p2a_cbflow (top,atlas) (t1 - &1) (&0) (g:real->B->real^3^3)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[p2a_cbflow; ricci_flow_from]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. t1 - &1 < s /\ s < &0
        ==> ((\s. v dot ((g:real->B->real^3^3) s x ** v)) has_real_derivative
             --(&2) * mfd_ricci atlas (g s) x v v) (atreal s)`
  (LABEL_TAC "D") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `t1 - &1`; `&0`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. t1 - &1 < s /\ s < &0
        ==> ((\s. --(v dot ((g:real->B->real^3^3) s x ** v))) has_real_derivative
             &2 * mfd_ricci atlas (g s) x v v) (atreal s)`
  (LABEL_TAC "ND") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "D" (MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_NEG o C MATCH_MP
      (ASSUME `t1 - &1 < s /\ s < &0`) o SPEC `s:real`) THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_NEG_NEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. --(v dot ((g:real->B->real^3^3) s x ** v))`;
                 `\s. &2 * mfd_ricci atlas ((g:real->B->real^3^3) s) x v v`;
                 `t1:real`; `t2:real`] RFA_MVT_MONO) THEN
  REWRITE_TAC[REAL_LE_NEG2] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `&2 * mfd_ricci atlas ((g:real->B->real^3^3) s) x v v` THEN
    USE_THEN "ND" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "ND" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `x:B`; `v:real^3`] P2BX_MFD_RICCI_BOUNDS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `mfd_sectional:((B->bool)#(B->real^3)->bool)->(B->real^3^3)->B->real^3->real^3->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Distances under a pointwise comparison of two metrics. *)

let P2BX_DIST_COMPARE = prove
 (`!top atlas (g:A->real^N^N) g' c x y.
     smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ riemannian_metric atlas g' /\ &0 <= c /\
     (!z v. z IN topspace top ==> v dot (g' z ** v) <= c * (v dot (g z ** v))) /\
     mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) g' x y <= sqrt c * mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma0:real->A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [mfd_joinable]) THEN
  SUBGOAL_THEN
   `!gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\ gamma(&1) = y
            ==> mfd_dist (top,atlas) (g':A->real^N^N) x y <=
                sqrt c * mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)`
  (LABEL_TAC "CU") THENL
   [X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g':A->real^N^N) gamma (&0) (&1)` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g':A->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_LENGTH_METRIC_COMPARE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`] THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `c = &0` THENL
   [USE_THEN "CU" (MP_TAC o SPEC `gamma0:real->A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SQRT_0; REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gamma0:real->A) (&0) (&1)` THEN
    EXISTS_TAC `gamma0:real->A` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    USE_THEN "CU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Distances of a kappa-solution decrease in time. *)

let P2BX_KSOL_DIST_MONO = prove
 (`!kappa top atlas (g:real->B->real^3^3) t1 t2 x y.
     p2b_kappa_solution kappa (top,atlas) g /\ t1 <= t2 /\ t2 < &0 /\
     x IN topspace top /\ y IN topspace top
     ==> mfd_dist (top,atlas) (g t2) x y <= mfd_dist (top,atlas) (g t1) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) t1`; `(g:real->B->real^3^3) t2`; `&1`;
                 `x:B`; `y:B`] P2BX_DIST_COMPARE) THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_KSOL_QFORM_MONO THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`;
                          `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]]);;

(* Short-time comparison of the distances (bounded curvature). *)

let P2BX_KSOL_DIST_EQUIV = prove
 (`!kappa top atlas (g:real->B->real^3^3) s.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < s
     ==> ?C. &0 <= C /\
             !h x y. &0 < h /\ h <= s / &2 /\ x IN topspace top /\ y IN topspace top
                     ==> mfd_dist (top,atlas) (g(--s)) x y <=
                         exp(C * h) * mfd_dist (top,atlas) (g(--(s - h))) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQ"))
    (INST_TYPE [`:B`,`:A`; `:3`,`:N`] RFU_FLOW_EQUIV) THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_kappa_solution] THEN
  DISCH_THEN(MP_TAC o SPEC `--(s + &1)` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `K0:real`) THEN
  ABBREV_TAC `K = max (&0) K0` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `&2 * C0 * K` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas) (--s) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`--(s + &1)`; `&0`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(s + &1)) (&0) (g:real->B->real^3^3)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[p2a_cbflow]];
    ALL_TAC] THEN
  USE_THEN "EQ" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                 `--s`; `&0`; `g:real->B->real^3^3`; `--s + &2 * h`;
                                 `K:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0:real` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "K" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "QF") THEN
  SUBGOAL_THEN `(--s + &2 * h) - --s = &2 * h` SUBST_ALL_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--(s - h))`; `(g:real->B->real^3^3) (--s)`;
                 `exp(&2 * (C0 * K) * &2 * h)`; `x:B`; `y:B`] P2BX_DIST_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:B`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "QF" (MP_TAC o SPECL [`--(s - h)`; `z:B`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN `&0 < exp(&2 * (C0 * K) * &2 * h)` MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
      SUBGOAL_THEN `exp(--(&2 * (C0 * K) * &2 * h)) = inv(exp(&2 * (C0 * K) * &2 * h))`
      SUBST1_TAC THENL [REWRITE_TAC[REAL_EXP_NEG]; ALL_TAC] THEN
      SPEC_TAC(`exp(&2 * (C0 * K) * &2 * h)`,`E:real`) THEN
      SPEC_TAC(`v dot ((g:real->B->real^3^3) (--s) z ** v)`,`P:real`) THEN
      SPEC_TAC(`v dot ((g:real->B->real^3^3) (--(s - h)) z ** v)`,`Q:real`) THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ];
      MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c. b = c ==> a <= b ==> a <= c`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `exp(&2 * (C0 * K) * &2 * h) = exp((&2 * C0 * K) * h) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_EXP_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Moving a point along a curve that has a chart velocity v at               *)
(* s costs at most h (|v| + e) of distance over the time step h, also when  *)
(* the metric moves with the time (continuity of the chart metric of the    *)
(* flow in space and time).                                                 *)
(* ------------------------------------------------------------------------- *)

(* The length of a chart segment, measured against a fixed form. *)

let P2BX_SEGMENT_FROZEN = prove
 (`!top atlas (g:A->real^N^N) (U:A->bool) phi p q (G0:real^N^N) C.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (U,phi) IN atlas /\ segment[p,q] SUBSET IMAGE phi U /\ &0 <= C /\
     &0 <= (q - p) dot (G0 ** (q - p)) /\
     (!y. y IN segment[p,q]
          ==> (q - p) dot (metric_local atlas (U,phi) g y ** (q - p)) <=
              C * ((q - p) dot (G0 ** (q - p))))
     ==> mfd_length atlas g (\t. chart_inv (U,phi) (p + t % (q - p))) (&0) (&1)
         <= sqrt C * sqrt((q - p) dot (G0 ** (q - p)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `p:real^N`; `q:real^N`]
               GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,&1])
                (\t:real. sqrt C * sqrt((q - p) dot ((G0:real^N^N) ** (q - p))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `\t. chart_inv (U:A->bool,phi:A->real^N) (p + t % (q - p))`;
                   `&0`; `&1`; `t:real`; `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_01]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL; REAL_POW_MUL; SQRT_POW_2] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS] THEN REAL_ARITH_TAC]);;

(* The chart metric of a kappa-solution near (x,-s) in space-time is at     *)
(* most (1 + ee) times the fixed form at (x,-s).                            *)

let P2BX_FLOW_METRIC_NEAR = prove
 (`!kappa top atlas (g:real->B->real^3^3) c x s ee.
     p2b_kappa_solution kappa (top,atlas) g /\ c IN atlas /\
     x IN IMAGE (SND c) (FST c) /\ &0 < s /\ &0 < ee
     ==> ?r. &0 < r /\ r <= s /\ ball(x,r) SUBSET IMAGE (SND c) (FST c) /\
             !t y w. abs(t - --s) < r /\ dist(y,x) < r
                     ==> w dot (metric_local atlas c (g t) y ** w) <=
                         (&1 + ee) * (w dot (metric_local atlas c (g(--s)) x ** w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (--(s + &1)) (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(s + &1)) (&0) (g:real->B->real^3^3)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[p2a_cbflow; ricci_flow_from]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--s))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (--s)`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                 `{x:real^3}`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR; COMPACT_SING; SING_SUBSET; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(\z:real^(1,3)finite_sum. (vectorize:real^3^3->real^(3,3)finite_prod)
        (metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (drop(fstcart z)))
                      (sndcart z)))
    continuous at (pastecart (lift(--s)) x)` MP_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) (--(s + &1)) (&0) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)` o CONJUNCT1 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS) THEN
    SUBGOAL_THEN `open(interval(lift(--(s + &1)),lift(&0)) PCROSS
                       IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `c0 * ee / &(dimindex(:3)) pow 2`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CT"))) THEN
  MP_TAC(ASSUME `open(IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))`) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d / &2) (min r1 s)` THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^3,r1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (--s)) x`;
                 `metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) t) y`;
                 `c0:real`; `ee:real`] P2BX_QUAD_NEAR) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((vectorize:real^3^3->real^(3,3)finite_prod)
                    (metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) t) y) -
                   vectorize (metric_local atlas c (g(--s)) x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM VECTORIZE_SUB] THEN
    ASM_SIMP_TAC[GSYM MATRIX_SUB_COMPONENT; P2BX_ENTRY_LE_VECTORIZE];
    ALL_TAC] THEN
  USE_THEN "CT" (MP_TAC o SPEC `pastecart (lift t) (y:real^3)`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(lift t,lift(--s)) + dist(y:real^3,x)` THEN
    REWRITE_TAC[DIST_PASTECART_LE; DIST_LIFT] THEN
    UNDISCH_TAC `abs(t - --s) < min (d / &2) (min r1 s)` THEN
    UNDISCH_TAC `dist(y:real^3,x) < min (d / &2) (min r1 s)` THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC]);;

(* Arithmetic for the choice of the tolerances in P2BX_MOVE_POINT. *)

let P2BX_MOVE_ARITH = prove
 (`!a V D e. &0 <= a /\ a <= &1 /\ &0 <= V /\ &0 <= D /\ a * (V + &1) <= e / &4 /\
             D <= e / &4 /\ &0 < e
             ==> (&1 + a) * (V + D) <= V + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a * V <= a * (V + &1) /\ a * D <= &1 * D` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Moving the point: d_{g(-(s+h))}(gamma s, gamma(s+h)) <= h (|v| + e). *)

let P2BX_MOVE_POINT = prove
 (`!kappa top atlas (g:real->B->real^3^3) (gamma:real->B) s v e.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < s /\ gamma s IN topspace top /\
     (!O. open_in top O /\ gamma s IN O
          ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma(s + h) IN O) /\
     ((\r. SND(chart_at atlas (gamma s)) (gamma(drop r))) has_vector_derivative v)
     (at (lift s)) /\
     &0 < e
     ==> ?d. &0 < d /\
             !h. &0 < h /\ h < d
                 ==> mfd_dist (top,atlas) (g(--(s + h))) (gamma s) (gamma(s + h)) <=
                     h * (sqrt(v dot (g(--s) (gamma s) ** v)) + e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "RC")
    (CONJUNCTS_THEN2 (LABEL_TAC "VD") ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(gamma:real->B) s`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_local atlas (chart_at atlas ((gamma:real->B) s))
                  ((g:real->B->real^3^3) (--s)) (SND(chart_at atlas (gamma s)) (gamma s)) =
                g(--s) (gamma s)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) ((gamma:real->B) s)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = SND (c:(B->bool)#(B->real^3)) ((gamma:real->B) s)` THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) x = (gamma:real->B) s` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `G0 = (g:real->B->real^3^3) (--s) ((gamma:real->B) s)` THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--s))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                  (metric_local atlas c ((g:real->B->real^3^3) (--s)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)`;
                 `metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (--s))`;
                 `x:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "FN" o MATCH_MP P2BX_FROZEN_NORM))) THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (--s)`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                 `{x:real^3}`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR; COMPACT_SING; SING_SUBSET; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!w:real^3. c0 * norm w pow 2 <= w dot ((G0:real^3^3) ** w) /\
                          w dot (G0 ** w) <= C0 * norm w pow 2` (LABEL_TAC "B0") THENL
   [X_GEN_TAC `w:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `w:real^3`] o check (fun th ->
      can (find_term ((=) `C0:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 /\ &0 <= sqrt C0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= C0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `V = norm((M:real^3^3) ** v)` THEN
  SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `a = min (&1) (e / (&4 * (V + &1)))` THEN
  SUBGOAL_THEN `&0 < a /\ a <= &1 /\ a * (V + &1) <= e / &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < e / (&4 * (V + &1)) /\ e / (&4 * (V + &1)) * (V + &1) = e / &4`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&0 <= V` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    EXPAND_TAC "a" THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / (&4 * (V + &1)) * (V + &1)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `ee = (&1 + a) pow 2 - &1` THEN
  SUBGOAL_THEN `&0 < ee` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[REAL_ARITH `(&1 + a) pow 2 - &1 = a * (a + &2)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `c:(B->bool)#(B->real^3)`; `x:real^3`; `s:real`;
                 `ee:real`] P2BX_FLOW_METRIC_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEAR"))))) THEN
  ABBREV_TAC `e2 = e / (&4 * (sqrt C0 + &1))` THEN
  SUBGOAL_THEN `&0 < e2 /\ sqrt C0 * e2 <= e / &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `e2 * (sqrt C0 + &1) = e / &4` ASSUME_TAC THENL
     [EXPAND_TAC "e2" THEN UNDISCH_TAC `&0 <= sqrt C0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "e2" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= e2` MP_TAC THENL
     [EXPAND_TAC "e2" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `e2 * (sqrt C0 + &1) = e / &4` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "VD" (MP_TAC o SPEC `e2:real` o CONJUNCT2 o
                 REWRITE_RULE[has_vector_derivative; HAS_DERIVATIVE_AT_ALT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DIFF"))) THEN
  SUBGOAL_THEN `open_in top {z | z IN FST (c:(B->bool)#(B->real^3)) /\
                                 SND c z IN ball(x:real^3,r / &2)}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                   `ball(x:real^3,r / &2)`] GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; OPEN_BALL];
    ALL_TAC] THEN
  USE_THEN "RC" (MP_TAC o SPEC `{z | z IN FST (c:(B->bool)#(B->real^3)) /\
                                     SND c z IN ball(x:real^3,r / &2)}`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WIN"))) THEN
  EXISTS_TAC `min (r / &2) (min d2 d3)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  USE_THEN "WIN" (MP_TAC o SPEC `h:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `yh = SND (c:(B->bool)#(B->real^3)) ((gamma:real->B) (s + h))` THEN
  SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) yh = (gamma:real->B) (s + h)`
  ASSUME_TAC THENL [EXPAND_TAC "yh" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the chart increment *)
  SUBGOAL_THEN `norm(yh - x - h % (v:real^3)) <= e2 * h` ASSUME_TAC THENL
   [USE_THEN "DIFF" (MP_TAC o SPEC `lift(s + h)`) THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; REAL_ARITH `(s + h) - s = h`; DROP_SUB; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `(s + h) - s = h`];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^3,yh] SUBSET ball(x,r / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_BALL; CENTRE_IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^3,r / &2) SUBSET ball(x,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--(s + h)))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the segment length *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--(s + h))`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                 `x:real^3`; `yh:real^3`; `G0:real^3^3`; `&1 + ee`] P2BX_SEGMENT_FROZEN) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^3,r / &2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^3,r)` THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * norm(yh - x:real^3) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "B0" (fun th -> REWRITE_TAC[th])];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "NEAR" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^3) IN ball(x,r / &2)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_BALL] THEN MP_TAC(ISPECL [`x:real^3`; `y:real^3`] DIST_SYM) THEN
      UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + ee) = &1 + a` SUBST1_TAC THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "FN" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  (* the norm of the increment for the fixed form *)
  SUBGOAL_THEN `!w:real^3. norm((M:real^3^3) ** w) <= sqrt C0 * norm w` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN USE_THEN "FN" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_POW_MUL; SQRT_POW_2] THEN
    USE_THEN "B0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((M:real^3^3) ** (yh - x)) <= h * V + sqrt C0 * (e2 * h)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(M:real^3^3) ** (yh - x) = h % (M ** v) + M ** (yh - x - h % v)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_RMUL; GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
      AP_TERM_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(h % ((M:real^3^3) ** v)) + norm(M ** (yh - x - h % v))` THEN
    REWRITE_TAC[NORM_TRIANGLE] THEN ASM_REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c. b <= c ==> a + b <= a + c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt C0 * norm(yh - x - h % v:real^3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the distance and the arithmetic *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                 `x:real^3`; `yh:real^3`] GRGD_CHART_SEGMENT) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(x:real^3,r / &2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^3,r)` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--(s + h))`;
                 `\t. chart_inv (c:(B->bool)#(B->real^3)) (x + t % (yh - x))`; `&0`; `&1`]
                MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                  VECTOR_ARITH `x + (y - x):real^3 = y`] THEN
  MP_TAC(ISPECL [`a:real`; `V:real`; `sqrt C0 * e2`; `e:real`] P2BX_MOVE_ARITH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_MUL]; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + a) * norm((M:real^3^3) ** (yh - x)) <=
                (&1 + a) * (h * V + sqrt C0 * (e2 * h))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + a) * (h * V + sqrt C0 * (e2 * h)) = h * ((&1 + a) * (V + sqrt C0 * e2))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * ((&1 + a) * (V + sqrt C0 * e2)) <= h * (V + e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The minimizers of FL9.  l(gamma s, s) <= sqrt(Tf/s) l(q,Tf)               *)
(* (FL9 (i), the L-integrand is nonnegative), and |gamma'(s)|^2 <= 3 l / s  *)
(* where FL9 (ii) gives differentiability and velocity grad l (FL8 with     *)
(* c -> 1, Cauchy-Schwarz).                                                  *)
(* ------------------------------------------------------------------------- *)

let P2BX_KSOL_LINT_NONNEG = prove
 (`!kappa top atlas (g:real->B->real^3^3) a p Tf gamma s.
     p2b_kappa_solution kappa (top,atlas) g /\ a < &0 /\ Tf <= --a /\
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p Tf gamma /\
     &0 <= s /\ s <= Tf
     ==> &0 <= p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                               (&0) gamma Tf s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2a_adm] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th))) THEN
  SUBGOAL_THEN `(gamma:real->B) s IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check
      (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace"))
                     (concl th) &&
                 can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vtop"))
                     (concl th) &&
                 not (can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in"))
                     (concl th)) &&
                 is_forall(concl th))) THEN
    ASM_REWRITE_TAC[P2BX_VIEW_PROJ; IN_REAL_INTERVAL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2a_L_integrand; P2BX_VIEW_PROJ] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC P2BX_MFD_SCALAR_NONNEG THEN EXISTS_TAC `top:B topology` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `mfd_sectional:((B->bool)#(B->real^3)->bool)->(B->real^3^3)->B->real^3->real^3->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* FL9 (i) and R >= 0: sqrt s l(gamma s, s) <= sqrt Tf l(gamma Tf, Tf). *)

let P2BX_FL9_LBOUND = prove
 (`!kappa top atlas (g:real->B->real^3^3) a p Tf gamma.
     p2b_kappa_solution kappa (top,atlas) g /\ a < &0 /\ &0 < Tf /\ Tf < --a /\
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p Tf gamma /\
     (!s. &0 < s /\ s <= Tf
          ==> &2 * sqrt s *
              p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p s (gamma s) =
              real_integral (real_interval[&0,s])
                (p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                                 (&0) gamma Tf))
     ==> !s. &0 < s /\ s <= Tf
             ==> sqrt s * p2b_klx (top,atlas) g p s (gamma s) <=
                 sqrt Tf * p2b_klx (top,atlas) g p Tf (gamma Tf)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I")))))) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2b_klx (top,atlas) (g:real->B->real^3^3) p s (gamma s) =
    p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p s (gamma s) /\
    p2b_klx (top,atlas) g p Tf (gamma Tf) =
    p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p Tf (gamma Tf)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "I" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "I" (MP_TAC o SPEC `Tf:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2a_adm] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th))) THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,s])
      (p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,&0])
                                      (g:real->B->real^3^3)) (&0) gamma Tf) <=
    real_integral (real_interval[&0,Tf])
      (p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) gamma Tf)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `Tf:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2BX_KSOL_LINT_NONNEG THEN
      MAP_EVERY EXISTS_TAC [`kappa:real`; `p:B`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* FL8 at a point of differentiability in the FL8 convention (chart_at q), *)
(* read with p2b_klx, for one c.                                            *)

let P2BX_FL8_AT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p q tau d1 cc.
     P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ q IN topspace top /\
     &0 < tau /\ &0 < cc /\ cc < &1 /\
     ((\z. lift(p2b_klx (top,atlas) g p (drop(fstcart z))
                 (chart_inv (chart_at atlas q) (sndcart z)))) has_derivative d1)
     (at (pastecart (lift tau) (SND(chart_at atlas q) q)))
     ==> lgrad2 (metric_local atlas (chart_at atlas q) (g(--tau)))
                (\y. p2b_klx (top,atlas) g p tau (chart_inv (chart_at atlas q) y))
                (SND(chart_at atlas q) q) +
         mfd_scalar atlas (g(--tau)) q
         <= (&1 + &2 / cc) * p2b_klx (top,atlas) g p tau q / tau`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL8") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `a = --(&2 * tau / (&1 - cc))` THEN
  SUBGOAL_THEN `a < &0 /\ tau < --a /\ tau <= (&1 - cc) * (&0 - a)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    SUBGOAL_THEN `&0 < &1 - cc` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - cc) * (tau / (&1 - cc)) = tau` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < tau / (&1 - cc)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < cc * (tau / (&1 - cc))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_SUB_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top:B topology,atlas) (real_interval[a,&0])
                    (g:real->B->real^3^3)` THEN
  SUBGOAL_THEN
   `((\z. lift(p2a_lx (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                         (real->B->real^3^3)) (&0) (p:B) (drop(fstcart z))
                 (chart_inv (chart_at atlas (q:B)) (sndcart z)))) has_derivative
     (d1:real^(1,3)finite_sum->real^1)) (at (pastecart (lift tau) (SND (chart_at atlas q) q)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. lift(p2b_klx (top,atlas) (g:real->B->real^3^3) p (drop(fstcart z))
                           (chart_inv (chart_at atlas (q:B)) (sndcart z)))` THEN
    EXISTS_TAC `min tau (--a - tau)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z':real^(1,3)finite_sum` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "V" THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN
    SUBGOAL_THEN `abs(drop(fstcart(z':real^(1,3)finite_sum)) - tau) <
                  min tau (--a - tau)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `dist(z':real^(1,3)finite_sum,
                       pastecart (lift tau)
                         (SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)) q))` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN] THEN REWRITE_TAC[dist] THEN
      MP_TAC(ISPEC `(z':real^(1,3)finite_sum) -
                    pastecart (lift tau)
                      (SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)) q)`
                   NORM_FSTCART) THEN
      REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART; NORM_1; DROP_SUB; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "FL8" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `a:real`; `&0`; `g:real->B->real^3^3`; `p:B`; `cc:real`] o
                  REWRITE_RULE[P2A_FLOW_PROP_9_9_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[DIMINDEX_3; LE_REFL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `mfd_sectional:((B->bool)#(B->real^3)->bool)->(B->real^3^3)->B->real^3->real^3->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`tau:real`; `q:B`; `d1:real^(1,3)finite_sum->real^1`]) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN
  SUBGOAL_THEN
   `!y. p2a_lx (p2a_flow_view (top:B topology,atlas) (real_interval[a,&0])
                 (g:real->B->real^3^3)) (&0) p tau y = p2b_klx (top,atlas) g p tau y`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LZERO] THEN SIMP_TAC[]);;

(* c -> 1. *)

let P2BX_FL8_AT_LIMIT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p q tau d1.
     P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ q IN topspace top /\
     &0 < tau /\
     ((\z. lift(p2b_klx (top,atlas) g p (drop(fstcart z))
                 (chart_inv (chart_at atlas q) (sndcart z)))) has_derivative d1)
     (at (pastecart (lift tau) (SND(chart_at atlas q) q)))
     ==> lgrad2 (metric_local atlas (chart_at atlas q) (g(--tau)))
                (\y. p2b_klx (top,atlas) g p tau (chart_inv (chart_at atlas q) y))
                (SND(chart_at atlas q) q) +
         mfd_scalar atlas (g(--tau)) q
         <= &3 * (p2b_klx (top,atlas) g p tau q / tau)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL8") (CONJUNCTS_THEN2 (LABEL_TAC "C910")
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[REAL_ARITH `&3 * x = (&1 + &2) * x`] THEN
  MATCH_MP_TAC P2BX_CC_LIMIT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                     `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:real->B->real^3^3`; `p:B`] o
                     REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`tau:real`; `q:B`] o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    REAL_ARITH_TAC;
    X_GEN_TAC `cc:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX_FL8_AT THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `d1:real^(1,3)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[]]);;

(* The velocity of an FL9 minimizer is bounded: |v|^2 <= 3 l / tau. *)

let P2BX_VEL_BOUND = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p q tau d1 v.
     P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ q IN topspace top /\
     &0 < tau /\
     ((\z. lift(p2b_klx (top,atlas) g p (drop(fstcart z))
                 (chart_inv (chart_at atlas q) (sndcart z)))) has_derivative d1)
     (at (pastecart (lift tau) (SND(chart_at atlas q) q))) /\
     ((\y. lift(p2b_klx (top,atlas) g p tau (chart_inv (chart_at atlas q) y))) has_derivative
      (\u. lift(v dot (g(--tau) q ** u)))) (at (SND(chart_at atlas q) q))
     ==> v dot (g(--tau) q ** v) <= &3 * (p2b_klx (top,atlas) g p tau q / tau)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL8") (CONJUNCTS_THEN2 (LABEL_TAC "C910")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `q:B`;
                 `tau:real`; `d1:real^(1,3)finite_sum->real^1`] P2BX_FL8_AT_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `q:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--tau))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_scalar atlas ((g:real->B->real^3^3) (--tau)) q` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_MFD_SCALAR_NONNEG THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `mfd_sectional:((B->bool)#(B->real^3)->bool)->(B->real^3^3)->B->real^3->real^3->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p2b_klx (top,atlas) (g:real->B->real^3^3) p tau q / tau` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                     `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:real->B->real^3^3`; `p:B`] o
                     REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`tau:real`; `q:B`] o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                  (metric_local atlas c ((g:real->B->real^3^3) (--tau)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (--tau))
                  (SND c q) = g(--tau) q` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot ((g:real->B->real^3^3) (--tau) q ** v)` ASSUME_TAC THENL
   [ASM_CASES_TAC `v:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
    UNDISCH_TAC `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                   (metric_local atlas c ((g:real->B->real^3^3) (--tau)))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND (c:(B->bool)#(B->real^3)) q` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)`;
                 `metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (--tau))`;
                 `\y. p2b_klx (top,atlas) (g:real->B->real^3^3) p tau
                        (chart_inv (c:(B->bool)#(B->real^3)) y)`;
                 `SND (c:(B->bool)#(B->real^3)) q`; `v:real^3`] P2BX_LGRAD2_CS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\u. lift(v dot ((g:real->B->real^3^3) (--tau) q ** u))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th) &&
    can (find_term ((=) `v:real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  ABBREV_TAC `Q = v dot ((g:real->B->real^3^3) (--tau) q ** v)` THEN
  ABBREV_TAC `L2 = lgrad2 (metric_local atlas (c:(B->bool)#(B->real^3))
                            ((g:real->B->real^3^3) (--tau)))
                          (\y. p2b_klx (top,atlas) g p tau (chart_inv c y)) (SND c q)` THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `Q = &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Q <= L2` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x y. x * Q <= y * Q /\ (x * Q <= y * Q ==> x <= y) ==> x <= y`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `L2 + mfd_scalar atlas ((g:real->B->real^3^3) (--tau)) q <=
               &3 * (p2b_klx (top,atlas) g p tau q / tau)` THEN
  UNDISCH_TAC `&0 <= mfd_scalar atlas ((g:real->B->real^3^3) (--tau)) q` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The two minimizers of FL9, read with p2b_klx: continuous                  *)
(* curves from p, l(gamma s, s) <= sqrt(T/s) l(q,T), and a chart velocity   *)
(* with |v|^2 <= 3 l / s at every interior time.                            *)
(* ------------------------------------------------------------------------- *)

let P2BX_KLX_DERIV_FROM_VIEW = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) p a
    (c:(B->bool)#(B->real^3)) tau (y0:real^3) d1.
     &0 < tau /\ tau < --a /\
     ((\z. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p
                 (drop(fstcart z)) (chart_inv c (sndcart z)))) has_derivative d1)
     (at (pastecart (lift tau) y0))
     ==> ((\z. lift(p2b_klx (top,atlas) g p (drop(fstcart z)) (chart_inv c (sndcart z))))
          has_derivative d1) (at (pastecart (lift tau) y0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\z. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0])
                                (g:real->B->real^3^3)) (&0) p (drop(fstcart z))
                         (chart_inv (c:(B->bool)#(B->real^3)) (sndcart z)))` THEN
  EXISTS_TAC `min tau (--a - tau)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z':real^(1,3)finite_sum` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN
  SUBGOAL_THEN `abs(drop(fstcart(z':real^(1,3)finite_sum)) - tau) < min tau (--a - tau)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(z':real^(1,3)finite_sum,pastecart (lift tau) (y0:real^3))` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN REWRITE_TAC[dist] THEN
    MP_TAC(ISPEC `(z':real^(1,3)finite_sum) - pastecart (lift tau) (y0:real^3)`
                 NORM_FSTCART) THEN
    REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART; NORM_1; DROP_SUB; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BX_L925_CURVE = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p Tf q.
     P2A_FLOW_MIN_GRAD_STATEMENT w (:3) /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ q IN topspace top /\
     &0 < Tf
     ==> ?gamma. gamma(&0) = p /\ gamma Tf = q /\
                 (!s. &0 <= s /\ s <= Tf ==> gamma s IN topspace top) /\
                 (!s0 O. &0 <= s0 /\ s0 <= Tf /\ open_in top O /\ gamma s0 IN O
                         ==> ?d. &0 < d /\
                                 !s. &0 <= s /\ s <= Tf /\ abs(s - s0) < d ==> gamma s IN O) /\
                 (!s. &0 < s /\ s <= Tf
                      ==> sqrt s * p2b_klx (top,atlas) g p s (gamma s) <=
                          sqrt Tf * p2b_klx (top,atlas) g p Tf q) /\
                 (!s. &0 < s /\ s < Tf
                      ==> ?v. ((\r. SND(chart_at atlas (gamma s)) (gamma(drop r)))
                               has_vector_derivative v) (at (lift s)) /\
                              v dot (g(--s) (gamma s) ** v) <=
                              &3 * (p2b_klx (top,atlas) g p s (gamma s) / s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL9") (CONJUNCTS_THEN2 (LABEL_TAC "FL8")
    (CONJUNCTS_THEN2 (LABEL_TAC "C910") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  USE_THEN "FL9" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `--(Tf + &1)`; `&0`; `g:real->B->real^3^3`; `p:B`;
                                  `Tf:real`; `q:B`] o
                  REWRITE_RULE[P2A_FLOW_MIN_GRAD_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "I") (LABEL_TAC "II"))))) THEN
  EXISTS_TAC `gamma:real->B` THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[--(Tf + &1),&0])
                           (g:real->B->real^3^3)) (&0) p Tf gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2a_adm] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th))) THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= Tf ==> (gamma:real->B) s IN topspace top`
  (LABEL_TAC "TS") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check
      (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace"))
                     (concl th) &&
                 can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vtop"))
                     (concl th) &&
                 not (can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in"))
                     (concl th)) &&
                 is_forall(concl th))) THEN
    ASM_REWRITE_TAC[P2BX_VIEW_PROJ; IN_REAL_INTERVAL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s0:real`; `O:B->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `O:B->bool`] o check
      (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in"))
                     (concl th) &&
                 can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vtop"))
                     (concl th) &&
                 is_forall(concl th))) THEN
    ASM_REWRITE_TAC[P2BX_VIEW_PROJ; IN_REAL_INTERVAL] THEN
    COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `--(Tf + &1)`; `p:B`; `Tf:real`; `gamma:real->B`]
                  P2BX_FL9_LBOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "II" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d1:real^(1,3)finite_sum->real^1`)
      (X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
    REWRITE_TAC[REAL_SUB_LZERO] THEN DISCH_TAC THEN
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gamma:real->B) s IN topspace top` ASSUME_TAC THENL
     [USE_THEN "TS" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. p2a_lx (p2a_flow_view (top,atlas) (real_interval[--(Tf + &1),&0])
                   (g:real->B->real^3^3)) (&0) p s y = p2b_klx (top,atlas) g p s y`
    (LABEL_TAC "KV") THENL
     [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `metric_local atlas (chart_at atlas ((gamma:real->B) s))
                    ((g:real->B->real^3^3) (--s)) (SND (chart_at atlas (gamma s)) (gamma s)) =
                  g(--s) (gamma s)` ASSUME_TAC THENL
     [MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BX_VEL_BOUND THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `d1:real^(1,3)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_KLX_DERIV_FROM_VIEW THEN EXISTS_TAC `--(Tf + &1)` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th) &&
      can (find_term ((=) `v:real^3`)) (concl th))) THEN
    USE_THEN "KV" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The steps for f(s) = d_{g(-s)}(gamma1 s, gamma2 s): the                   *)
(* Ricci bound on balls (Cor 9.10), the right Dini step (DIST_LOCAL and     *)
(* moving points), lower semicontinuity from the left (short-time metric     *)
(* comparison), and small values of f near s = 0.                           *)
(* ------------------------------------------------------------------------- *)

let P2BX_QF_NONNEG = prove
 (`!top atlas (g:A->real^N^N) x v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &0 <= v dot (g x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] RIEMANNIAN_METRIC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The Ricci curvature on a ball of g(-s): Ric <= R g <= (3 / s) B^2 g with *)
(* B = L + sqrt(3/(4s)) r0, L >= sqrt l at the centre (Cor 9.10).           *)

let P2BX_BALL_RIC_BOUND = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p s x0 r0 L y u.
     P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ &0 < s /\
     x0 IN topspace top /\ &0 < r0 /\ sqrt(p2b_klx (top,atlas) g p s x0) <= L /\
     y IN mfd_ball (top,atlas) (g(--s)) x0 r0
     ==> mfd_ricci atlas (g(--s)) y u u <=
         (&3 / s * (L + sqrt(&3 / (&4 * s)) * r0) pow 2) * (u dot (g(--s) y ** u))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (--s)) x0 r0` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--s))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `g:real->B->real^3^3`; `p:B`] o
                   REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PT") (CONJUNCTS_THEN2 (LABEL_TAC "SP") (K ALL_TAC))) THEN
  USE_THEN "PT" (MP_TAC o SPECL [`s:real`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "SP" (MP_TAC o SPECL [`s:real`; `x0:B`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&3 / (&4 * s))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p s y) <=
                L + sqrt(&3 / (&4 * s)) * r0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p s x0) +
                sqrt(&3 / (&4 * s)) * mfd_dist (top,atlas) (g(--s)) x0 y` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c d. a <= b /\ c <= d ==> a + c <= b + d`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `B = L + sqrt(&3 / (&4 * s)) * r0` THEN
  SUBGOAL_THEN `p2b_klx (top,atlas) (g:real->B->real^3^3) p s y <= B pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p s y) pow 2` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) (--s)) y <= &3 / s * B pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 * p2b_klx (top,atlas) (g:real->B->real^3^3) p s y / s` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--s)`; `y:B`; `u:real^3`] P2BX_MFD_RICCI_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `mfd_sectional:((B->bool)#(B->real^3)->bool)->(B->real^3^3)->B->real^3->real^3->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--s)`; `y:B`; `u:real^3`] P2BX_QF_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c. b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* The right Dini step: DIST_LOCAL at the two points, then the two moving   *)
(* points and the triangle inequality.                                      *)

let P2BX_L925_RIGHT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) gamma1 gamma2 s v1 v2 K r0 e.
     P2B_REQ_RFA_DIST_LOCAL_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < s /\
     gamma1 s IN topspace top /\ gamma2 s IN topspace top /\
     (!O. open_in top O /\ gamma1 s IN O
          ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma1(s + h) IN O) /\
     (!O. open_in top O /\ gamma2 s IN O
          ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma2(s + h) IN O) /\
     ((\r. SND(chart_at atlas (gamma1 s)) (gamma1(drop r))) has_vector_derivative v1)
     (at (lift s)) /\
     ((\r. SND(chart_at atlas (gamma2 s)) (gamma2(drop r))) has_vector_derivative v2)
     (at (lift s)) /\
     &0 <= K /\ &0 < r0 /\
     (!y u. y IN mfd_ball (top,atlas) (g(--s)) (gamma1 s) r0 UNION
              mfd_ball (top,atlas) (g(--s)) (gamma2 s) r0
            ==> mfd_ricci atlas (g(--s)) y u u <= &2 * K * (u dot (g(--s) y ** u))) /\
     &0 < e
     ==> ?d. &0 < d /\
             !h. &0 < h /\ h < d
                 ==> mfd_dist (top,atlas) (g(--(s + h))) (gamma1(s + h)) (gamma2(s + h)) <=
                     mfd_dist (top,atlas) (g(--s)) (gamma1 s) (gamma2 s) +
                     h * (&4 * (K * r0 + inv r0) + sqrt(v1 dot (g(--s) (gamma1 s) ** v1)) +
                          sqrt(v2 dot (g(--s) (gamma2 s) ** v2)) + e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "DL") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "RC1") (CONJUNCTS_THEN2 (LABEL_TAC "RC2")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "RIC") ASSUME_TAC)))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (--(s + &1)) (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(s + &1)) (&0) (g:real->B->real^3^3)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[p2a_cbflow; ricci_flow_from]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) ((g:real->B->real^3^3) (--s))` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "DL" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                 `--(s + &1)`; `&0`; `g:real->B->real^3^3`; `--s`;
                                 `(gamma1:real->B) s`; `(gamma2:real->B) s`; `K:real`;
                                 `r0:real`] o
                 REWRITE_RULE[P2B_REQ_RFA_DIST_LOCAL_STATEMENT]) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `3 - 1 = 2`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `gamma1:real->B`; `s:real`; `v1:real^3`; `e / &3`]
                P2BX_MOVE_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M1"))) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `gamma2:real->B`; `s:real`; `v2:real^3`; `e / &3`]
                P2BX_MOVE_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M2"))) THEN
  USE_THEN "RC1" (MP_TAC o SPEC `topspace top:B->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1"))) THEN
  USE_THEN "RC2" (MP_TAC o SPEC `topspace top:B->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T2"))) THEN
  EXISTS_TAC `min d1 (min d2 (min d3 (min d4 d5)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  USE_THEN "D1" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `--s - h = --(s + h)`] THEN DISCH_TAC THEN
  USE_THEN "M1" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "M2" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "T1" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "T2" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--(s + h)))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:B. x IN topspace top /\ y IN topspace top
                        ==> mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--(s + h))`; `(gamma1:real->B) (s + h)`;
                 `(gamma1:real->B) s`; `(gamma2:real->B) (s + h)`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--(s + h))`; `(gamma1:real->B) s`;
                 `(gamma2:real->B) s`; `(gamma2:real->B) (s + h)`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--(s + h))`; `(gamma1:real->B) (s + h)`;
                 `(gamma1:real->B) s`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (--(s + h))) (gamma1 s) (gamma2 s) <=
               mfd_dist (top,atlas) (g(--s)) (gamma1 s) (gamma2 s) +
               h * (&2 * &2 * (K * r0 + inv r0) + e / &3)` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (--(s + h))) (gamma1 s)
                 (gamma1(s + h)) <= h * (sqrt(v1 dot (g(--s) (gamma1 s) ** v1)) + e / &3)` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (--(s + h))) (gamma2 s)
                 (gamma2(s + h)) <= h * (sqrt(v2 dot (g(--s) (gamma2 s) ** v2)) + e / &3)` THEN
  REAL_ARITH_TAC);;

(* Lower semicontinuity from the left: the short-time comparison and the   *)
(* continuity of the curves at s.                                           *)

let P2BX_L925_LEFT = prove
 (`!kappa top atlas (g:real->B->real^3^3) gamma1 gamma2 s e.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < s /\
     gamma1 s IN topspace top /\ gamma2 s IN topspace top /\
     (!O. open_in top O /\ gamma1 s IN O
          ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma1(s - h) IN O) /\
     (!O. open_in top O /\ gamma2 s IN O
          ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma2(s - h) IN O) /\
     &0 < e
     ==> ?d. &0 < d /\
             !h. &0 < h /\ h < d
                 ==> mfd_dist (top,atlas) (g(--s)) (gamma1 s) (gamma2 s) <=
                     mfd_dist (top,atlas) (g(--(s - h))) (gamma1(s - h)) (gamma2(s - h)) + e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "LC1") (CONJUNCTS_THEN2 (LABEL_TAC "LC2") ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `s:real`] P2BX_KSOL_DIST_EQUIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQV"))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--s))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:B. x IN topspace top /\ y IN topspace top
                        ==> mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D0 = mfd_dist (top,atlas) ((g:real->B->real^3^3) (--s)) (gamma1 s) (gamma2 s)` THEN
  SUBGOAL_THEN `&0 <= D0` ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ep = e / &4` THEN
  SUBGOAL_THEN `&0 < ep` ASSUME_TAC THENL [EXPAND_TAC "ep" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--s)`; `(gamma1:real->B) s`; `ep:real`]
                GRGD_DIST_SMALL_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--s)`; `(gamma2:real->B) s`; `ep:real`]
                GRGD_DIST_SMALL_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T2:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N2")))) THEN
  USE_THEN "LC1" (MP_TAC o SPEC `T1:B->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W1"))) THEN
  USE_THEN "LC2" (MP_TAC o SPEC `T2:B->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W2"))) THEN
  ABBREV_TAC `M = C * (D0 + &2 * ep) + C + &1` THEN
  SUBGOAL_THEN `&0 < M /\ C <= M /\ C * (D0 + &2 * ep) <= M` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= C * (D0 + &2 * ep)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (s / &2) (min d1 (min d2 (min (inv(&2 * M)) (ep / M))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  USE_THEN "W1" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "W2" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "N1" (MP_TAC o SPEC `(gamma1:real->B) (s - h)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "N2" (MP_TAC o SPEC `(gamma2:real->B) (s - h)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->B) (s - h) IN topspace top /\ (gamma2:real->B) (s - h) IN topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  ABBREV_TAC `X = mfd_dist (top,atlas) ((g:real->B->real^3^3) (--s)) (gamma1(s - h))
                    (gamma2(s - h))` THEN
  ABBREV_TAC `Y = mfd_dist (top,atlas) ((g:real->B->real^3^3) (--(s - h))) (gamma1(s - h))
                    (gamma2(s - h))` THEN
  ABBREV_TAC `E = exp(C * h)` THEN
  SUBGOAL_THEN `X <= E * Y` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"; "E"] THEN USE_THEN "EQV" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Y <= X` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN MATCH_MP_TAC P2BX_KSOL_DIST_MONO THEN
    EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun (x,y,z) ->
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (--s)`; x; y; z] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC])
   [`(gamma1:real->B) s`,`(gamma1:real->B) (s - h)`,`(gamma2:real->B) s`;
    `(gamma1:real->B) (s - h)`,`(gamma2:real->B) (s - h)`,`(gamma2:real->B) s`;
    `(gamma1:real->B) (s - h)`,`(gamma1:real->B) s`,`(gamma2:real->B) (s - h)`;
    `(gamma1:real->B) s`,`(gamma2:real->B) s`,`(gamma2:real->B) (s - h)`] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--s)`; `(gamma1:real->B) (s - h)`; `(gamma1:real->B) s`]
                MFD_DIST_SYM) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--s)`; `(gamma2:real->B) (s - h)`; `(gamma2:real->B) s`]
                MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= C * h /\ C * h <= inv(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * h` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h * (&2 * M) < &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `inv(&2 * M) * (&2 * M)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `E <= &1 + &2 * (C * h) /\ &1 <= E` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REWRITE_TAC[];
      MP_TAC(SPEC `C * h` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * M <= ep` ASSUME_TAC THENL
   [SUBGOAL_THEN `h * M < ep` MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`h:real`; `ep:real`; `M:real`] REAL_LT_RDIV_EQ) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `X <= &2 * ep + D0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(E - &1) * Y <= (E - &1) * X /\
    (E - &1) * X <= (E - &1) * (&2 * ep + D0) /\
    (E - &1) * (&2 * ep + D0) <= (&2 * (C * h)) * (&2 * ep + D0) /\
    h * (C * (D0 + &2 * ep)) <= h * M`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* f is small near s = 0: both curves start at p, and the distances of     *)
(* g(-t0) are at most those of g(-T) for t0 <= T.                           *)

let P2BX_L925_START = prove
 (`!kappa top atlas (g:real->B->real^3^3) gamma1 gamma2 p Tf e.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < Tf /\ p IN topspace top /\
     gamma1(&0) = p /\ gamma2(&0) = p /\
     (!s. &0 <= s /\ s <= Tf ==> gamma1 s IN topspace top /\ gamma2 s IN topspace top) /\
     (!O. open_in top O /\ p IN O
          ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= Tf /\ abs(s - &0) < d ==> gamma1 s IN O) /\
     (!O. open_in top O /\ p IN O
          ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= Tf /\ abs(s - &0) < d ==> gamma2 s IN O) /\
     &0 < e
     ==> ?t0. &0 < t0 /\ t0 < Tf /\
              mfd_dist (top,atlas) (g(--t0)) (gamma1 t0) (gamma2 t0) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TS") (CONJUNCTS_THEN2 (LABEL_TAC "C1")
    (CONJUNCTS_THEN2 (LABEL_TAC "C2") ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--Tf))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--Tf)`; `p:B`; `e / &2`] GRGD_DIST_SMALL_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N")))) THEN
  USE_THEN "C1" (MP_TAC o SPEC `T0:B->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W1"))) THEN
  USE_THEN "C2" (MP_TAC o SPEC `T0:B->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W2"))) THEN
  ABBREV_TAC `t0 = min (Tf / &2) (min d1 d2) / &2` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < Tf /\ t0 < d1 /\ t0 < d2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "W1" (MP_TAC o SPEC `t0:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "W2" (MP_TAC o SPEC `t0:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "N" (MP_TAC o SPEC `(gamma1:real->B) t0`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "N" (MP_TAC o SPEC `(gamma2:real->B) t0`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "TS" (MP_TAC o SPEC `t0:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (--Tf)) ((gamma1:real->B) t0)
                ((gamma2:real->B) t0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_KSOL_DIST_MONO THEN EXISTS_TAC `kappa:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (--Tf)) ((gamma1:real->B) t0) p +
              mfd_dist (top,atlas) (g(--Tf)) p ((gamma2:real->B) t0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(gamma1:real->B) t0`; `p:B`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (--Tf)`; `(gamma1:real->B) t0`; `p:B`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

(* The arithmetic of the rates: sg = s^(1/4), th = T^(1/4), lm = Lambda^(1/2). *)

let P2BX_RATE_L925 = prove
 (`!sg th lm l1 l2 V1 V2 r0 K.
     &0 < sg /\ sg <= th /\ &1 <= lm /\ &0 <= l1 /\ &0 <= l2 /\
     sg pow 2 * l1 <= th pow 2 * lm pow 2 /\ sg pow 2 * l2 <= th pow 2 * lm pow 2 /\
     &0 <= V1 /\ &0 <= V2 /\ V1 pow 2 <= &3 * (l1 / sg pow 4) /\
     V2 pow 2 <= &3 * (l2 / sg pow 4) /\
     r0 = sg pow 3 / (th * lm) /\ K = &6 * th pow 2 * lm pow 2 / sg pow 6
     ==> &0 < r0 /\ &0 <= K /\
         sqrt l1 <= (th * lm) / sg /\ sqrt l2 <= (th * lm) / sg /\
         &3 / sg pow 4 * ((th * lm) / sg + sqrt(&3 / (&4 * sg pow 4)) * r0) pow 2 <= &2 * K /\
         &4 * (K * r0 + inv r0) + V1 + V2 <= &32 * ((th * lm) / sg pow 3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))))))))))) THEN
  SUBGOAL_THEN `&0 < th /\ &0 < lm` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sg pow 2 /\ &0 < sg pow 3 /\ &0 < sg pow 4 /\ &0 < th * lm`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (th * lm) / sg` ASSUME_TAC THENL
   [SIMP_TAC[REAL_LE_RDIV_EQ; ASSUME `&0 < sg`] THEN REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `!sg th lm. sg <= th /\ th * &1 <= th * lm ==> sg <= th * lm`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sg pow 3 / (th * lm)) * ((th * lm) / sg) = sg pow 2 /\
    inv(sg pow 3 / (th * lm)) = (th * lm) / sg pow 3 /\
    (&6 * th pow 2 * lm pow 2 / sg pow 6) * (sg pow 3 / (th * lm)) =
    &6 * ((th * lm) / sg pow 3) /\
    &6 * th pow 2 * lm pow 2 / sg pow 6 = &6 * ((th * lm) / sg) pow 2 / sg pow 4 /\
    (th * lm) / sg pow 3 = ((th * lm) / sg) / sg pow 2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < sg` THEN UNDISCH_TAC `&0 < th` THEN UNDISCH_TAC `&0 < lm` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = (th * lm) / sg` THEN
  ABBREV_TAC `ww = u / sg pow 2` THEN
  ABBREV_TAC `r = sg pow 3 / (th * lm)` THEN
  SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ &0 < ww` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "ww"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* l_i <= u^2 and the square roots *)
  SUBGOAL_THEN `l1 <= u pow 2 /\ l2 <= u pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `u pow 2 = (th pow 2 * lm pow 2) / sg pow 2` SUBST1_TAC THENL
     [EXPAND_TAC "u" THEN UNDISCH_TAC `&0 < sg` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the Ricci constant *)
    SUBGOAL_THEN `sqrt(&3 / (&4 * sg pow 4)) <= inv(sg pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN
      SUBGOAL_THEN `&0 < &4 * sg pow 4` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `inv(sg pow 2) pow 2 = &4 / (&4 * sg pow 4)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sg` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(&3 / (&4 * sg pow 4))` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(sg pow 2) * r = inv u` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["r"; "u"] THEN
      UNDISCH_TAC `&0 < sg` THEN UNDISCH_TAC `&0 < th` THEN UNDISCH_TAC `&0 < lm` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv u <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&3 / (&4 * sg pow 4)) * r <= inv(sg pow 2) * r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(&3 / (&4 * sg pow 4)) * r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / sg pow 4 * (&2 * u) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sg` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* the rate *)
  SUBGOAL_THEN `&3 * (l1 / sg pow 4) <= &3 * ww pow 2 /\ &3 * (l2 / sg pow 4) <= &3 * ww pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ww pow 2 = u pow 2 / sg pow 4` SUBST1_TAC THENL
     [EXPAND_TAC "ww" THEN UNDISCH_TAC `&0 < sg` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `V1 <= &2 * ww /\ V2 <= &2 * ww` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(&2 * ww) pow 2 < V1 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC];
      SUBGOAL_THEN `(&2 * ww) pow 2 < V2 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC]] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(SPEC `ww:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The assembly.  With th = T^(1/4), lm = Lambda^(1/2) and                   *)
(* F(s) = 128 th lm s^(1/4), the function f - F satisfies the hypotheses of *)
(* P2BX_DINI_MONO on [t0,T]; with f(t0) -> 0 this gives                     *)
(* d_{g(-T)}(p1,q1) <= 128 sqrt T sqrt Lambda, hence Lemma 9.25 with        *)
(* c1 = 1/16384.                                                             *)
(* ------------------------------------------------------------------------- *)

(* One-sided continuity at interior times from continuity on [0,T]. *)

let P2BX_CONT_SIDES = prove
 (`!top (gamma:real->B) Tf s.
     (!s0 O. &0 <= s0 /\ s0 <= Tf /\ open_in top O /\ gamma s0 IN O
             ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= Tf /\ abs(s - s0) < d ==> gamma s IN O) /\
     &0 < s /\ s <= Tf
     ==> (s < Tf
          ==> !O. open_in top O /\ gamma s IN O
                  ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma(s + h) IN O) /\
         (!O. open_in top O /\ gamma s IN O
              ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma(s - h) IN O)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C") STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `O:B->bool` THEN STRIP_TAC THEN
    USE_THEN "C" (MP_TAC o SPECL [`s:real`; `O:B->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (Tf - s)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `O:B->bool` THEN STRIP_TAC THEN
    USE_THEN "C" (MP_TAC o SPECL [`s:real`; `O:B->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d s` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The comparison function and its derivative. *)

let P2BX_QRT_SCALED_DERIV = prove
 (`!A s. &0 < s
         ==> ((\x. &4 * A * sqrt(sqrt x)) has_real_derivative
              A * inv(sqrt(sqrt s) pow 3)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. sqrt(sqrt x)`; `inv(&4 * sqrt(sqrt s) pow 3)`; `&4 * A`; `s:real`]
                HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  ASM_SIMP_TAC[P2BX_QRT_DERIV] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(sqrt s) pow 3` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* The right Dini bound for f - F at an interior time s. *)

let P2BX_L925_PHI_RIGHT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p gamma1 gamma2 s Tf lm v1 v2 e.
     P2B_REQ_RFA_DIST_LOCAL_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\
     &0 < s /\ s <= Tf /\ &1 <= lm /\
     gamma1 s IN topspace top /\ gamma2 s IN topspace top /\
     (!O. open_in top O /\ gamma1 s IN O
          ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma1(s + h) IN O) /\
     (!O. open_in top O /\ gamma2 s IN O
          ==> ?d. &0 < d /\ !h. &0 < h /\ h < d ==> gamma2(s + h) IN O) /\
     ((\r. SND(chart_at atlas (gamma1 s)) (gamma1(drop r))) has_vector_derivative v1)
     (at (lift s)) /\
     ((\r. SND(chart_at atlas (gamma2 s)) (gamma2(drop r))) has_vector_derivative v2)
     (at (lift s)) /\
     v1 dot (g(--s) (gamma1 s) ** v1) <= &3 * (p2b_klx (top,atlas) g p s (gamma1 s) / s) /\
     v2 dot (g(--s) (gamma2 s) ** v2) <= &3 * (p2b_klx (top,atlas) g p s (gamma2 s) / s) /\
     sqrt s * p2b_klx (top,atlas) g p s (gamma1 s) <= sqrt Tf * lm pow 2 /\
     sqrt s * p2b_klx (top,atlas) g p s (gamma2 s) <= sqrt Tf * lm pow 2 /\
     &0 < e
     ==> ?d. &0 < d /\
             !h. &0 < h /\ h < d
                 ==> mfd_dist (top,atlas) (g(--(s + h))) (gamma1(s + h)) (gamma2(s + h)) -
                     &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt(s + h)) <=
                     (mfd_dist (top,atlas) (g(--s)) (gamma1 s) (gamma2 s) -
                      &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt s)) + e * h`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "DL") (CONJUNCTS_THEN2 (LABEL_TAC "C910")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--s))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* fourth roots *)
  SUBGOAL_THEN `&0 < sqrt(sqrt s) /\ sqrt(sqrt s) pow 2 = sqrt s /\ sqrt(sqrt s) pow 4 = s /\
                &0 < sqrt(sqrt Tf) /\ sqrt(sqrt Tf) pow 2 = sqrt Tf /\
                sqrt(sqrt s) <= sqrt(sqrt Tf)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt s /\ &0 < sqrt Tf` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `sg = sqrt(sqrt s)` THEN ABBREV_TAC `th = sqrt(sqrt Tf)` THEN
  (* the reduced lengths and speeds *)
  ABBREV_TAC `l1 = p2b_klx (top,atlas) (g:real->B->real^3^3) p s (gamma1 s)` THEN
  ABBREV_TAC `l2 = p2b_klx (top,atlas) (g:real->B->real^3^3) p s (gamma2 s)` THEN
  SUBGOAL_THEN `&0 <= l1 /\ &0 <= l2` STRIP_ASSUME_TAC THENL
   [USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                     `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:real->B->real^3^3`; `p:B`] o
                     REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`s:real`; `(gamma1:real->B) s`] th) THEN
                         MP_TAC(SPECL [`s:real`; `(gamma2:real->B) s`] th)) THEN
    MAP_EVERY EXPAND_TAC ["l1"; "l2"] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v1 dot ((g:real->B->real^3^3) (--s) (gamma1 s) ** v1) /\
                &0 <= v2 dot ((g:real->B->real^3^3) (--s) (gamma2 s) ** v2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BX_QF_NONNEG THEN MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sqrt(v1 dot ((g:real->B->real^3^3) (--s) (gamma1 s) ** v1)) /\
    &0 <= sqrt(v2 dot ((g:real->B->real^3^3) (--s) (gamma2 s) ** v2)) /\
    sqrt(v1 dot ((g:real->B->real^3^3) (--s) (gamma1 s) ** v1)) pow 2 <= &3 * (l1 / sg pow 4) /\
    sqrt(v2 dot ((g:real->B->real^3^3) (--s) (gamma2 s) ** v2)) pow 2 <= &3 * (l2 / sg pow 4)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `V1 = sqrt(v1 dot ((g:real->B->real^3^3) (--s) (gamma1 s) ** v1))` THEN
  ABBREV_TAC `V2 = sqrt(v2 dot ((g:real->B->real^3^3) (--s) (gamma2 s) ** v2))` THEN
  MP_TAC(ISPECL [`sg:real`; `th:real`; `lm:real`; `l1:real`; `l2:real`; `V1:real`; `V2:real`;
                 `sg pow 3 / (th * lm)`; `&6 * th pow 2 * lm pow 2 / sg pow 6`]
                P2BX_RATE_L925) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `sqrt Tf`)) (concl th) &&
      can (find_term ((=) `lm pow 2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r0 = sg pow 3 / (th * lm)` THEN
  ABBREV_TAC `K = &6 * th pow 2 * lm pow 2 / sg pow 6` THEN
  STRIP_TAC THEN
  (* the Ricci bound on the two balls *)
  SUBGOAL_THEN
   `!y u. y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (--s)) (gamma1 s) r0 UNION
            mfd_ball (top,atlas) (g(--s)) (gamma2 s) r0
          ==> mfd_ricci atlas (g(--s)) y u u <= &2 * K * (u dot (g(--s) y ** u))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:B`; `u:real^3`] THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                     `s:real`; `(gamma1:real->B) s`; `r0:real`; `(th * lm) / sg`; `y:B`;
                     `u:real^3`] P2BX_BALL_RIC_BOUND);
      MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                     `s:real`; `(gamma2:real->B) s`; `r0:real`; `(th * lm) / sg`; `y:B`;
                     `u:real^3`] P2BX_BALL_RIC_BOUND)] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c. b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    (CONJ_TAC THENL
      [UNDISCH_TAC `&3 / sg pow 4 * ((th * lm) / sg + sqrt (&3 / (&4 * sg pow 4)) * r0) pow 2 <=
                    &2 * K` THEN
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC];
       MATCH_MP_TAC P2BX_QF_NONNEG THEN MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
       ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_ball; IN_ELIM_THM; MFD_JOINABLE_IN_TOPSPACE]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                 `gamma1:real->B`; `gamma2:real->B`; `s:real`; `v1:real^3`; `v2:real^3`;
                 `K:real`; `r0:real`; `e / &2`] P2BX_L925_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1"))) THEN
  MP_TAC(ISPECL [`\x. &4 * (&32 * th * lm) * sqrt(sqrt x)`;
                 `(&32 * th * lm) * inv(sg pow 3)`; `s:real`; `e / &2`] P2BX_DERIV_RIGHT_LOWER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "sg" THEN MATCH_MP_TAC P2BX_QRT_SCALED_DERIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2"))) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  USE_THEN "R1" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "R2" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&32 * th * lm) * inv(sg pow 3) = &32 * ((th * lm) / sg pow 3)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * (&4 * (K * r0 + inv r0) + V1 + V2) <= h * (&32 * ((th * lm) / sg pow 3))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `sqrt(sqrt s) = sg`] THEN REAL_ARITH_TAC);;

(* The Dini integration of f - F on [t0,T]. *)

let P2BX_L925_MONO = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p Tf lm gamma1 gamma2 t0.
     P2B_REQ_RFA_DIST_LOCAL_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ &0 < Tf /\ &1 <= lm /\
     (!s. &0 <= s /\ s <= Tf ==> gamma1 s IN topspace top) /\
     (!s. &0 <= s /\ s <= Tf ==> gamma2 s IN topspace top) /\
     (!s0 O. &0 <= s0 /\ s0 <= Tf /\ open_in top O /\ gamma1 s0 IN O
             ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= Tf /\ abs(s - s0) < d ==> gamma1 s IN O) /\
     (!s0 O. &0 <= s0 /\ s0 <= Tf /\ open_in top O /\ gamma2 s0 IN O
             ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= Tf /\ abs(s - s0) < d ==> gamma2 s IN O) /\
     (!s. &0 < s /\ s <= Tf
          ==> sqrt s * p2b_klx (top,atlas) g p s (gamma1 s) <= sqrt Tf * lm pow 2) /\
     (!s. &0 < s /\ s <= Tf
          ==> sqrt s * p2b_klx (top,atlas) g p s (gamma2 s) <= sqrt Tf * lm pow 2) /\
     (!s. &0 < s /\ s < Tf
          ==> ?v. ((\r. SND(chart_at atlas (gamma1 s)) (gamma1(drop r)))
                   has_vector_derivative v) (at (lift s)) /\
                  v dot (g(--s) (gamma1 s) ** v) <=
                  &3 * (p2b_klx (top,atlas) g p s (gamma1 s) / s)) /\
     (!s. &0 < s /\ s < Tf
          ==> ?v. ((\r. SND(chart_at atlas (gamma2 s)) (gamma2(drop r)))
                   has_vector_derivative v) (at (lift s)) /\
                  v dot (g(--s) (gamma2 s) ** v) <=
                  &3 * (p2b_klx (top,atlas) g p s (gamma2 s) / s)) /\
     &0 < t0 /\ t0 < Tf
     ==> mfd_dist (top,atlas) (g(--Tf)) (gamma1 Tf) (gamma2 Tf) -
         &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt Tf) <=
         mfd_dist (top,atlas) (g(--t0)) (gamma1 t0) (gamma2 t0) -
         &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt t0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "DL") (CONJUNCTS_THEN2 (LABEL_TAC "C910")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TS1") (CONJUNCTS_THEN2 (LABEL_TAC "TS2")
    (CONJUNCTS_THEN2 (LABEL_TAC "CO1") (CONJUNCTS_THEN2 (LABEL_TAC "CO2")
    (CONJUNCTS_THEN2 (LABEL_TAC "LB1") (CONJUNCTS_THEN2 (LABEL_TAC "LB2")
    (CONJUNCTS_THEN2 (LABEL_TAC "VE1") (CONJUNCTS_THEN2 (LABEL_TAC "VE2")
    STRIP_ASSUME_TAC)))))))))))))) THEN
  SUBGOAL_THEN `&0 <= &4 * (&32 * sqrt(sqrt Tf) * lm)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. mfd_dist (top,atlas) ((g:real->B->real^3^3) (--s)) ((gamma1:real->B) s)
                        ((gamma2:real->B) s) -
                      &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt s)`;
                 `t0:real`; `Tf:real`] P2BX_DINI_MONO) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `e:real`] THEN STRIP_TAC THEN
    USE_THEN "VE1" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "VE2" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v2:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `gamma1:real->B`; `Tf:real`; `s:real`] P2BX_CONT_SIDES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `gamma2:real->B`; `Tf:real`; `s:real`] P2BX_CONT_SIDES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "TS1" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "TS2" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "LB1" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "LB2" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                   `gamma1:real->B`; `gamma2:real->B`; `s:real`; `Tf:real`; `lm:real`;
                   `v1:real^3`; `v2:real^3`; `e:real`] P2BX_L925_PHI_RIGHT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `gamma1:real->B`; `Tf:real`; `s:real`] P2BX_CONT_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:B topology`; `gamma2:real->B`; `Tf:real`; `s:real`] P2BX_CONT_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  USE_THEN "TS1" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "TS2" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `gamma1:real->B`; `gamma2:real->B`; `s:real`;
                 `e:real`] P2BX_L925_LEFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt(s - h)) <=
                &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt s)` MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* The distance bound: d_{g(-T)}(p1,q1) <= 128 sqrt T lm when l <= lm^2.   *)

let P2BX_L925_DIST = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p Tf p1 q1 lm.
     P2A_FLOW_MIN_GRAD_STATEMENT w (:3) /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     P2B_COR_9_10_STATEMENT w /\ P2B_REQ_RFA_DIST_LOCAL_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ &0 < Tf /\
     p1 IN topspace top /\ q1 IN topspace top /\ &1 <= lm /\
     p2b_klx (top,atlas) g p Tf p1 <= lm pow 2 /\ p2b_klx (top,atlas) g p Tf q1 <= lm pow 2
     ==> mfd_dist (top,atlas) (g(--Tf)) p1 q1 <= &128 * sqrt Tf * lm`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL9") (CONJUNCTS_THEN2 (LABEL_TAC "FL8")
    (CONJUNCTS_THEN2 (LABEL_TAC "C910") (CONJUNCTS_THEN2 (LABEL_TAC "DL")
    STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `Tf:real`; `p1:B`] P2BX_L925_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TS1")
    (CONJUNCTS_THEN2 (LABEL_TAC "CO1") (CONJUNCTS_THEN2 (LABEL_TAC "LB1")
    (LABEL_TAC "VE1"))))))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `Tf:real`; `q1:B`] P2BX_L925_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma2:real->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TS2")
    (CONJUNCTS_THEN2 (LABEL_TAC "CO2") (CONJUNCTS_THEN2 (LABEL_TAC "LB2")
    (LABEL_TAC "VE2"))))))) THEN
  SUBGOAL_THEN `&0 <= sqrt Tf` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s. &0 < s /\ s <= Tf
         ==> sqrt s * p2b_klx (top,atlas) (g:real->B->real^3^3) p s (gamma1 s) <=
             sqrt Tf * lm pow 2) /\
    (!s. &0 < s /\ s <= Tf
         ==> sqrt s * p2b_klx (top,atlas) (g:real->B->real^3^3) p s (gamma2 s) <=
             sqrt Tf * lm pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `sqrt Tf * p2b_klx (top,atlas) (g:real->B->real^3^3) p Tf p1` THEN
      CONJ_TAC THENL [USE_THEN "LB1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC];
      EXISTS_TAC `sqrt Tf * p2b_klx (top,atlas) (g:real->B->real^3^3) p Tf q1` THEN
      CONJ_TAC THENL [USE_THEN "LB2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t0. &0 < t0 /\ t0 < Tf
         ==> mfd_dist (top,atlas) ((g:real->B->real^3^3) (--Tf)) (gamma1 Tf) (gamma2 Tf) -
             &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt Tf) <=
             mfd_dist (top,atlas) (g(--t0)) (gamma1 t0) (gamma2 t0) -
             &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt t0)`
  (LABEL_TAC "MONO") THENL
   [X_GEN_TAC `t0:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2BX_L925_MONO THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `p:B`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THENL
     [USE_THEN "TS1" MATCH_MP_TAC; USE_THEN "TS2" MATCH_MP_TAC;
      USE_THEN "VE1" MATCH_MP_TAC; USE_THEN "VE2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `ee = mfd_dist (top,atlas) ((g:real->B->real^3^3) (--Tf)) p1 q1 -
                   &128 * sqrt Tf * lm` THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `gamma1:real->B`; `gamma2:real->B`; `p:B`; `Tf:real`;
                 `ee:real`] P2BX_L925_START) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THENL
       [USE_THEN "TS1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "TS2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `O:B->bool` THEN STRIP_TAC THEN
      USE_THEN "CO1" (MP_TAC o SPECL [`&0`; `O:B->bool`]) THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
      X_GEN_TAC `O:B->bool` THEN STRIP_TAC THEN
      USE_THEN "CO2" (MP_TAC o SPECL [`&0`; `O:B->bool`]) THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
      EXPAND_TAC "ee" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "MONO" (MP_TAC o SPEC `t0:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt Tf) = &128 * sqrt Tf * lm /\
                &0 <= &4 * (&32 * sqrt(sqrt Tf) * lm) * sqrt(sqrt t0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `sqrt(sqrt Tf) pow 2 = sqrt Tf` MP_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; CONV_TAC REAL_RING];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The route theorem of MT Lemma 9.25 (c1 = 1/16384). *)

let P2B_LEMMA_9_25_ROUTE = prove
 (`!w:B->bool. P2B_LEMMA_9_25_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_LEMMA_9_25_ROUTE_STATEMENT; P2B_LEMMA_9_25_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL9") (CONJUNCTS_THEN2 (LABEL_TAC "FL8")
    (CONJUNCTS_THEN2 (LABEL_TAC "C910") (LABEL_TAC "DL")))) THEN
  EXISTS_TAC `&1 / &16384` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`; `t:real`; `p1:B`; `q1:B`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `&0 <= p2b_klx (top,atlas) (g:real->B->real^3^3) p t p1 /\
                &0 <= p2b_klx (top,atlas) g p t q1` STRIP_ASSUME_TAC THENL
   [USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                     `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:real->B->real^3^3`; `p:B`] o
                     REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`t:real`; `p1:B`] th) THEN
                         MP_TAC(SPECL [`t:real`; `q1:B`] th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `l1 = p2b_klx (top,atlas) (g:real->B->real^3^3) p t p1` THEN
  ABBREV_TAC `l2 = p2b_klx (top,atlas) (g:real->B->real^3^3) p t q1` THEN
  ABBREV_TAC `M = max l1 l2` THEN
  SUBGOAL_THEN `l1 <= M /\ l2 <= M /\ &0 <= M /\ M <= l1 + l2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt(M + &1) /\ sqrt(M + &1) pow 2 = M + &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `lm = sqrt(M + &1)` THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `t:real`; `p1:B`; `q1:B`; `lm:real`] P2BX_L925_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (--t)) p1 q1` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->B->real^3^3) (--t)) p1 q1` THEN
  SUBGOAL_THEN `d pow 2 <= &16384 * (t * (M + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&128 * sqrt t * lm) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * M <= t * (l1 + l2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &16384 * d pow 2) / t <= l1 + l2 + &1` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

