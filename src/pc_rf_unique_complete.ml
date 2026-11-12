(* ========================================================================= *)
(* Unit pc_rf_unique_complete: uniqueness of complete Ricci flows of bounded *)
(* curvature (the core of A14, the statement                                 *)
(* P2C_REQ_UNIQ_COMPLETE_STATEMENT, at (:real^3)), by Kotschwar's energy     *)
(* (arXiv 1206.3225, Sec 2) with the weight exp(-lambda phi) and cutoffs     *)
(* chi(phi / R) from the exhaustion function phi of the statement, using the *)
(* local inequality of pc_rf_unique and the noncompact integration tools of  *)
(* pc_rf_unique_ncint.  Main result RFU_ENERGY_ZERO: under uniform bounds on *)
(* [a,b1] the Kotschwar density vanishes.                                    *)
(* ========================================================================= *)

needs "src/pc_rf_unique.ml";;
needs "src/pc_p2c_views.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/pc_rfa_slcalc.ml";;
needs "src/pc_rf_unique_ncint.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The local Kotschwar inequality keeping one copy of the good               *)
(* term: e_t <= div Z - |X|^2 + C e (RFU_KOT_ALG2, RFU_KOT_LOCAL2).  The     *)
(* kept term absorbs the cross term of the weight and of the cutoffs in the  *)
(* noncompact energy.                                                        *)
(* ========================================================================= *)

let RFU_KOT_ARITH2 = prove
 (`!ed D xx x e s ixy iap R bb cp Cr:real.
        ed = D - &2 * xx - &2 * ixy + &2 * iap + R /\
        xx = x pow 2 /\ e = s pow 2 /\
        abs ixy <= x * (bb * s) /\ abs iap <= s * (cp * x) /\ R <= Cr * e
        ==> ed <= D - xx + (Cr + (bb + cp) pow 2) * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  MP_TAC(SPEC `x - (bb + cp) * s` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

(* The pointwise inequality e_t <= div Z - |X|^2 + C e at one time. *)

let RFU_KOT_ALG2 = prove
 (`!K. ?C. &0 <= C /\
        !U (G1:real^N->real^N^N) G2 y.
          metric_field U G1 /\ metric_field U G2 /\ y IN U /\ rfu_kbound K G1 G2 y
          ==> rfu_edot G1 G2 y <=
              ldiv G1 (rfu_kz G1 G2) y - ltnorm2 5 G1 (rfu_x G1 G2) y +
              C * pde_kot_density G1 G2 y`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_EHH_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ch:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Ch"))) THEN
  MP_TAC(SPEC `K:real` RFU_EAA_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ca:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Ca"))) THEN
  MP_TAC(SPEC `K:real` RFU_EQ_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cq"))) THEN
  MP_TAC(SPEC `K:real` RFU_Y_NORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cy"))) THEN
  MP_TAC(SPEC `K:real` (MATCH_MP (INST_TYPE [`:N`,`:N`] RFU_QA_INNER)
                                 (ARITH_RULE `1 <= 2`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q2"))) THEN
  MP_TAC(SPEC `K:real` (MATCH_MP (INST_TYPE [`:N`,`:N`] RFU_QA_INNER)
                                 (ARITH_RULE `1 <= 3`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q3"))) THEN
  MP_TAC(SPEC `K:real` (MATCH_MP (INST_TYPE [`:N`,`:N`] RFU_QA_INNER)
                                 (ARITH_RULE `1 <= 4`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q4"))) THEN
  MP_TAC(INST_TYPE [`:N`,`:N`] RFU_PA_NORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cp"))) THEN
  EXISTS_TAC `(&2 * (Ch + Ca + Cq) * K pow 4 + Q2 + Q3 + Q4) +
              (sqrt(Cy * K pow 4) + sqrt Cp) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS] THEN
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfu_hyp K (K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)) U G1 G2 y`
  ASSUME_TAC THENL [MATCH_MP_TAC RFU_HYP_DENS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`] RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_X_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "Cp" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `G2:real^N->real^N^N`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `rfu_cb 4 (lrm4 (G1:real^N->real^N^N)) y K` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfu_kbound]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 5 U
      (\z u. lnabla 4 (G1:real^N->real^N^N) (rfu_q G1 G2) z u - rfu_x G1 G2 z u)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                   `rfu_q (G1:real^N->real^N^N) G2`] LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[ARITH] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)) pow 2 =
    K pow 4 * pde_kot_density G1 G2 y`
  (LABEL_TAC "cc") THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y` ASSUME_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 3 (G1:real^N->real^N^N) (rfu_pa G1 G2) y` ASSUME_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pde_kot_density (G1:real^N->real^N^N) G2 y` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RFU_KOT_ARITH2 THEN
  MAP_EVERY EXISTS_TAC
   [`sqrt(ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y)`;
    `sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
    `ltinner 5 G1 (rfu_x G1 G2)
       (\z u. lnabla 4 (G1:real^N->real^N^N) (rfu_q G1 G2) z u - rfu_x G1 G2 z u) y`;
    `ltinner 3 (G1:real^N->real^N^N) (rfu_aa G1 G2) (rfu_pa G1 G2) y`;
    `(&2 * ltinner 2 G1 (rfu_hh G1 G2) (rfu_hhdot (G1:real^N->real^N^N) G2) y +
      ltinner 2 G1 (rfu_hh G1 G2) (rfu_qa 2 G1 (rfu_hh G1 G2)) y) +
     (&2 * ltinner 3 G1 (rfu_aa G1 G2)
             (\z u. rfu_aadot G1 G2 z u - rfu_pa G1 G2 z u) y +
      ltinner 3 G1 (rfu_aa G1 G2) (rfu_qa 3 G1 (rfu_aa G1 G2)) y) +
     (&2 * ltinner 4 G1 (rfu_q G1 G2)
             (\z u. rfu_qdot G1 G2 z u - rfu_tdiv 4 G1 (rfu_x G1 G2) z u) y +
      ltinner 4 G1 (rfu_q G1 G2) (rfu_qa 4 G1 (rfu_q G1 G2)) y)`] THEN
  REPEAT CONJ_TAC THENL
   [(* the splitting identity *)
    MATCH_MP_TAC RFU_EDOT_SPLIT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POW_2];
    ASM_SIMP_TAC[SQRT_POW_2];
    (* the X-Y cross term *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sqrt(ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y) *
      sqrt(ltnorm2 5 G1
        (\z u. lnabla 4 (G1:real^N->real^N^N) (rfu_q G1 G2) z u - rfu_x G1 G2 z u) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_ABS_LE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    USE_THEN "Cy" (MP_TAC o SPECL
      [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
       `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "cc" SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC];
    (* the A-PA cross term *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sqrt(ltnorm2 3 (G1:real^N->real^N^N) (rfu_aa G1 G2) y) *
      sqrt(ltnorm2 3 G1 (rfu_pa G1 G2) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_ABS_LE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REWRITE_TAC[]];
    (* the lower-order rest *)
    ALL_TAC] THEN
  USE_THEN "Ch" (MP_TAC o SPECL
    [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
     `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
  USE_THEN "Ca" (MP_TAC o SPECL
    [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
     `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
  USE_THEN "Cq" (MP_TAC o SPECL
    [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
     `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
  USE_THEN "Q2" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `rfu_hh (G1:real^N->real^N^N) G2`; `y:real^N`]) THEN
  USE_THEN "Q3" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `rfu_aa (G1:real^N->real^N^N) G2`; `y:real^N`]) THEN
  USE_THEN "Q4" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `rfu_q (G1:real^N->real^N^N) G2`; `y:real^N`]) THEN
  REWRITE_TAC[GSYM rfu_qa] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "cc" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN
   `Q2 * ltnorm2 2 (G1:real^N->real^N^N) (rfu_hh G1 G2) y <= Q2 * pde_kot_density G1 G2 y /\
    Q3 * ltnorm2 3 (G1:real^N->real^N^N) (rfu_aa G1 G2) y <= Q3 * pde_kot_density G1 G2 y /\
    Q4 * ltnorm2 4 (G1:real^N->real^N^N) (rfu_q G1 G2) y <= Q4 * pde_kot_density G1 G2 y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The local inequality with the good term, for two local Ricci flows. *)

let RFU_KOT_LOCAL2 = prove
 (`!K. ?C. &0 <= C /\
        !U a b (G1:real->real^N->real^N^N) G2 t y.
          lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ a < t /\ t < b /\ y IN U /\
          rfu_kbound K (G1 t) (G2 t) y
          ==> ((\s. pde_kot_density (G1 s) (G2 s) y) has_real_derivative
               rfu_edot (G1 t) (G2 t) y) (atreal t) /\
              rfu_edot (G1 t) (G2 t) y <=
              ldiv (G1 t) (rfu_kz (G1 t) (G2 t)) y -
              ltnorm2 5 (G1 t) (rfu_x (G1 t) (G2 t)) y +
              C * pde_kot_density (G1 t) (G2 t) y`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_KOT_ALG2) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFU_EDOT_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    USE_THEN "C" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[RFU_FLOW_METRIC]]);;

(* ========================================================================= *)
(* The derivative of a function along the Kotschwar field Z is               *)
(* at most C sqrt(e) |X| |df| (RFU_KZ_DF_BOUND), under the component bounds *)
(* rfu_kbound K at the point.  Z = G1^-1 w with w_b = 2 <Q, X(.., e_b)>.    *)
(* ========================================================================= *)

(* Cauchy-Schwarz for the inverse metric. *)

let RFU_GINV_CS = prove
 (`!U (G:real^N->real^N^N) y (p:real^N) q.
        metric_field U G /\ y IN U
        ==> abs(p dot (matrix_inv(G y) ** q)) <=
            sqrt(p dot (matrix_inv(G y) ** p)) * sqrt(q dot (matrix_inv(G y) ** q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  SIMP_TAC[POW_2_SQRT; NORM_POS_LE; NORM_CAUCHY_SCHWARZ_ABS]);;

(* The derivative as a dot product with the vector of partial derivatives. *)

let RFU_D1_DOT = prove
 (`!(f:real^N->real) y v.
        (\z. lift(f z)) differentiable at y
        ==> rfa_d1 f y v = ((lambda i. rfa_d1 f y (basis i)):real^N) dot v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `1`] o MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let RFU_LGRAD2_DOT = prove
 (`!(G:real^N->real^N^N) f y.
        lgrad2 G f y =
        ((lambda i. rfa_d1 f y (basis i)):real^N) dot
        (matrix_inv(G y) ** ((lambda i. rfa_d1 f y (basis i)):real^N))`,
  REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner; RFA_BILIN_SUM]);;

(* A quadratic form with bounded entries on a vector with bounded entries. *)

let RFU_QFORM_BOUND = prove
 (`!(A:real^N^N) (w:real^N) K W.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(A$i$j) <= K) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> abs(w$i) <= W)
        ==> abs(w dot (A ** w)) <= &(dimindex(:N)) * (W * (&(dimindex(:N)) * (K * W)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dot] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS]);;

(* Fixing the last slot of a 5-tensor with component bound c to a basis     *)
(* vector gives a 4-tensor with component bound c.                           *)

let RFU_CB_SLOT5 = prove
 (`!U (X:real^N->(num->real^N)->real) y c b.
        ltensor_field 5 U X /\ y IN U /\ rfu_cb 5 X y c /\ 1 <= b /\ b <= dimindex(:N)
        ==> rfu_cb 4 (\z u. X z (\m. if m = 5 then basis b else u m)) y c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_CB_OF_BTUP THEN
  X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`5`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfu_btup] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `rfu_btup 4 (u:num->real^N)` THEN REWRITE_TAC[rfu_btup] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let RFU_KZ_DF_BOUND = prove
 (`!K. ?C. &0 <= C /\
        !U (G1:real^N->real^N^N) G2 y (f:real^N->real).
          metric_field U G1 /\ metric_field U G2 /\ y IN U /\ rfu_kbound K G1 G2 y /\
          (\z. lift(f z)) differentiable at y
          ==> abs(rfa_d1 f y (rfu_kz G1 G2 y)) <=
              C * sqrt(pde_kot_density G1 G2 y) * sqrt(ltnorm2 5 G1 (rfu_x G1 G2) y) *
              sqrt(lgrad2 G1 f y)`,
  GEN_TAC THEN
  EXISTS_TAC `&2 * &(dimindex(:N)) * &(CARD(index_tuples 4 (:N))) pow 2 * abs K pow 10` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_LE THEN
    REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= K` ASSUME_TAC THENL [ASM_MESON_TAC[rfu_kbound]; ALL_TAC] THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> abs((G1:real^N->real^N^N) y$i$j) <= K /\
              abs(matrix_inv(G1 y)$i$j) <= K`
  (LABEL_TAC "GB") THENL [ASM_MESON_TAC[rfu_kbound]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_X_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`] RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `e = pde_kot_density (G1:real^N->real^N^N) G2 y` THEN
  ABBREV_TAC `xx = ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y` THEN
  SUBGOAL_THEN `&0 <= e /\ &0 <= xx` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "xx" THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* component bounds of Q and of X *)
  SUBGOAL_THEN `rfu_cb 4 (rfu_q (G1:real^N->real^N^N) G2) y (K pow 2 * sqrt e)`
  ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                   `y:real^N`; `K:real`] RFU_DENS_SMALL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfu_cb 5 (rfu_x (G1:real^N->real^N^N) G2) y (K pow 3 * sqrt xx)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_CB_MONO THEN EXISTS_TAC `sqrt(xx * K pow 5)` THEN CONJ_TAC THENL
     [EXPAND_TAC "xx" THEN MATCH_MP_TAC RFU_CB_LTNORM2 THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "GB" (MP_TAC o SPECL [`i:num`; `i:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POW_POW] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the covector w and its entries *)
  ABBREV_TAC
   `w = (lambda b. &2 * ltinner 4 G1 (rfu_q G1 G2)
                     (\z' (u:num->real^N).
                        rfu_x (G1:real^N->real^N^N) G2 z'
                          (\m. if m = 5 then basis b else u m)) y):real^N` THEN
  SUBGOAL_THEN `rfu_kz (G1:real^N->real^N^N) G2 y = matrix_inv(G1 y) ** (w:real^N)`
  SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[rfu_kz; rfu_vf] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = &2 * (&(CARD(index_tuples 4 (:N))) pow 2 * K pow 4 * (K pow 2 * sqrt e) *
             (K pow 3 * sqrt xx))` THEN
  SUBGOAL_THEN `&0 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; SQRT_POS_LE; REAL_POW_LE;
                 REAL_ARITH `&1 <= K ==> &0 <= K`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b. 1 <= b /\ b <= dimindex(:N) ==> abs((w:real^N)$b) <= W`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:num` THEN STRIP_TAC THEN EXPAND_TAC "w" THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &2 * x <= &2 * y`) THEN
    MATCH_MP_TAC RFU_LTINNER_CB THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RFU_CB_SLOT5 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the quadratic form of w *)
  SUBGOAL_THEN
   `sqrt((w:real^N) dot (matrix_inv((G1:real^N->real^N^N) y) ** w)) <=
    (&2 * &(dimindex(:N)) * &(CARD(index_tuples 4 (:N))) pow 2 * K pow 10) *
    sqrt e * sqrt xx`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; SQRT_POS_LE; REAL_POW_LE;
                   REAL_ARITH `&1 <= K ==> &0 <= K`];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N)) * (W * (&(dimindex(:N)) * (K * W)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFU_QFORM_BOUND THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&(dimindex(:N)) * (W * (&(dimindex(:N)) * (K * W))) =
      (&2 * &(dimindex(:N)) * &(CARD(index_tuples 4 (:N))) pow 2 * K pow 9 *
       sqrt e * sqrt xx) pow 2 * K /\
      ((&2 * &(dimindex(:N)) * &(CARD(index_tuples 4 (:N))) pow 2 * K pow 10) *
       sqrt e * sqrt xx) pow 2 =
      (&2 * &(dimindex(:N)) * &(CARD(index_tuples 4 (:N))) pow 2 * K pow 9 *
       sqrt e * sqrt xx) pow 2 * K pow 2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [EXPAND_TAC "W" THEN CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= K * (K - &1) ==> K <= K * K`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Cauchy-Schwarz *)
  MP_TAC(ISPECL [`f:real^N->real`; `y:real^N`;
                 `matrix_inv((G1:real^N->real^N^N) y) ** (w:real^N)`] RFU_D1_DOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(lgrad2 (G1:real^N->real^N^N) f y) *
    sqrt((w:real^N) dot (matrix_inv((G1:real^N->real^N^N) y) ** w))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RFU_LGRAD2_DOT] THEN MATCH_MP_TAC RFU_GINV_CS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(lgrad2 (G1:real^N->real^N^N) f y) *
    ((&2 * &(dimindex(:N)) * &(CARD(index_tuples 4 (:N))) pow 2 * K pow 10) *
     sqrt e * sqrt xx)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC LGRAD2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Linear changes of coordinates normalising a metric at a                   *)
(* point (RFU_NORMALIZE), and the component bounds rfu_kbound from norm      *)
(* bounds in normalised coordinates (RFU_KBOUND_NORMAL).                     *)
(* ========================================================================= *)

let RFU_SMOOTH_LINEAR = prove
 (`!s (M:real^N^N). open s ==> smooth_map_on s (\z. M ** z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^N. (M:real^N^N) ** z) = (\z. M ** z) o (\z. z)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR]);;

let RFU_LINEAR_FDERIV = prove
 (`!(M:real^N^N) z. frechet_derivative (\z. M ** z) (at z) = (\z. M ** z)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let RFU_DIFFEO_LINEAR = prove
 (`!(M:real^N^N) U.
        invertible M /\ open U
        ==> diffeomorphism_on (IMAGE (\y. M ** y) U) U
                              (\z. matrix_inv M ** z) (\y. M ** y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(M:real^N^N) ** matrix_inv M = mat 1 /\ matrix_inv M ** M = mat 1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MATRIX_INV]; ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN
  SUBGOAL_THEN `open(IMAGE (\y. (M:real^N^N) ** y) U)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. (M:real^N^N) ** y`; `U:real^N->bool`]
           OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^N. matrix_inv(M:real^N^N) ** w`) THEN
        ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
        X_GEN_TAC `v:real^N` THEN EXISTS_TAC `matrix_inv(M:real^N^N) ** v` THEN
        ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFU_SMOOTH_LINEAR] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID; IMAGE_ID;
                  MATRIX_MUL_LID; MATRIX_MUL_RID; MATRIX_MUL_ASSOC]);;

(* Normalisation: a linear map h with h(z0) = y and (h^* G)(z0) = I. *)

let RFU_NORMALIZE = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> ?M. invertible M /\
                diffeomorphism_on (IMAGE (\y. M ** y) U) U
                                  (\z. matrix_inv M ** z) (\y. M ** y) /\
                M ** y IN IMAGE (\y. M ** y) U /\
                matrix_inv M ** (M ** y) = y /\
                mpullback (\z. matrix_inv M ** z) G (M ** y) = mat 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real^N^N` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(M:real^N^N) ** matrix_inv M = mat 1 /\ matrix_inv M ** M = mat 1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MATRIX_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^N^N) ** y IN IMAGE (\y. M ** y) U` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFU_DIFFEO_LINEAR] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[mpullback; RFU_LINEAR_FDERIV; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
  SUBGOAL_THEN
   `transp(matrix_inv M) ** (transp M ** M) ** matrix_inv M =
    transp((M:real^N^N) ** matrix_inv M) ** (M ** matrix_inv M)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_LID]);;

(* A square root bound used for the component bounds. *)

let RFU_SQRT_KB = prove
 (`!x k L B.
        &0 <= x /\ x <= B /\ k <= 6 /\ &0 <= L
        ==> sqrt(x * L pow k) <= (abs B + &1) * (L + &1) pow 3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs B + &1) * (L + &1) pow 6` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L + &1) pow k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x * (x - &1) ==> x <= x * x`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC);;

(* rfu_kbound in coordinates where G1 = I at the point, from the            *)
(* equivalence of G2 with G1 and bounds of |Rm1|, |Rm2|, |nabla Rm2| and     *)
(* |nabla^2 Rm2|.                                                           *)

let RFU_KBOUND_NORMAL = prove
 (`!U (G1:real^N->real^N^N) G2 z Lam B.
     metric_field U G1 /\ metric_field U G2 /\ z IN U /\ G1 z = mat 1 /\
     (!v. v dot (G2 z ** v) <= Lam * (v dot v) /\ v dot v <= Lam * (v dot (G2 z ** v))) /\
     lrm_deriv_norm2 0 G1 z <= B /\ lrm_deriv_norm2 0 G2 z <= B /\
     lrm_deriv_norm2 1 G2 z <= B /\ lrm_deriv_norm2 2 G2 z <= B
     ==> rfu_kbound ((abs B + &1) * (abs Lam + &1) pow 3) G1 G2 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v dot ((G2:real^N->real^N^N) z ** v) <= abs Lam * norm v pow 2 /\
        norm v pow 2 <= abs Lam * (v dot (G2 z ** v))`
  (LABEL_TAC "EQ") THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `v:real^N`) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `z:real^N`; `v:real^N`]
           LRG_METRIC_NONNEG) THEN
    MP_TAC(ISPEC `v:real^N` DOT_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `Lam * ((v:real^N) dot v)`;
      EXISTS_TAC `Lam * (v dot ((G2:real^N->real^N^N) z ** v))`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = abs Lam` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL [EXPAND_TAC "L" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = (abs B + &1) * (L + &1) pow 3` THEN
  SUBGOAL_THEN `&1 <= K /\ L <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBGOAL_THEN `L + &1 <= (L + &1) pow 3` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(L + &1) pow 3 <= (abs B + &1) * (L + &1) pow 3` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `transp((G2:real^N->real^N^N) z) = G2 z /\ invertible(G2 z) /\
    (!v. &0 <= v dot (G2 z ** v))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[RFU_METRIC_PROPS];
      ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
      GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> abs((G2:real^N->real^N^N) z$i$j) <= L /\ abs(matrix_inv(G2 z)$i$j) <= L`
  (LABEL_TAC "E2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_QFORM_ENTRY_BOUND THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`(G2:real^N->real^N^N) z`; `L:real`] RFA_GINV_ENTRY_BOUND) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N) ==> (G2:real^N->real^N^N) z$i$i <= L`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "E2" (MP_TAC o SPECL [`i:num`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                 `lrm4 (G2:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "IT") THEN
  SUBGOAL_THEN
   `!k tf. ltensor_field k U tf /\ k <= 6 /\ &0 <= ltnorm2 k (G2:real^N->real^N^N) tf z /\
           ltnorm2 k G2 tf z <= B
           ==> rfu_cb k tf z K`
  (LABEL_TAC "CB2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_CB_MONO THEN
    EXISTS_TAC `sqrt(ltnorm2 k (G2:real^N->real^N^N) tf z * L pow k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFU_CB_LTNORM2 THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "K" THEN MATCH_MP_TAC RFU_SQRT_KB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[rfu_kbound] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* entries *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "E2" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[MATRIX_INV_I] THEN ASM_SIMP_TAC[MAT_COMPONENT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
    (* Rm1 in coordinates with G1 = I *)
    MATCH_MP_TAC RFU_CB_MONO THEN
    EXISTS_TAC `sqrt(ltnorm2 4 (G1:real^N->real^N^N) (lrm4 G1) z * &1 pow 4)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFU_CB_LTNORM2 THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[MAT_COMPONENT; REAL_POS; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs B + &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `lrm_deriv_norm2 0 (G1:real^N->real^N^N) z <= B` THEN
      REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN
      MP_TAC(SPEC `abs B` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      EXPAND_TAC "K" THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC]];
    (* Rm2 *)
    USE_THEN "CB2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `lrm_deriv_norm2 0 (G2:real^N->real^N^N) z <= B` THEN
      REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES]];
    (* nabla Rm2 *)
    USE_THEN "CB2" MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    USE_THEN "IT" (MP_TAC o SPEC `1`) THEN REWRITE_TAC[RFA_LNABLA_ITER_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `lrm_deriv_norm2 1 (G2:real^N->real^N^N) z <= B` THEN
      REWRITE_TAC[lrm_deriv_norm2; RFA_LNABLA_ITER_1] THEN CONV_TAC NUM_REDUCE_CONV];
    (* nabla^2 Rm2 *)
    USE_THEN "CB2" MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    USE_THEN "IT" (MP_TAC o SPEC `2`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `lrm_deriv_norm2 2 (G2:real^N->real^N^N) z <= B` THEN
      REWRITE_TAC[lrm_deriv_norm2] THEN CONV_TAC NUM_REDUCE_CONV]]);;

(* ========================================================================= *)
(* Invariance of the quantities of the local inequality under                *)
(* diffeomorphisms (e_t, |X|^2, div Z, df(Z)), and the local inequality in  *)
(* norm form (RFU_KOT_NORM): the constant depends only on the equivalence   *)
(* constant of the two metrics and on bounds of |Rm1|, |Rm2|, |nabla Rm2|   *)
(* and |nabla^2 Rm2| at the point, not on the chart.                        *)
(* ========================================================================= *)

let RFU_EDOT_PULLBACK = prove
 (`!U U' a b (h:real^N->real^N) h' (G1:real->real^N->real^N^N) G2 t z.
        lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ diffeomorphism_on U' U h h' /\
        a < t /\ t < b /\ z IN U'
        ==> rfu_edot (mpullback h (G1 t)) (mpullback h (G2 t)) z =
            rfu_edot (G1 t) (G2 t) (h z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `a:real`; `b:real`;
                 `h:real^N->real^N`; `h':real^N->real^N`; `G1:real->real^N->real^N^N`]
                LRICCI_FLOW_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `a:real`; `b:real`;
                 `h:real^N->real^N`; `h':real^N->real^N`; `G2:real->real^N->real^N^N`]
                LRICCI_FLOW_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `\s. pde_kot_density (mpullback (h:real^N->real^N) ((G1:real->real^N->real^N^N) s))
                                  (mpullback h ((G2:real->real^N->real^N^N) s)) z` THEN
  EXISTS_TAC `t:real` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`U':real^N->bool`; `a:real`; `b:real`;
                   `\s. mpullback (h:real^N->real^N) ((G1:real->real^N->real^N^N) s)`;
                   `\s. mpullback (h:real^N->real^N) ((G2:real->real^N->real^N^N) s)`;
                   `t:real`; `z:real^N`] RFU_EDOT_DERIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. pde_kot_density ((G1:real->real^N->real^N^N) s) (G2 s) ((h:real^N->real^N) z)` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `a < s /\ s < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BETA_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFU_DENS_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_MESON_TAC[RFU_FLOW_METRIC];
    MATCH_MP_TAC RFU_EDOT_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[]]);;

let RFU_XX_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 z.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ z IN U'
        ==> ltnorm2 5 (mpullback h G1) (rfu_x (mpullback h G1) (mpullback h G2)) z =
            ltnorm2 5 G1 (rfu_x G1 G2) (h z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_X_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. rfu_x (mpullback (h:real^N->real^N) G1) (mpullback h G2) z u =
        ltpullback h (rfu_x (G1:real^N->real^N^N) G2) z u`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RFU_X_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM RFU_LTINNER_SELF] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltinner 5 (mpullback (h:real^N->real^N) G1)
                (ltpullback h (rfu_x (G1:real^N->real^N^N) G2))
                (ltpullback h (rfu_x G1 G2)) z` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ltinner] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFU_LTINNER_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let RFU_LDIVKZ_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 z.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ z IN U'
        ==> ldiv (mpullback h G1) (rfu_kz (mpullback h G1) (mpullback h G2)) z =
            ldiv G1 (rfu_kz G1 G2) (h z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\ open(U':real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^N->real^N) G1) /\
                metric_field U' (mpullback h G2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGT_LDIV_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[RFU_KZ_SMOOTH];
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[RFU_KZ_SMOOTH];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFU_KZ_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let RFU_D1_COMPOSE = prove
 (`!U U' (h:real^N->real^N) h' (f:real^N->real) z v.
        diffeomorphism_on U' U h h' /\ z IN U' /\ smooth_map_on U (\y. lift(f y))
        ==> rfa_d1 (f o h) z v = rfa_d1 f (h z) (frechet_derivative h (at z) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. lift((f:real^N->real) y)) has_derivative
     frechet_derivative (\y. lift(f y)) (at ((h:real^N->real^N) z))) (at (h z))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_d1] THEN
  SUBGOAL_THEN
   `frechet_derivative (\x. lift(((f:real^N->real) o (h:real^N->real^N)) x)) (at z) =
    frechet_derivative (\y. lift(f y)) (at (h z)) o frechet_derivative h (at z)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN
     `(\x. lift(((f:real^N->real) o (h:real^N->real^N)) x)) = (\y. lift(f y)) o h`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM]]);;

let RFU_DFKZ_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 (f:real^N->real) z.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\
        z IN U' /\ smooth_map_on U (\y. lift(f y))
        ==> rfa_d1 (f o h) z (rfu_kz (mpullback h G1) (mpullback h G2) z) =
            rfa_d1 f (h z) (rfu_kz G1 G2 (h z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `f:real^N->real`; `z:real^N`;
                 `rfu_kz (mpullback (h:real^N->real^N) G1) (mpullback h G2) z`]
                RFU_D1_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFU_KZ_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let RFU_MPULLBACK_QFORM = prove
 (`!(h:real^N->real^N) G z v.
        linear(frechet_derivative h (at z))
        ==> v dot (mpullback h G z ** v) =
            (frechet_derivative h (at z) v) dot (G(h z) ** frechet_derivative h (at z) v)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mpullback; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

(* The local inequality in norm form. *)

let RFU_KOT_NORM = prove
 (`!Lam B. ?C. &0 <= C /\
     !U a b (G1:real->real^N->real^N^N) G2 t y.
       lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ a < t /\ t < b /\ y IN U /\
       (!v. v dot (G2 t y ** v) <= Lam * (v dot (G1 t y ** v)) /\
            v dot (G1 t y ** v) <= Lam * (v dot (G2 t y ** v))) /\
       lrm_deriv_norm2 0 (G1 t) y <= B /\ lrm_deriv_norm2 0 (G2 t) y <= B /\
       lrm_deriv_norm2 1 (G2 t) y <= B /\ lrm_deriv_norm2 2 (G2 t) y <= B
       ==> rfu_edot (G1 t) (G2 t) y <=
           ldiv (G1 t) (rfu_kz (G1 t) (G2 t)) y -
           ltnorm2 5 (G1 t) (rfu_x (G1 t) (G2 t)) y +
           C * pde_kot_density (G1 t) (G2 t) y /\
           (!f. smooth_map_on U (\z. lift(f z))
                ==> abs(rfa_d1 f y (rfu_kz (G1 t) (G2 t) y)) <=
                    C * sqrt(pde_kot_density (G1 t) (G2 t) y) *
                    sqrt(ltnorm2 5 (G1 t) (rfu_x (G1 t) (G2 t)) y) *
                    sqrt(lgrad2 (G1 t) f y))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `(abs B + &1) * (abs Lam + &1) pow 3`
              (INST_TYPE [`:N`,`:N`] RFU_KOT_ALG2)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1"))) THEN
  MP_TAC(SPEC `(abs B + &1) * (abs Lam + &1) pow 3`
              (INST_TYPE [`:N`,`:N`] RFU_KZ_DF_BOUND)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C2"))) THEN
  EXISTS_TAC `C1 + C2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field U ((G1:real->real^N->real^N^N) t) /\ metric_field U (G2 t) /\ open U`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[RFU_FLOW_METRIC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`; `y:real^N`]
                RFU_NORMALIZE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = \z:real^N. matrix_inv(M:real^N^N) ** z` THEN
  ABBREV_TAC `U' = IMAGE (\y:real^N. (M:real^N^N) ** y) U` THEN
  ABBREV_TAC `z0 = (M:real^N^N) ** y` THEN
  SUBGOAL_THEN `(h:real^N->real^N) z0 = y` (LABEL_TAC "HZ") THENL
   [MAP_EVERY EXPAND_TAC ["h"; "z0"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `\y:real^N. (M:real^N^N) ** y`; `z0:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `F1 = mpullback (h:real^N->real^N) ((G1:real->real^N->real^N^N) t)` THEN
  ABBREV_TAC `F2 = mpullback (h:real^N->real^N) ((G2:real->real^N->real^N^N) t)` THEN
  SUBGOAL_THEN `metric_field U' (F1:real^N->real^N^N) /\ metric_field U' (F2:real^N->real^N^N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `\y:real^N. (M:real^N^N) ** y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the normalised component bounds *)
  SUBGOAL_THEN
   `!l. lrm_deriv_norm2 l (F1:real^N->real^N^N) z0 =
        lrm_deriv_norm2 l ((G1:real->real^N->real^N^N) t) y /\
        lrm_deriv_norm2 l (F2:real^N->real^N^N) z0 = lrm_deriv_norm2 l (G2 t) y`
  (LABEL_TAC "NR") THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN
    USE_THEN "HZ" (fun th -> GEN_REWRITE_TAC DEPTH_CONV [SYM th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC LRM_DERIV_NORM2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `\y:real^N. (M:real^N^N) ** y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfu_kbound ((abs B + &1) * (abs Lam + &1) pow 3) (F1:real^N->real^N^N) F2 z0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_KBOUND_NORMAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `(G1:real->real^N->real^N^N) t`; `z0:real^N`;
                   `v:real^N`] RFU_MPULLBACK_QFORM) THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `(G2:real->real^N->real^N^N) t`; `z0:real^N`;
                   `v:real^N`] RFU_MPULLBACK_QFORM) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* transport of the terms *)
  SUBGOAL_THEN
   `rfu_edot (F1:real^N->real^N^N) F2 z0 =
    rfu_edot ((G1:real->real^N->real^N^N) t) (G2 t) y /\
    pde_kot_density F1 F2 z0 = pde_kot_density (G1 t) (G2 t) y /\
    ldiv F1 (rfu_kz F1 F2) z0 = ldiv (G1 t) (rfu_kz (G1 t) (G2 t)) y /\
    ltnorm2 5 F1 (rfu_x F1 F2) z0 = ltnorm2 5 (G1 t) (rfu_x (G1 t) (G2 t)) y`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN
    USE_THEN "HZ" (fun th -> GEN_REWRITE_TAC DEPTH_CONV [SYM th]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFU_EDOT_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `a:real`; `b:real`;
                            `\y:real^N. (M:real^N^N) ** y`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_DENS_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `\y:real^N. (M:real^N^N) ** y`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_LDIVKZ_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `\y:real^N. (M:real^N^N) ** y`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_XX_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `\y:real^N. (M:real^N^N) ** y`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pde_kot_density ((G1:real->real^N->real^N^N) t) (G2 t) y /\
                &0 <= ltnorm2 5 (G1 t) (rfu_x (G1 t) (G2 t)) y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`;
                     `(G2:real->real^N->real^N^N) t`; `y:real^N`] RFU_DENS_TERMS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[RFU_X_FIELD]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "C1" (MP_TAC o SPECL [`U':real^N->bool`; `F1:real^N->real^N^N`;
                                   `F2:real^N->real^N^N`; `z0:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`C2:real`; `pde_kot_density ((G1:real->real^N->real^N^N) t) (G2 t) y`]
                 REAL_LE_MUL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `f:real^N->real` THEN DISCH_TAC THEN
  USE_THEN "C2" (MP_TAC o SPECL [`U':real^N->bool`; `F1:real^N->real^N^N`;
                                 `F2:real^N->real^N^N`; `z0:real^N`;
                                 `(f:real^N->real) o (h:real^N->real^N)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z. lift(((f:real^N->real) o (h:real^N->real^N)) z)) = (\y. lift(f y)) o h`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfa_d1 ((f:real^N->real) o (h:real^N->real^N)) z0 (rfu_kz F1 F2 z0) =
    rfa_d1 f y (rfu_kz ((G1:real->real^N->real^N^N) t) (G2 t) y) /\
    lgrad2 (F1:real^N->real^N^N) (f o h) z0 = lgrad2 (G1 t) f y`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN
    USE_THEN "HZ" (fun th -> GEN_REWRITE_TAC DEPTH_CONV [SYM th]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFU_DFKZ_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `\y:real^N. (M:real^N^N) ** y`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LGRAD2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `\y:real^N. (M:real^N^N) ** y`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!x p c1 c2. &0 <= c1 * p ==> x <= c2 * p ==> x <= (c1 + c2) * p`) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC SQRT_POS_LE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LGRAD2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The pointwise inequality on the manifold, in the preferred                *)
(* chart at x, with constants depending only on norm bounds at x            *)
(* (RFU_KOT_MFD).  Manifold scalars: |X|^2 (rfu_mxx), |df|^2 (rfu_mgrad2;    *)
(* p2c_fgrad2 is its 3-dimensional instance) and df(Z) (rfu_mdf).           *)
(* ========================================================================= *)

let rfu_mxx = new_definition
 `rfu_mxx (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N) (g2:A->real^N^N) (x:A) =
    ltnorm2 5 (metric_local atlas (chart_at atlas x) g1)
      (rfu_x (metric_local atlas (chart_at atlas x) g1)
             (metric_local atlas (chart_at atlas x) g2))
      (SND(chart_at atlas x) x)`;;

let rfu_mgrad2 = new_definition
 `rfu_mgrad2 (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) (x:A) =
    lgrad2 (metric_local atlas (chart_at atlas x) g) (f o chart_inv (chart_at atlas x))
           (SND(chart_at atlas x) x)`;;

let rfu_mdf = new_definition
 `rfu_mdf (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (Z:A->real^N) (x:A) =
    drop(frechet_derivative (\y. lift(f(chart_inv (chart_at atlas x) y)))
                            (at (SND(chart_at atlas x) x))
                            (mfd_vrep atlas Z (chart_at atlas x) (SND(chart_at atlas x) x)))`;;

let RFU_P2C_FGRAD2 = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) g f x.
        p2c_fgrad2 atlas g f x = rfu_mgrad2 atlas g f x`,
  REWRITE_TAC[p2c_fgrad2; rfu_mgrad2]);;

let RFU_KOT_MFD = prove
 (`!Lam B. ?C. &0 <= C /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b g1 g2 t x.
       ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
       a < t /\ t < b /\ x IN topspace top /\
       (!v. v dot (g2 t x ** v) <= Lam * (v dot (g1 t x ** v)) /\
            v dot (g1 t x ** v) <= Lam * (v dot (g2 t x ** v))) /\
       rfa_rmd2 0 atlas (g1 t) x <= B /\ rfa_rmd2 0 atlas (g2 t) x <= B /\
       rfa_rmd2 1 atlas (g2 t) x <= B /\ rfa_rmd2 2 atlas (g2 t) x <= B
       ==> ?d. ((\s. pde_mkot_density atlas (g1 s) (g2 s) x) has_real_derivative d)
               (atreal t) /\
               d <= mfd_div atlas (g1 t) (rfu_mkz atlas (g1 t) (g2 t)) x -
                    rfu_mxx atlas (g1 t) (g2 t) x +
                    C * pde_mkot_density atlas (g1 t) (g2 t) x /\
               (!f. mfd_smooth atlas (\y. lift(f y))
                    ==> abs(rfu_mdf atlas f (rfu_mkz atlas (g1 t) (g2 t)) x) <=
                        C * sqrt(pde_mkot_density atlas (g1 t) (g2 t) x) *
                        sqrt(rfu_mxx atlas (g1 t) (g2 t) x) *
                        sqrt(rfu_mgrad2 atlas (g1 t) f x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`Lam:real`; `B:real`] (INST_TYPE [`:N`,`:N`] RFU_KOT_NORM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                 `c:(A->bool)#(A->real^N)`; `t:real`; `x:A`] RFU_KOT_AT_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  EXISTS_TAC
   `rfu_edot (metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) t))
             (metric_local atlas c ((g2:real->A->real^N^N) t)) (SND c x)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lricci_flow (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) a b
                (\s. metric_local atlas c ((g1:real->A->real^N^N) s)) /\
    lricci_flow (IMAGE (SND c) (FST c)) a b
                (\s. metric_local atlas c ((g2:real->A->real^N^N) s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "C" (MP_TAC o SPECL
   [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
    `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) s)`;
    `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g2:real->A->real^N^N) s)`;
    `t:real`; `SND(c:(A->bool)#(A->real^N)) x`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!s. a <= s /\ s < b
          ==> metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) s)
                (SND c x) = g1 s x /\
              metric_local atlas c ((g2:real->A->real^N^N) s) (SND c x) = g2 s x`
    (fun th -> MP_TAC(SPEC `t:real` th)) THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfa_rmd2 0 atlas ((g1:real->A->real^N^N) t) x <= B` THEN
    UNDISCH_TAC `rfa_rmd2 0 atlas ((g2:real->A->real^N^N) t) x <= B` THEN
    UNDISCH_TAC `rfa_rmd2 1 atlas ((g2:real->A->real^N^N) t) x <= B` THEN
    UNDISCH_TAC `rfa_rmd2 2 atlas ((g2:real->A->real^N^N) t) x <= B` THEN
    ASM_REWRITE_TAC[rfa_rmd2] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF")) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[rfu_mxx]; ALL_TAC] THEN
  X_GEN_TAC `f:A->real` THEN DISCH_TAC THEN
  USE_THEN "DF" (MP_TAC o SPEC `\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\y. lift((f:A->real) y))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`; `(g2:real->A->real^N^N) t`;
                 `c:(A->bool)#(A->real^N)`; `SND(c:(A->bool)#(A->real^N)) x`] RFU_MKZ_VREP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[rfu_mdf; rfu_mxx; rfu_mgrad2; rfa_d1; o_DEF]);;

(* ========================================================================= *)
(* The cutoff profile rfu_chi (1 on (-inf,0], 0 on [1,inf)) and              *)
(* the weight-cutoff profiles rfu_wf lam R s = exp(-lam s) chi(s - R)^2.     *)
(* RFU_SMOOTH_REAL_DERIV and RFU_CONT_BOUNDED_INTERVAL are copies of         *)
(* RFA_SMOOTH_REAL_DERIV and RFA_CONT_BOUNDED_INTERVAL of pc_rfa_slcut, whose *)
(* closure (about 2.6 MB: comparison geometry and ODE layers) is not needed *)
(* here otherwise.                                                           *)
(* ========================================================================= *)

let RFU_SMOOTH_REAL_DERIV = prove
 (`!g. smooth_map_on (:real^1) (lift o g o drop)
       ==> smooth_map_on (:real^1) (lift o real_derivative g o drop) /\
           !x. (g has_real_derivative real_derivative g x) (atreal x)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. (g has_real_derivative real_derivative g x) (atreal x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN
    SUBGOAL_THEN `(lift o g o drop) differentiable (at (lift x))` MP_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[differentiable] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1` ASSUME_TAC) THEN
    SUBGOAL_THEN `linear(f':real^1->real^1)` MP_TAC THENL
     [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    REWRITE_TAC[LINEAR_1] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `(g has_real_derivative c) (atreal x)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lift o real_derivative g o drop =
    (\y. frechet_derivative (lift o g o drop) (at y) (lift(&1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `y:real^1` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop y`) THEN
    REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID];
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]]);;

let RFU_CONT_BOUNDED_INTERVAL = prove
 (`!f R. (lift o f o drop) continuous_on (:real^1)
         ==> ?C. !s. abs s <= R ==> abs(f s) <= C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `interval[lift(--R),lift R]`]
         COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* The cutoff profile. *)

let rfu_chi = new_definition
 `rfu_chi (s:real) = smooth_step(&1 - s)`;;

let RFU_CHI_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o rfu_chi o drop)`,
  REWRITE_TAC[o_DEF; rfu_chi] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&1 - drop x)`]
         SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&1)`; `\x:real^1. x`]
         SMOOTH_MAP_ON_LIFT_SUB) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

let RFU_CHI_VALUES = prove
 (`!s. &0 <= rfu_chi s /\ rfu_chi s <= &1 /\
       (s <= &0 ==> rfu_chi s = &1) /\ (&1 <= s ==> rfu_chi s = &0)`,
  GEN_TAC THEN REWRITE_TAC[rfu_chi; SMOOTH_STEP_BOUNDS] THEN CONJ_TAC THEN
  DISCH_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1; MATCH_MP_TAC SMOOTH_STEP_0] THEN ASM_REAL_ARITH_TAC);;

let RFU_CHI_DERIV = prove
 (`?D. &0 <= D /\
       !s. (rfu_chi has_real_derivative real_derivative rfu_chi s) (atreal s) /\
           abs(real_derivative rfu_chi s) <= D /\
           (s < &0 \/ &1 < s ==> real_derivative rfu_chi s = &0)`,
  MP_TAC(SPEC `rfu_chi` RFU_SMOOTH_REAL_DERIV) THEN REWRITE_TAC[RFU_CHI_SMOOTH] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. s < &0 \/ &1 < s ==> real_derivative rfu_chi s = &0` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`rfu_chi`; `s:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`\x:real. &1`; `--s:real`] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(SPEC `x:real` RFU_CHI_VALUES) THEN
      SUBGOAL_THEN `x <= &0` (fun th -> SIMP_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`\x:real. &0`; `s - &1`] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(SPEC `x:real` RFU_CHI_VALUES) THEN
      SUBGOAL_THEN `&1 <= x` (fun th -> SIMP_TAC[th]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`real_derivative rfu_chi`; `&2`] RFU_CONT_BOUNDED_INTERVAL) THEN
  ANTS_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN EXISTS_TAC `abs C:real` THEN
  REWRITE_TAC[REAL_ABS_POS] THEN X_GEN_TAC `s:real` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `abs s <= &2` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `real_derivative rfu_chi s = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* The weight-cutoff profile. *)

let rfu_wf = new_definition
 `rfu_wf (lam:real) (R:real) (s:real) = exp(--(lam * s)) * rfu_chi(s - R) pow 2`;;

let RFU_WF_SMOOTH = prove
 (`!lam R. smooth_map_on (:real^1) (lift o rfu_wf lam R o drop)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_DEF; rfu_wf] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(exp(--(lam * drop x)))`;
                 `\x:real^1. lift(rfu_chi(drop x - R) pow 2)`]
                SMOOTH_MAP_ON_LIFT_MUL) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(--(lam * drop x))`]
           SMOOTH_MAP_ON_LIFT_EXP) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_NEG; LIFT_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(rfu_chi(drop x - R))`; `2`]
         SMOOTH_MAP_ON_LIFT_POW) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `(:real^1)`; `\x:real^1. lift(drop x - R)`; `rfu_chi`]
         SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; IN_UNIV; RFU_CHI_SMOOTH] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. x`; `\x:real^1. lift R`]
         SMOOTH_MAP_ON_LIFT_SUB) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

let RFU_WF_DERIV = prove
 (`!lam R s.
        (rfu_wf lam R has_real_derivative
         (--lam * rfu_wf lam R s +
          exp(--(lam * s)) * (&2 * rfu_chi(s - R) * real_derivative rfu_chi (s - R))))
        (atreal s)`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CD")) RFU_CHI_DERIV THEN
  SUBGOAL_THEN
   `((\s. exp(--(lam * s))) has_real_derivative (exp(--(lam * s)) * --lam)) (atreal s)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. exp(--(lam * s))) = exp o (\s. --(lam * s))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_EXP] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
    MP_TAC(ISPECL [`\s:real. s`; `&1`; `lam:real`; `s:real`]
           HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. rfu_chi(s - R)) has_real_derivative real_derivative rfu_chi (s - R)) (atreal s)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s:real. rfu_chi(s - R)) = rfu_chi o (\s. s - R)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN
    USE_THEN "CD" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`\s:real. s`; `&1`; `\s:real. (R:real)`; `&0`; `atreal s`]
           HAS_REAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. rfu_chi(s - R) pow 2) has_real_derivative
     (&2 * rfu_chi(s - R) * real_derivative rfu_chi (s - R))) (atreal s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s:real. rfu_chi(s - R)`; `real_derivative rfu_chi (s - R)`;
                   `s:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfu_wf lam R = (\s. exp(--(lam * s)) * rfu_chi(s - R) pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rfu_wf]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. exp(--(lam * s))`; `exp(--(lam * s)) * --lam`;
                 `\s:real. rfu_chi(s - R) pow 2`;
                 `&2 * rfu_chi(s - R) * real_derivative rfu_chi (s - R)`; `s:real`]
                HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) net
                                   ==> (f has_real_derivative b) net`) THEN
  REAL_ARITH_TAC);;

let RFU_WF_VALUES = prove
 (`!lam R s.
        &0 <= rfu_wf lam R s /\ rfu_wf lam R s <= exp(--(lam * s)) /\
        (s <= R ==> rfu_wf lam R s = exp(--(lam * s))) /\
        (R + &1 <= s ==> rfu_wf lam R s = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfu_wf] THEN
  MP_TAC(SPEC `s - R:real` RFU_CHI_VALUES) THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_LE_POW_2];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `rfu_chi(s - R) = &1` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID];
    DISCH_TAC THEN
    SUBGOAL_THEN `rfu_chi(s - R) = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_MUL_RZERO]]);;

(* ========================================================================= *)
(* The test functions psi = rfu_wf lam R o phi on the manifold               *)
(* and the pointwise inequality for e psi (RFU_KOT_TEST):                    *)
(*   d(e psi)/dt <= div(psi Z) + K2 e psi + K3 exp(-lam phi) chi'^2 e,       *)
(* the cross term df(Z) being absorbed by the kept good term -|X|^2.         *)
(* ========================================================================= *)

let RFU_PSI_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) phi lam R.
        smooth_manifold_atlas top atlas /\ mfd_smooth atlas (lift o phi)
        ==> mfd_smooth atlas (\x. lift(rfu_wf lam R (phi x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:A. lift(rfu_wf lam R (phi x))) o chart_inv (c:(A->bool)#(A->real^N)) =
    (\y. lift(rfu_wf lam R (drop(((lift o phi) o chart_inv c) y))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; RFU_WF_SMOOTH; ETA_AX] THEN
  UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (lift o phi)` THEN
  REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The derivative along Z of F o phi. *)

let RFU_MDF_COMPOSE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (phi:A->real) (FF:real->real) FF' Z x.
        smooth_manifold_atlas top atlas /\ x IN topspace top /\
        mfd_smooth atlas (lift o phi) /\ (FF has_real_derivative FF') (atreal (phi x))
        ==> rfu_mdf atlas (\y. FF(phi y)) Z x = FF' * rfu_mdf atlas phi Z x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rfu_mdf] THEN
  MP_TAC(ISPECL [`\y. (phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)`;
                 `FF:real->real`; `FF':real`; `SND(c:(A->bool)#(A->real^N)) x`;
                 `mfd_vrep atlas (Z:A->real^N) (c:(A->bool)#(A->real^N)) (SND c x)`]
                RFA_D1_COMPOSE_AT) THEN
  REWRITE_TAC[rfa_d1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (lift o phi)` THEN
  REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Two weighted arithmetic-geometric mean inequalities. *)

let RFU_AMGM1 = prove
 (`!W0 a b. &0 <= W0 ==> W0 * a * b <= W0 * a pow 2 / &2 + W0 * b pow 2 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W0:real`; `(a - b) pow 2`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC);;

let RFU_AMGM2 = prove
 (`!w a b. &0 <= w ==> &2 * w * a * b <= w * a pow 2 / &2 + &2 * w * b pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real`; `(a - &2 * b) pow 2`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC);;

(* The algebra of the absorption, with se = sqrt e and sx = |X|. *)

let RFU_TEST_ALG = prove
 (`!d dv se sx m w c q lam K1 C.
        &0 <= se /\ &0 <= sx /\ &0 <= w /\ &0 <= lam /\ &0 <= K1 /\
        d <= dv - sx pow 2 + C * se pow 2 /\
        abs m <= K1 * se * sx
        ==> d * (w * c pow 2) <=
            ((w * c pow 2) * dv + (--lam * (w * c pow 2) + w * (&2 * c * q)) * m) +
            (C + lam pow 2 * K1 pow 2 / &2) * se pow 2 * (w * c pow 2) +
            &2 * K1 pow 2 * w * q pow 2 * se pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= w * c pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `d * (w * c pow 2) <= (dv - sx pow 2 + C * se pow 2) * (w * c pow 2)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `--((--lam * (w * c pow 2) + w * (&2 * c * q)) * m) <=
    lam * (w * c pow 2) * (K1 * se * sx) + &2 * w * (abs c * sx) * (abs q * K1 * se)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> --x <= y`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(lam * (w * c pow 2) + &2 * w * abs c * abs q) * (K1 * se * sx)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs a <= A /\ abs b <= B ==> abs(a + b) <= A + B`) THEN
      CONJ_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM; REAL_ABS_POW] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_POW2_ABS] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w * c pow 2`; `sx:real`; `lam * K1 * se`] RFU_AMGM1) THEN
  MP_TAC(ISPECL [`w:real`; `abs c * sx`; `abs q * K1 * se`] RFU_AMGM2) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS] THEN
  ASM_REAL_ARITH_TAC);;

(* The chart representatives of the Kotschwar field are smooth. *)

let RFU_MKZ_VREP_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g1 g2 c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
        riemannian_metric atlas g2 /\ c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas (rfu_mkz atlas g1 g2) c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `rfu_kz (metric_local atlas (c:(A->bool)#(A->real^N)) (g1:A->real^N^N))
                     (metric_local atlas c (g2:A->real^N^N))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFU_MKZ_VREP THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFU_KZ_SMOOTH THEN ASM_MESON_TAC[riemannian_metric]]);;

(* Nonnegativity of the manifold scalars |X|^2 and |df|^2. *)

let RFU_MXX_MGRAD2_POS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g1 g2 (f:A->real) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
        riemannian_metric atlas g2 /\ x IN topspace top
        ==> &0 <= rfu_mxx atlas g1 g2 x /\ &0 <= rfu_mgrad2 atlas g1 f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c (g1:A->real^N^N)) /\
    metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (g2:A->real^N^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rfu_mxx; rfu_mgrad2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[RFU_X_FIELD];
    MATCH_MP_TAC LGRAD2_POS THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[]]);;

(* The pointwise inequality for e psi. *)

let RFU_KOT_TEST = prove
 (`!Lam B Cp lam. &0 <= lam
     ==> ?K2 K3. &0 <= K2 /\ &0 <= K3 /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b g1 g2 phi R t x.
       ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
       a < t /\ t < b /\ x IN topspace top /\
       (!v. v dot (g2 t x ** v) <= Lam * (v dot (g1 t x ** v)) /\
            v dot (g1 t x ** v) <= Lam * (v dot (g2 t x ** v))) /\
       rfa_rmd2 0 atlas (g1 t) x <= B /\ rfa_rmd2 0 atlas (g2 t) x <= B /\
       rfa_rmd2 1 atlas (g2 t) x <= B /\ rfa_rmd2 2 atlas (g2 t) x <= B /\
       mfd_smooth atlas (lift o phi) /\ rfu_mgrad2 atlas (g1 t) phi x <= Cp
       ==> ?d. ((\s. pde_mkot_density atlas (g1 s) (g2 s) x) has_real_derivative d)
               (atreal t) /\
               d * rfu_wf lam R (phi x) <=
               mfd_div atlas (g1 t)
                 (\y. rfu_wf lam R (phi y) % rfu_mkz atlas (g1 t) (g2 t) y) x +
               K2 * pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x) +
               K3 * exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2 *
                    pde_mkot_density atlas (g1 t) (g2 t) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`Lam:real`; `B:real`] (INST_TYPE [`:N`,`:N`] RFU_KOT_MFD)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  ABBREV_TAC `K1 = C * sqrt(abs Cp)` THEN
  SUBGOAL_THEN `&0 <= K1` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  EXISTS_TAC `C + lam pow 2 * K1 pow 2 / &2` THEN EXISTS_TAC `&2 * K1 pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "C" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
    `g1:real->A->real^N^N`; `g2:real->A->real^N^N`; `t:real`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF")))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) t) /\
                riemannian_metric atlas ((g2:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the product rule *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`; `\y:A. rfu_wf lam R (phi y)`;
                 `rfu_mkz atlas ((g1:real->A->real^N^N) t) (g2 t)`; `x:A`]
                RFU_MFD_DIV_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFU_PSI_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC RFU_MKZ_VREP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM rfu_mdf] THEN DISCH_THEN SUBST1_TAC THEN
  (* the chain rule for psi = F o phi *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `phi:A->real`;
                 `rfu_wf lam R`;
                 `--lam * rfu_wf lam R ((phi:A->real) x) +
                  exp(--(lam * phi x)) *
                  (&2 * rfu_chi(phi x - R) * real_derivative rfu_chi (phi x - R))`;
                 `rfu_mkz atlas ((g1:real->A->real^N^N) t) (g2 t)`; `x:A`]
                RFU_MDF_COMPOSE) THEN
  ASM_REWRITE_TAC[RFU_WF_DERIV] THEN DISCH_THEN SUBST1_TAC THEN
  (* the absorption *)
  USE_THEN "DF" (MP_TAC o SPEC `phi:A->real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM o_DEF] THEN ASM_REWRITE_TAC[o_DEF] THEN
                  ASM_MESON_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                 `(g1:real->A->real^N^N) t`; `(g2:real->A->real^N^N) t`; `x:A`]
                PDE_KOT_DENSITY_ZERO) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`; `(g2:real->A->real^N^N) t`;
                 `phi:A->real`; `x:A`] RFU_MXX_MGRAD2_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `e = pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x` THEN
  ABBREV_TAC `xx = rfu_mxx atlas ((g1:real->A->real^N^N) t) (g2 t) x` THEN
  MP_TAC(ISPECL
   [`d:real`; `mfd_div atlas ((g1:real->A->real^N^N) t) (rfu_mkz atlas (g1 t) (g2 t)) x`;
    `sqrt e`; `sqrt xx`;
    `rfu_mdf atlas (phi:A->real) (rfu_mkz atlas ((g1:real->A->real^N^N) t) (g2 t)) x`;
    `exp(--(lam * (phi:A->real) x))`; `rfu_chi((phi:A->real) x - R)`;
    `real_derivative rfu_chi ((phi:A->real) x - R)`; `lam:real`; `K1:real`; `C:real`]
   RFU_TEST_ALG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_EXP_POS_LE; SQRT_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `C * sqrt e * sqrt xx *
      sqrt(rfu_mgrad2 atlas ((g1:real->A->real^N^N) t) (phi:A->real) x)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K1" THEN
    REWRITE_TAC[REAL_ARITH `(C * s) * se * sx = (C * se * sx) * s:real`] THEN
    REWRITE_TAC[REAL_ARITH `C * se * sx * s = (C * se * sx) * s:real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[SQRT_POS_LE];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rfu_wf] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The cut-off weighted energy E(t) = int_S e psi dV_g1(t) on                *)
(* S = {phi <= R + 1}: smoothness up to t = a of the integrands, continuity *)
(* and differentiability of E (RFU_ENERGY_SETUP).                            *)
(* ========================================================================= *)

let RFU_SFUN_MUL_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real) (f:A->real).
     smooth_manifold_atlas top atlas /\ pde_sfun_from atlas a b e /\
     mfd_smooth atlas (\x. lift(f x))
     ==> pde_sfun_from atlas a b (\t x. e t x * f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_sfun_from] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  UNDISCH_TAC `pde_sfun_from (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real)` THEN
  REWRITE_TAC[pde_sfun_from] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN
  EXISTS_TAC `\z. lift(drop((FF:real^(1,N)finite_sum->real^1) z) *
                       (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`interval(lift(a - d),lift b) PCROSS
                    IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                   `FF:real^(1,N)finite_sum->real^1`;
                   `\z:real^(1,N)finite_sum.
                      lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))`]
                  SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    SUBGOAL_THEN
     `(\z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))) =
      (\y. lift(f(chart_inv c y))) o (sndcart:real^(1,N)finite_sum->real^N)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  SNDCART_PASTECART] THEN SIMP_TAC[];
      SUBGOAL_THEN `(sndcart:real^(1,N)finite_sum->real^N) = sndcart o (\z. z)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_ID];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SNDCART_PASTECART; LIFT_DROP]]);;

(* The density has the derivative rfu_tder on (a,b). *)

let RFU_DENS_TDER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b g1 g2 t x.
     ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
     a < t /\ t < b /\ x IN topspace top
     ==> ((\s. pde_mkot_density atlas (g1 s) (g2 s) x) has_real_derivative
          rfu_tder a (\s. pde_mkot_density atlas (g1 s) (g2 s)) t x) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `t:real`; `x:A`]
                RFU_KOT_AT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)) t x =
    rfu_edot (metric_local atlas (chart_at atlas x) (g1 t))
             (metric_local atlas (chart_at atlas x) (g2 t))
             (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFU_TDER_UNIQUE THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BETA_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The energy: integrability, continuity on [a,b) and the derivative. *)

let RFU_ENERGY_SETUP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b g1 g2 (f:A->real) S.
     hausdorff_space top /\
     ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
     mfd_smooth atlas (\x. lift(f x)) /\ compact_in top S
     ==> (!s. a <= s /\ s < b
              ==> mfd_integrable_on (top,atlas) (g1 s)
                    (\x. pde_mkot_density atlas (g1 s) (g2 s) x * f x) S) /\
         (!t. a < t /\ t < b
              ==> mfd_integrable_on (top,atlas) (g1 t)
                    (\x. rfu_tder a (\s. pde_mkot_density atlas (g1 s) (g2 s)) t x * f x -
                         mfd_scalar atlas (g1 t) x *
                         (pde_mkot_density atlas (g1 t) (g2 t) x * f x)) S) /\
         (\s. mfd_integral (top,atlas) (g1 s) S
                (\x. pde_mkot_density atlas (g1 s) (g2 s) x * f x))
           real_continuous_on {s | a <= s /\ s < b} /\
         !t. a < t /\ t < b
             ==> ((\s. mfd_integral (top,atlas) (g1 s) S
                        (\x. pde_mkot_density atlas (g1 s) (g2 s) x * f x))
                  has_real_derivative
                  mfd_integral (top,atlas) (g1 t) S
                    (\x. rfu_tder a (\s. pde_mkot_density atlas (g1 s) (g2 s)) t x * f x -
                         mfd_scalar atlas (g1 t) x *
                         (pde_mkot_density atlas (g1 t) (g2 t) x * f x))) (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_sfun_from atlas a b
      (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_MKOT_SFUN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
    `g1:real->A->real^N^N`;
    `\t x. pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x * (f:A->real) x`;
    `\t x. rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)) t x *
           (f:A->real) x`;
    `S:A->bool`] RFU_INTEGRAL_RF_DERIV_ON) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`;
                     `\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)`;
                     `f:A->real`] RFU_SFUN_MUL_SMOOTH) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`;
                     `rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s))`;
                     `f:A->real`] RFU_SFUN_MUL_SMOOTH) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC RFU_SFUN_TDER THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `x:A`] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
      MATCH_MP_TAC RFU_DENS_TDER THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`] THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The differential inequality of the cut-off weighted energy                *)
(* (RFU_ENERGY_DERIV_BOUND):                                                 *)
(*   E'(t) <= (K2 + H) E(t) + K3 |M| exp(-lam R) Vol_g1(t)(S),               *)
(* with the divergence term integrated out (RFU_DIVERGENCE_ON).              *)
(* ========================================================================= *)

let RFU_VREP_MUL_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (psi:A->real) (Z:A->real^N) c.
        smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(psi x)) /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c)) /\
        c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas (\x. psi x % Z x) c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\y. drop(((\x. lift((psi:A->real) x)) o chart_inv (c:(A->bool)#(A->real^N))) y) %
        mfd_vrep atlas (Z:A->real^N) c y` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `Z:A->real^N`; `psi:A->real`;
                   `(\i x. vec 0):num->A->real^N`; `0`;
                   `c:(A->bool)#(A->real^N)`; `y:real^N`] GRGT_VREP_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((psi:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth] THEN ASM_SIMP_TAC[]]);;

(* The error weight exp(-lam phi) chi'(phi - R)^2 is smooth. *)

let RFU_ERRW_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) phi lam R.
        smooth_manifold_atlas top atlas /\ mfd_smooth atlas (lift o phi)
        ==> mfd_smooth atlas
              (\x. lift(exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `rfu_chi` RFU_SMOOTH_REAL_DERIV) THEN REWRITE_TAC[RFU_CHI_SMOOTH] THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                  ((lift o phi) o chart_inv c)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (lift o phi)` THEN
    REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:A. lift(exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2)) o
    chart_inv (c:(A->bool)#(A->real^N)) =
    (\y. lift(drop((\y. lift(exp(drop(lift(--(lam * drop(((lift o phi) o chart_inv c) y))))))) y) *
              drop((\y. lift(drop(lift(real_derivative rfu_chi
                       (drop(((lift o phi) o chart_inv c) y) - R))) pow 2)) y)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_EXP THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_NEG; LIFT_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_POW THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `(:real^1)`;
                 `\y:real^N. lift(drop(((lift o phi) o chart_inv (c:(A->bool)#(A->real^N))) y) -
                                  R)`;
                 `real_derivative rfu_chi`] SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `(lift o phi) o chart_inv (c:(A->bool)#(A->real^N))`;
                 `\y:real^N. lift(R:real)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST]);;

(* The differential inequality. *)

let RFU_ENERGY_DERIV_BOUND = prove
 (`!Lam B Cp lam. &0 <= lam
    ==> ?K2 K3. &0 <= K2 /\ &0 <= K3 /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b g1 g2 phi R H M t.
       hausdorff_space top /\
       ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
       a < t /\ t < b /\ &0 <= H /\ mfd_smooth atlas (lift o phi) /\
       compact_in top {x | x IN topspace top /\ phi x <= R + &1} /\
       (!x. x IN topspace top
            ==> (!v. v dot (g2 t x ** v) <= Lam * (v dot (g1 t x ** v)) /\
                     v dot (g1 t x ** v) <= Lam * (v dot (g2 t x ** v))) /\
                rfa_rmd2 0 atlas (g1 t) x <= B /\ rfa_rmd2 0 atlas (g2 t) x <= B /\
                rfa_rmd2 1 atlas (g2 t) x <= B /\ rfa_rmd2 2 atlas (g2 t) x <= B /\
                rfu_mgrad2 atlas (g1 t) phi x <= Cp /\
                --H <= mfd_scalar atlas (g1 t) x /\
                pde_mkot_density atlas (g1 t) (g2 t) x <= M)
       ==> mfd_integral (top,atlas) (g1 t) {x | x IN topspace top /\ phi x <= R + &1}
             (\x. rfu_tder a (\s. pde_mkot_density atlas (g1 s) (g2 s)) t x *
                  rfu_wf lam R (phi x) -
                  mfd_scalar atlas (g1 t) x *
                  (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x)))
           <= (K2 + H) *
              mfd_integral (top,atlas) (g1 t) {x | x IN topspace top /\ phi x <= R + &1}
                (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x)) +
              K3 * abs M * exp(--(lam * R)) *
              mfd_volume (top,atlas) (g1 t) {x | x IN topspace top /\ phi x <= R + &1}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`Lam:real`; `B:real`; `Cp:real`; `lam:real`]
               (INST_TYPE [`:N`,`:N`] RFU_KOT_TEST)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:real` (X_CHOOSE_THEN `K3:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T"))))) THEN
  X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CD")) RFU_CHI_DERIV THEN
  EXISTS_TAC `K2:real` THEN EXISTS_TAC `K3 * D pow 2` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "PT") THEN
  ABBREV_TAC `S = {x:A | x IN topspace top /\ phi x <= R + &1}` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) t) /\
                riemannian_metric atlas ((g2:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(rfu_wf lam R (phi x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_PSI_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
      (\x. lift(exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_ERRW_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN];
    ALL_TAC] THEN
  (* the integrals *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                 `\x:A. rfu_wf lam R (phi x)`; `S:A->bool`]
                RFU_ENERGY_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `t:real`)
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `t:real`) (K ALL_TAC))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN DISCH_THEN(LABEL_TAC "I2") THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN DISCH_THEN(LABEL_TAC "I1") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                 `\x:A. exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2`;
                 `S:A->bool`] RFU_ENERGY_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN DISCH_THEN(LABEL_TAC "I3") THEN
  (* the divergence term *)
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) ((g1:real->A->real^N^N) t)
      (mfd_div atlas (g1 t) (\y. rfu_wf lam R (phi y) % rfu_mkz atlas (g1 t) (g2 t) y))
      S (&0)`
  (LABEL_TAC "ID") THENL
   [MATCH_MP_TAC RFU_DIVERGENCE_ON THEN EXISTS_TAC `S:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `rfu_wf lam R ((phi:A->real) x) = &0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
      MP_TAC(SPECL [`lam:real`; `R:real`; `(phi:A->real) x`] RFU_WF_VALUES) THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      UNDISCH_TAC `~((x:A) IN S)` THEN EXPAND_TAC "S" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC(BETA_RULE(ISPECL
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `\y:A. rfu_wf lam R ((phi:A->real) y)`;
        `rfu_mkz atlas ((g1:real->A->real^N^N) t) (g2 t)`] RFU_VREP_MUL_SMOOTH)) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC RFU_MKZ_VREP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the pointwise inequality *)
  SUBGOAL_THEN
   `!x. x IN S
        ==> rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)) t x *
            rfu_wf lam R (phi x) -
            mfd_scalar atlas (g1 t) x *
            (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x))
            <= mfd_div atlas (g1 t)
                 (\y. rfu_wf lam R (phi y) % rfu_mkz atlas (g1 t) (g2 t) y) x +
               (K2 + H) * (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x)) +
               K3 * (pde_mkot_density atlas (g1 t) (g2 t) x *
                     (exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2))`
  (LABEL_TAC "PW") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "PT" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
    USE_THEN "T" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
      `g1:real->A->real^N^N`; `g2:real->A->real^N^N`; `phi:A->real`; `R:real`;
      `t:real`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)) t x = d`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
      MAP_EVERY EXISTS_TAC
       [`\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s) x`; `t:real`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFU_DENS_TDER THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                   `(g1:real->A->real^N^N) t`; `(g2:real->A->real^N^N) t`; `x:A`]
                  PDE_KOT_DENSITY_ZERO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`lam:real`; `R:real`; `(phi:A->real) x`] RFU_WF_VALUES) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 <= pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
            rfu_wf lam R ((phi:A->real) x)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`--H:real`; `mfd_scalar atlas ((g1:real->A->real^N^N) t) x`;
                  `pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
                   rfu_wf lam R ((phi:A->real) x)`] REAL_LE_RMUL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `d * rfu_wf lam R ((phi:A->real) x) <=
      mfd_div atlas ((g1:real->A->real^N^N) t)
        (\y. rfu_wf lam R (phi y) % rfu_mkz atlas (g1 t) (g2 t) y) x +
      K2 * pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x) +
      K3 * exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2 *
           pde_mkot_density atlas (g1 t) (g2 t) x` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* integrate *)
  ABBREV_TAC
   `I1 = mfd_integral (top,atlas) ((g1:real->A->real^N^N) t) S
           (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R ((phi:A->real) x))` THEN
  ABBREV_TAC
   `I3 = mfd_integral (top,atlas) ((g1:real->A->real^N^N) t) S
           (\x. pde_mkot_density atlas (g1 t) (g2 t) x *
                exp(--(lam * (phi:A->real) x)) * real_derivative rfu_chi (phi x - R) pow 2)` THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) ((g1:real->A->real^N^N) t)
      (\x. mfd_div atlas (g1 t)
             (\y. rfu_wf lam R ((phi:A->real) y) % rfu_mkz atlas (g1 t) (g2 t) y) x +
           (K2 + H) * (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x)) +
           K3 * (pde_mkot_density atlas (g1 t) (g2 t) x *
                 (exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2)))
      S (&0 + (K2 + H) * I1 + K3 * I3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[ETA_AX] (BETA_RULE(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(g1:real->A->real^N^N) t`;
      `mfd_div atlas ((g1:real->A->real^N^N) t)
         (\y. rfu_wf lam R ((phi:A->real) y) % rfu_mkz atlas (g1 t) (g2 t) y)`;
      `\x. (K2 + H) * (pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
                       rfu_wf lam R ((phi:A->real) x)) +
           K3 * (pde_mkot_density atlas (g1 t) (g2 t) x *
                 (exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2))`;
      `S:A->bool`; `&0`; `(K2 + H) * I1 + K3 * I3`] MFD_HAS_INTEGRAL_ADD))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(g1:real->A->real^N^N) t`;
      `\x. (K2 + H) * (pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
                       rfu_wf lam R ((phi:A->real) x))`;
      `\x. K3 * (pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
                 (exp(--(lam * (phi:A->real) x)) * real_derivative rfu_chi (phi x - R) pow 2))`;
      `S:A->bool`; `(K2 + H) * I1`; `K3 * I3`] MFD_HAS_INTEGRAL_ADD)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC(BETA_RULE MFD_HAS_INTEGRAL_CMUL) THEN
    MAP_EVERY EXPAND_TAC ["I1"; "I3"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_integral (top,atlas) ((g1:real->A->real^N^N) t) S
      (\x. rfu_tder a (\s. pde_mkot_density atlas (g1 s) (g2 s)) t x *
           rfu_wf lam R ((phi:A->real) x) -
           mfd_scalar atlas (g1 t) x *
           (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x)))
    <= &0 + (K2 + H) * I1 + K3 * I3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(g1:real->A->real^N^N) t`;
      `\x. rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)) t x *
           rfu_wf lam R ((phi:A->real) x) -
           mfd_scalar atlas (g1 t) x *
           (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x))`;
      `\x. mfd_div atlas ((g1:real->A->real^N^N) t)
             (\y. rfu_wf lam R ((phi:A->real) y) % rfu_mkz atlas (g1 t) (g2 t) y) x +
           (K2 + H) * (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x)) +
           K3 * (pde_mkot_density atlas (g1 t) (g2 t) x *
                 (exp(--(lam * phi x)) * real_derivative rfu_chi (phi x - R) pow 2))`;
      `S:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "PW" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  (* the error integral *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`; `S:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`; `S:A->bool`; `v:real`] MFD_HAS_VOLUME_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `I3 <= (D pow 2 * abs M * exp(--(lam * R))) * v` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(g1:real->A->real^N^N) t`;
      `\x. pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
           exp(--(lam * (phi:A->real) x)) * real_derivative rfu_chi (phi x - R) pow 2`;
      `\x:A. D pow 2 * abs M * exp(--(lam * R))`; `S:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_HAS_INTEGRAL_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "PT" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                   `(g1:real->A->real^N^N) t`; `(g2:real->A->real^N^N) t`; `x:A`]
                  PDE_KOT_DENSITY_ZERO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "CD" (STRIP_ASSUME_TAC o SPEC `(phi:A->real) x - R`) THEN
    ASM_CASES_TAC `(phi:A->real) x - R < &0` THENL
     [SUBGOAL_THEN `real_derivative rfu_chi ((phi:A->real) x - R) = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_MUL_RZERO] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS; REAL_EXP_POS_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(lam * (phi:A->real) x)) <= exp(--(lam * R))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `lam * R <= lam * p ==> --(lam * p) <= --(lam * R)`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `real_derivative rfu_chi ((phi:A->real) x - R) pow 2 <= D pow 2`
    ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs M * (exp(--(lam * R)) * D pow 2)` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `e <= M ==> e <= abs M`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE; REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K3:real`; `I3:real`; `(D pow 2 * abs M * exp(--(lam * R))) * v`]
               REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `mfd_integral (top,atlas) ((g1:real->A->real^N^N) t) S
      (\x. rfu_tder a (\s. pde_mkot_density atlas (g1 s) (g2 s)) t x *
           rfu_wf lam R ((phi:A->real) x) -
           mfd_scalar atlas (g1 t) x *
           (pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x)))
    <= &0 + (K2 + H) * I1 + K3 * I3` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Tools for the limit R -> infinity: a nonnegative function                 *)
(* continuous in charts with integral 0 over S vanishes on any open subset  *)
(* of S (RFU_INTEGRAL_ZERO_IMP_ON, adapted from RFU_MFD_INTEGRAL_ZERO_IMP),   *)
(* integrals of functions vanishing off a subset, and Gronwall with a        *)
(* constant forcing term (RFU_GRONWALL_FORCED).                              *)
(* ========================================================================= *)

let RFU_INTEGRAL_ZERO_IMP_ON = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f S O x0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x. x IN S ==> &0 <= f x) /\
     mfd_has_integral (top,atlas) g f S (&0) /\
     (!c. c IN atlas
          ==> (\y. lift(f(chart_inv c y))) continuous_on IMAGE (SND c) (FST c)) /\
     open_in top O /\ O SUBSET S /\ x0 IN O
     ==> f x0 = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "fpos") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "fcont") STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_HAS_INTEGRAL_IMP_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_lebesgue_measurable]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x0:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W = FST (c:(A->bool)#(A->real^N)) INTER O` THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ W SUBSET FST(c:(A->bool)#(A->real^N)) /\
                W SUBSET S /\ (x0:A) IN W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_lebesgue_measurable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) W /\
    mfd_lebesgue_measurable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (S DIFF W)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_integrable_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
      (g:A->real^N^N) (f:A->real) W /\
    mfd_integrable_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) g f (S DIFF W)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN
    EXISTS_TAC `S:A->bool` THEN
    ASM_REWRITE_TAC[mfd_integrable_on; SUBSET_DIFF] THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN
  ABBREV_TAC `v = mfd_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                    (g:A->real^N^N) W (f:A->real)` THEN
  ABBREV_TAC `w = mfd_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                    (g:A->real^N^N) (S DIFF W) (f:A->real)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!T0 v. mfd_has_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
            (g:A->real^N^N) (f:A->real) T0 v /\ T0 SUBSET S
          ==> &0 <= v`
  (LABEL_TAC "nn") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\x:A. &0 * f x`; `f:A->real`; `T0:A->bool`;
                   `&0 * v'`; `v':real`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CMUL] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      USE_THEN "fpos" MATCH_MP_TAC THEN ASM SET_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v /\ &0 <= w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "nn" MATCH_MP_TAC THENL
     [EXISTS_TAC `W:A->bool`; EXISTS_TAC `S DIFF W:A->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `v = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `W:A->bool`;
                   `S DIFF W:A->bool`; `v:real`; `w:real`]
                  MFD_HAS_INTEGRAL_UNION) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(W:A->bool) UNION (S DIFF W) = S` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `S:A->bool`;
                   `v + w:real`; `&0`] MFD_HAS_INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`;
                 `W:A->bool`; `v:real`] MFD_HAS_INTEGRAL_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) W)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(mfd_chart_integrand atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N)) has_integral vec 0)
      (IMAGE (SND c) W)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`mfd_chart_integrand atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N))`;
                   `IMAGE (SND (c:(A->bool)#(A->real^N))) W`] HAS_INTEGRAL_INTEGRAL) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) HAS_INTEGRAL_NEGLIGIBLE_EQ o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`y:real^N`; `i:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `i = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_chart_integrand; GSYM drop; LIFT_DROP] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN W` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) W` THEN
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [USE_THEN "fpos" MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  CONJ_TAC THENL [USE_THEN "fpos" MATCH_MP_TAC THEN ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `{y | y IN IMAGE (SND (c:(A->bool)#(A->real^N))) W /\
                     lift(f(chart_inv c y)) IN {z:real^1 | z$1 > &0}}`
               OPEN_NOT_NEGLIGIBLE) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    CONJ_TAC THENL
     [USE_THEN "fcont" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `SND (c:(A->bool)#(A->real^N)) x0` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] NEGLIGIBLE_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM drop; LIFT_DROP; mfd_chart_integrand] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC GRGV_DENSITY_POS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) W` THEN
    UNDISCH_TAC `(W:A->bool) SUBSET FST(c:(A->bool)#(A->real^N))` THEN SET_TAC[]]);;

(* Gronwall with a constant forcing term. *)

let RFU_GRONWALL_FORCED = prove
 (`!(q:real->real) q' K eps a t.
     a < t /\ &0 < K /\ &0 <= eps /\ q a = &0 /\
     q real_continuous_on real_interval[a,t] /\
     (!s. a < s /\ s < t ==> (q has_real_derivative q' s) (atreal s)) /\
     (!s. a < s /\ s < t ==> q' s <= K * q s + eps)
     ==> q t <= eps / K * exp(K * (t - a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real. q s + eps / K`; `q':real->real`; `K:real`; `a:real`; `t:real`]
         RFU_GRONWALL_UP) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
      ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_CONST];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN
  SUBGOAL_THEN `&0 <= eps / K` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The Gronwall estimate of the cut-off weighted energy                      *)
(* (RFU_ENERGY_GRONWALL) and its monotonicity in the cutoff radius           *)
(* (RFU_ENERGY_MONO_R).                                                      *)
(* ========================================================================= *)

let RFU_OPEN_SUBLEVEL_NBHD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) phi x0 c0.
        smooth_manifold_atlas top atlas /\ mfd_smooth atlas (lift o phi) /\
        x0 IN topspace top /\ phi x0 < c0
        ==> ?O. open_in top O /\ x0 IN O /\
                (!x. x IN O ==> x IN topspace top /\ phi x < c0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x0:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `V = {y | y IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c) /\
             ((lift o phi) o chart_inv c) y IN {z:real^1 | z$1 < c0}}` THEN
  SUBGOAL_THEN `open(V:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (lift o phi)` THEN
    REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{z:A | z IN FST(c:(A->bool)#(A->real^N)) /\ SND c z IN V}` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `V:real^N->bool`] GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop; LIFT_DROP] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x0) = x0` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop; LIFT_DROP] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]]);;

let RFU_CV_EXP_ABS = prove
 (`!Cv r. Cv * exp(Cv * r) <= abs Cv * exp(abs Cv * r)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= Cv` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --c * e ==> c * e <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_EXP_POS_LE]]]);;

(* The integral of a function vanishing on S is 0; nonnegative functions    *)
(* have nonnegative integrals.                                               *)

let RFU_INTEGRAL_ZERO_FUN = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f S.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_in top S /\ (!x. x IN S ==> f x = &0)
        ==> mfd_has_integral (top,atlas) g f S (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `S:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `S:A->bool`; `v:real`; `&0`] MFD_HAS_INTEGRAL_CONST) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_SIMP_TAC[]);;

let RFU_INTEGRAL_NONNEG = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f S.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_in top S /\
        mfd_integrable_on (top,atlas) g f S /\ (!x. x IN S ==> &0 <= f x)
        ==> &0 <= mfd_integral (top,atlas) g S f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\x:A. &0`; `f:A->real`; `S:A->bool`] THEN
  ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
  MATCH_MP_TAC RFU_INTEGRAL_ZERO_FUN THEN ASM_REWRITE_TAC[]);;

(* The Gronwall estimate. *)

let RFU_ENERGY_GRONWALL = prove
 (`!Lam B Cp lam. &0 <= lam
    ==> ?K2 K3. &0 <= K2 /\ &0 <= K3 /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b b1 g1 g2 phi H M Cv R t.
       hausdorff_space top /\
       ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
       b1 < b /\ a < t /\ t <= b1 /\ &0 <= R /\
       (!x. x IN topspace top ==> g1 a x = g2 a x) /\
       mfd_smooth atlas (lift o phi) /\
       compact_in top {x | x IN topspace top /\ phi x <= R + &1} /\
       &0 <= H /\
       (!s x. a <= s /\ s <= b1 /\ x IN topspace top
              ==> (!v. v dot (g2 s x ** v) <= Lam * (v dot (g1 s x ** v)) /\
                       v dot (g1 s x ** v) <= Lam * (v dot (g2 s x ** v))) /\
                  rfa_rmd2 0 atlas (g1 s) x <= B /\ rfa_rmd2 0 atlas (g2 s) x <= B /\
                  rfa_rmd2 1 atlas (g2 s) x <= B /\ rfa_rmd2 2 atlas (g2 s) x <= B /\
                  rfu_mgrad2 atlas (g1 s) phi x <= Cp /\
                  --H <= mfd_scalar atlas (g1 s) x /\
                  pde_mkot_density atlas (g1 s) (g2 s) x <= M) /\
       (!s r v. a <= s /\ s <= b1 /\ &0 <= r /\
                mfd_has_volume (top,atlas) (g1 s) {x | x IN topspace top /\ phi x <= r} v
                ==> v <= Cv * exp(Cv * r))
       ==> mfd_integral (top,atlas) (g1 t) {x | x IN topspace top /\ phi x <= R + &1}
             (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x))
           <= (K3 * abs M * exp(--(lam * R)) * (abs Cv * exp(abs Cv * (R + &1)))) /
              (K2 + H + &1) * exp((K2 + H + &1) * (t - a))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`Lam:real`; `B:real`; `Cp:real`; `lam:real`]
               (INST_TYPE [`:N`,`:N`] RFU_ENERGY_DERIV_BOUND)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:real` (X_CHOOSE_THEN `K3:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))))) THEN
  EXISTS_TAC `K2:real` THEN EXISTS_TAC `K3:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "VOL") THEN
  FIRST_X_ASSUM(LABEL_TAC "BD" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfa_rmd2")) (concl th))) THEN
  ABBREV_TAC `S = {x:A | x IN topspace top /\ phi x <= R + &1}` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(rfu_wf lam R (phi x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_PSI_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                 `\x:A. rfu_wf lam R (phi x)`; `S:A->bool`] RFU_ENERGY_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "INT")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "CONT") (LABEL_TAC "DER")))) THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\s. mfd_integral (top,atlas) ((g1:real->A->real^N^N) s) S
          (\x. pde_mkot_density atlas (g1 s) (g2 s) x * rfu_wf lam R ((phi:A->real) x))`;
    `\s. mfd_integral (top,atlas) ((g1:real->A->real^N^N) s) S
          (\x. rfu_tder a (\s. pde_mkot_density atlas (g1 s) (g2 s)) s x *
               rfu_wf lam R ((phi:A->real) x) -
               mfd_scalar atlas (g1 s) x *
               (pde_mkot_density atlas (g1 s) (g2 s) x * rfu_wf lam R (phi x)))`;
    `K2 + H + &1`;
    `K3 * abs M * exp(--(lam * R)) * (abs Cv * exp(abs Cv * (R + &1)))`;
    `a:real`; `t:real`] RFU_GRONWALL_FORCED)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_EXP_POS_LE];
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(g1:real->A->real^N^N) a`;
      `\x. pde_mkot_density atlas ((g1:real->A->real^N^N) a) (g2 a) x *
           rfu_wf lam R ((phi:A->real) x)`;
      `S:A->bool`; `&0`] MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) a)` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFU_INTEGRAL_ZERO_FUN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
    MATCH_MP_TAC RFU_MKOT_SAME THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN S` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{s:real | a <= s /\ s < b}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "DER" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) s)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "DB" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
    `g1:real->A->real^N^N`; `g2:real->A->real^N^N`; `phi:A->real`; `R:real`;
    `H:real`; `M:real`; `s:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "BD" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "DBI") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) s`; `S:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) s`; `S:A->bool`; `v:real`]
                MFD_HAS_VOLUME_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "VV") THEN
  USE_THEN "VOL" (MP_TAC o SPECL [`s:real`; `R + &1`; `v:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`Cv:real`; `R + &1`] RFU_CV_EXP_ABS) THEN
  SUBGOAL_THEN
   `&0 <= mfd_integral (top,atlas) ((g1:real->A->real^N^N) s) S
           (\x. pde_mkot_density atlas (g1 s) (g2 s) x * rfu_wf lam R ((phi:A->real) x))`
  MP_TAC THENL
   [MATCH_MP_TAC RFU_INTEGRAL_NONNEG THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "INT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[RFU_WF_VALUES] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                   `(g1:real->A->real^N^N) s`; `(g2:real->A->real^N^N) s`; `x:A`]
                  PDE_KOT_DENSITY_ZERO) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(x:A) IN S` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= K3 * abs M * exp(--(lam * R))` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K3 * abs M * exp(--(lam * R))`; `v:real`;
                `abs Cv * exp(abs Cv * (R + &1))`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `&0 <= mfd_integral (top,atlas) ((g1:real->A->real^N^N) s) S
           (\x. pde_mkot_density atlas (g1 s) (g2 s) x * rfu_wf lam R ((phi:A->real) x))` THEN
  USE_THEN "VV" (fun vv -> USE_THEN "DBI" (MP_TAC o REWRITE_RULE[vv])) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Monotonicity of the cut-off energies in the radius                        *)
(* (RFU_ENERGY_MONO_R), and the energy argument: under uniform bounds on    *)
(* [a,b1] the Kotschwar density vanishes (RFU_ENERGY_ZERO).                  *)
(* ========================================================================= *)

let RFU_ENERGY_MONO_R = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b g1 g2 phi lam R0 R t.
     hausdorff_space top /\
     ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
     a <= t /\ t < b /\ R0 + &1 <= R /\ &0 <= lam /\ mfd_smooth atlas (lift o phi) /\
     (!c. compact_in top {x | x IN topspace top /\ phi x <= c})
     ==> mfd_integral (top,atlas) (g1 t) {x | x IN topspace top /\ phi x <= R0 + &1}
           (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R0 (phi x))
         <= mfd_integral (top,atlas) (g1 t) {x | x IN topspace top /\ phi x <= R + &1}
              (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R (phi x))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S0 = {x:A | x IN topspace top /\ phi x <= R0 + &1}` THEN
  ABBREV_TAC `S1 = {x:A | x IN topspace top /\ phi x <= R + &1}` THEN
  SUBGOAL_THEN `compact_in top (S0:A->bool) /\ compact_in top (S1:A->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "S1"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(S0:A->bool) SUBSET S1 /\ S1 SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "S1"] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) t) /\
                riemannian_metric atlas ((g2:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!R'. mfd_integrable_on (top,atlas) ((g1:real->A->real^N^N) t)
           (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R' ((phi:A->real) x)) S1`
  (LABEL_TAC "INT") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                   `\x:A. rfu_wf lam R' (phi x)`; `S1:A->bool`] RFU_ENERGY_SETUP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC RFU_PSI_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> &0 <= pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                   `(g1:real->A->real^N^N) t`; `(g2:real->A->real^N^N) t`; `x:A`]
                  PDE_KOT_DENSITY_ZERO) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* split S1 = S0 UNION (S1 DIFF S0) for the R0 function *)
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S0 /\
                mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) (S1 DIFF S0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `f0 = \x. pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
             rfu_wf lam R0 ((phi:A->real) x)` THEN
  SUBGOAL_THEN
   `mfd_integrable_on (top,atlas) ((g1:real->A->real^N^N) t) (f0:A->real) S0 /\
    mfd_integrable_on (top,atlas) (g1 t) f0 (S1 DIFF S0)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `S1:A->bool` THEN
    EXPAND_TAC "f0" THEN ASM_REWRITE_TAC[SUBSET_DIFF];
    ALL_TAC] THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_integral (top,atlas) ((g1:real->A->real^N^N) t) (S1 DIFF S0) (f0:A->real) = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(g1:real->A->real^N^N) t`; `f0:A->real`; `S1 DIFF S0:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_has_integral (top,atlas) ((g1:real->A->real^N^N) t) (\x:A. &1)
                    (S1 DIFF S0) (mfd_integral (top,atlas) (g1 t) (S1 DIFF S0) (\x. &1))`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
      MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `S1:A->bool` THEN
      ASM_REWRITE_TAC[SUBSET_DIFF] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g1:real->A->real^N^N) t`; `S1:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
      ASM_REWRITE_TAC[mfd_has_volume; mfd_integrable_on];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `&0` o MATCH_MP MFD_HAS_INTEGRAL_CMUL) THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    EXPAND_TAC "f0" THEN BETA_TAC THEN MATCH_MP_TAC(REAL_RING `y = &0 ==> &0 = x * y`) THEN
    MP_TAC(SPECL [`lam:real`; `R0:real`; `(phi:A->real) x`] RFU_WF_VALUES) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    UNDISCH_TAC `~((x:A) IN S0)` THEN EXPAND_TAC "S0" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[REAL_NOT_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`; `f0:A->real`; `S0:A->bool`;
                 `S1 DIFF S0:A->bool`;
                 `mfd_integral (top,atlas) ((g1:real->A->real^N^N) t) S0 (f0:A->real)`;
                 `&0`] MFD_HAS_INTEGRAL_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_has_integral (top,atlas) ((g1:real->A->real^N^N) t) (f0:A->real)
                   (S1 DIFF S0) (mfd_integral (top,atlas) (g1 t) (S1 DIFF S0) f0)` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN DISCH_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S0:A->bool) UNION (S1 DIFF S0) = S1` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN DISCH_TAC THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `(g1:real->A->real^N^N) t`; `f0:A->real`;
    `\x. pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
         rfu_wf lam R ((phi:A->real) x)`; `S1:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "INT" (MP_TAC o SPEC `R:real`) THEN REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "f0" THEN BETA_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`lam:real`; `R0:real`; `(phi:A->real) x`] RFU_WF_VALUES) THEN
  MP_TAC(SPECL [`lam:real`; `R:real`; `(phi:A->real) x`] RFU_WF_VALUES) THEN
  ASM_CASES_TAC `(phi:A->real) x <= R` THENL
   [ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `R0 + &1 <= (phi:A->real) x` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]]);;

(* A quantity bounded by C exp(-R) for all large R is nonpositive. *)

let RFU_EXP_DECAY_LIMIT = prove
 (`!E C R0. (!R. R0 <= R ==> E <= C * exp(--R)) ==> E <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `R = max R0 (&0) + abs C / E` THEN
  SUBGOAL_THEN `&0 <= abs C / E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `R:real`) THEN
  ANTS_TAC THENL [EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  SUBGOAL_THEN `abs C / E < exp R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 + R` THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN EXPAND_TAC "R" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs C < exp R * E` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LDIV_EQ]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs C * inv(exp R)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_EXP_POS_LE] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM real_div] THEN
    MP_TAC(SPEC `R:real` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* The energy argument under uniform bounds on [a,b1]. *)

let RFU_ENERGY_ZERO = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b b1 g1 g2 phi
    Lam B Cp Cv H M.
     hausdorff_space top /\
     ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
     b1 < b /\
     (!x. x IN topspace top ==> g1 a x = g2 a x) /\
     mfd_smooth atlas (lift o phi) /\
     (!c. compact_in top {x | x IN topspace top /\ phi x <= c}) /\
     &0 <= H /\
     (!s x. a <= s /\ s <= b1 /\ x IN topspace top
            ==> (!v. v dot (g2 s x ** v) <= Lam * (v dot (g1 s x ** v)) /\
                     v dot (g1 s x ** v) <= Lam * (v dot (g2 s x ** v))) /\
                rfa_rmd2 0 atlas (g1 s) x <= B /\ rfa_rmd2 0 atlas (g2 s) x <= B /\
                rfa_rmd2 1 atlas (g2 s) x <= B /\ rfa_rmd2 2 atlas (g2 s) x <= B /\
                rfu_mgrad2 atlas (g1 s) phi x <= Cp /\
                --H <= mfd_scalar atlas (g1 s) x /\
                pde_mkot_density atlas (g1 s) (g2 s) x <= M) /\
     (!s r v. a <= s /\ s <= b1 /\ &0 <= r /\
              mfd_has_volume (top,atlas) (g1 s) {x | x IN topspace top /\ phi x <= r} v
              ==> v <= Cv * exp(Cv * r))
     ==> !t x. a <= t /\ t <= b1 /\ x IN topspace top
               ==> pde_mkot_density atlas (g1 t) (g2 t) x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`Lam:real`; `B:real`; `Cp:real`; `abs Cv + &1`]
               (INST_TYPE [`:N`,`:N`] RFU_ENERGY_GRONWALL)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:real` (X_CHOOSE_THEN `K3:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GR"))))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x0:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `t:real = a` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFU_MKOT_SAME THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < t /\ t < b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `R0 = (phi:A->real) x0` THEN
  ABBREV_TAC `lam = abs Cv + &1` THEN
  ABBREV_TAC
   `E = \R. mfd_integral (top,atlas) ((g1:real->A->real^N^N) t)
               {x | x IN topspace top /\ phi x <= R + &1}
               (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R ((phi:A->real) x))` THEN
  (* E R is O(exp(-R)) *)
  ABBREV_TAC `C1 = (K3 * abs M * abs Cv * exp(abs Cv)) / (K2 + H + &1) *
                   exp((K2 + H + &1) * (t - a))` THEN
  SUBGOAL_THEN `!R. &0 <= R ==> (E:real->real) R <= C1 * exp(--R)` (LABEL_TAC "SM") THENL
   [X_GEN_TAC `R:real` THEN DISCH_TAC THEN EXPAND_TAC "E" THEN
    USE_THEN "GR" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
      `b1:real`; `g1:real->A->real^N^N`; `g2:real->A->real^N^N`; `phi:A->real`;
      `H:real`; `M:real`; `Cv:real`; `R:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    EXPAND_TAC "C1" THEN EXPAND_TAC "lam" THEN
    SUBGOAL_THEN
     `exp(--((abs Cv + &1) * R)) * exp(abs Cv * (R + &1)) = exp(abs Cv) * exp(--R)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  (* E R0 <= E R for R >= R0 + 1, hence E R0 = 0 *)
  SUBGOAL_THEN `(E:real->real) R0 <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_EXP_DECAY_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`C1:real`; `max (R0 + &1) (&0)`] THEN
    X_GEN_TAC `R:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(E:real->real) R` THEN
    CONJ_TAC THENL [ALL_TAC; USE_THEN "SM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "E" THEN
    MATCH_MP_TAC RFU_ENERGY_MONO_R THEN EXISTS_TAC `a:real` THEN EXISTS_TAC `b:real` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the integral of the R0 energy density vanishes *)
  ABBREV_TAC `S0 = {x:A | x IN topspace top /\ phi x <= R0 + &1}` THEN
  SUBGOAL_THEN `compact_in top (S0:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(rfu_wf lam R0 (phi x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_PSI_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                 `\x:A. rfu_wf lam R0 (phi x)`; `S0:A->bool`] RFU_ENERGY_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) t) /\
                riemannian_metric atlas ((g2:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> &0 <= pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
                  rfu_wf lam R0 ((phi:A->real) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[RFU_WF_VALUES] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                   `(g1:real->A->real^N^N) t`; `(g2:real->A->real^N^N) t`; `x:A`]
                  PDE_KOT_DENSITY_ZERO) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) ((g1:real->A->real^N^N) t)
      (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R0 ((phi:A->real) x))
      S0 (&0)`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME
     `mfd_integrable_on (top,atlas) ((g1:real->A->real^N^N) t)
        (\x. pde_mkot_density atlas (g1 t) (g2 t) x * rfu_wf lam R0 ((phi:A->real) x)) S0`) THEN
    REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN
    MATCH_MP_TAC(MESON[] `(y:real) = x ==> (P:real->bool) x ==> P y`) THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &0 /\ &0 <= x ==> &0 = x`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `(E:real->real) R0 <= &0` THEN EXPAND_TAC "E" THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_INTEGRAL_NONNEG THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:A) IN S0` THEN EXPAND_TAC "S0" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  (* hence the integrand vanishes near x0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `phi:A->real`;
                 `x0:A`; `R0 + &1`] RFU_OPEN_SUBLEVEL_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`;
                 `\x. pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t) x *
                      rfu_wf lam R0 ((phi:A->real) x)`;
                 `S0:A->bool`; `O:A->bool`; `x0:A`] RFU_INTEGRAL_ZERO_IMP_ON) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:A) IN S0` THEN EXPAND_TAC "S0" THEN SIMP_TAC[IN_ELIM_THM];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`;
                     `\s x. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s) x *
                            rfu_wf lam R0 ((phi:A->real) x)`;
                     `c:(A->bool)#(A->real^N)`; `t:real`] RFU_SFUN_CHART_CONTINUOUS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`;
                     `\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)`;
                     `\x:A. rfu_wf lam R0 ((phi:A->real) x)`] RFU_SFUN_MUL_SMOOTH) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC RFU_MKOT_SFUN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "S0" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
  MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
  MP_TAC(SPECL [`lam:real`; `R0:real`; `(phi:A->real) x0`] RFU_WF_VALUES) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `--(lam * R0)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC);;

