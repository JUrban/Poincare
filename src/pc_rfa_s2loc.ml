(* ========================================================================= *)
(* Unit pc_rfa_s2loc: local 2-d facts for the 2-dimensional case of          *)
(* P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT.  In dimension 2                     *)
(* an orthonormal pair gives a frame (RFA_S2_ORTHO2_MATRIX), the Ricci form  *)
(* is diagonal with entries the sectional curvature (RFA_S2_RIC_ORTHO), and  *)
(* Ric = (R/2) g with every sectional curvature R/2 (RFA_S2_EINSTEIN2).      *)
(* On a 2-d gradient shrinker dR = R df and nabla df = (1/2 - R/2) g         *)
(* (RFA_S2_DR_DF, RFA_S2_HESS_CONF, from the general-dimension identity      *)
(* RFA_S2_SOLITON_DR); R = C exp f on a connected shrinker with R > 0        *)
(* (RFA_S2_SCAL_EXPF); along chart geodesic curves (df(y)(y'))' =            *)
(* nabla df(y)(y',y') (RFA_S2_CURVE_HESS).                                   *)
(* ========================================================================= *)

needs "src/pc_rfa_shrink.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* 2-d curvature algebra.                                                    *)
(* ========================================================================= *)

let RFA_S2_ORTHO2_MATRIX = prove
 (`!(G0:real^2^2) u v.
     (!a b. a dot (G0 ** b) = b dot (G0 ** a)) /\
     u dot (G0 ** u) = &1 /\ v dot (G0 ** v) = &1 /\ u dot (G0 ** v) = &0
     ==> ?S:real^2^2. invertible S /\ matrix_inv G0 = transp S ** S /\
                      transp S ** basis 1 = u /\ transp S ** basis 2 = v`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(lambda i j. if i = 1 then (u:real^2)$j else (v:real^2)$j):real^2^2` THEN
  ABBREV_TAC `S = (lambda i j. if i = 1 then (u:real^2)$j else (v:real^2)$j):real^2^2` THEN
  SUBGOAL_THEN `transp (S:real^2^2) ** basis 1 = u /\ transp S ** basis 2 = v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REPEAT CONJ_TAC THEN
    SIMP_TAC[CART_EQ; MATRIX_VECTOR_MUL_BASIS; column; transp; LAMBDA_BETA;
             DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                      ==> ((S:real^2^2) ** (G0:real^2^2) ** transp S)$i$j =
                          (transp S ** basis i) dot (G0 ** (transp S ** basis j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_2; column; LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^2^2) ** (G0:real^2^2) ** transp S = mat 1` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SUBGOAL_THEN `(v:real^2) dot ((G0:real^2^2) ** u) = &0` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH; MAT_COMPONENT; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv (G0:real^2^2) = transp (S:real^2^2) ** S` ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    SUBGOAL_THEN `(G0:real^2^2) ** (transp (S:real^2^2) ** S) = mat 1` ASSUME_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
      ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE] THEN
  EXISTS_TAC `(G0:real^2^2) ** transp (S:real^2^2)` THEN ASM_REWRITE_TAC[]);;

let RFA_S2_RIC_ORTHO = prove
 (`!U (G:real^2->real^2^2) y u v.
     metric_field U G /\ y IN U /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ u dot (G y ** v) = &0
     ==> lricci G y u u = lsectional G y u v /\
         lricci G y v v = lsectional G y u v /\
         lricci G y u v = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `u:real^2`; `v:real^2`] RFA_S2_ORTHO2_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `lsectional (G:real^2->real^2^2) y u v =
                lrm4 G y (\m. if m = 1 then u else if m = 2 then v
                              else if m = 3 then u else v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[lsectional; lrm4] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `S:real^2^2`]
                RFA_RIC_FRAME_RM) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; SUM_2] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`]
                RFA_LRM4_ZERO12) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`]
                RFA_LRM4_ZERO34) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `v:real^2`; `u:real^2`]
                RFA_LRM4_SWAP_PAIRS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]);;

let RFA_S2_EINSTEIN2 = prove
 (`!U (G:real^2->real^2^2) y.
     metric_field U G /\ y IN U
     ==> (!v w. lricci G y v w = lscalar G y / &2 * (v dot (G y ** w))) /\
         (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v = lscalar G y / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^2->real^2^2) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
          ==> (transp (S:real^2^2) ** basis a) dot ((G:real^2->real^2^2) y ** (transp S ** basis b)) =
              if a = b then &1 else &0`
  (LABEL_TAC "on") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  ABBREV_TAC `K = lsectional (G:real^2->real^2^2) y (transp (S:real^2^2) ** basis 1)
                    (transp S ** basis 2)` THEN
  SUBGOAL_THEN
   `lricci (G:real^2->real^2^2) y (transp (S:real^2^2) ** basis 1) (transp S ** basis 1) = K /\
    lricci G y (transp S ** basis 2) (transp S ** basis 2) = K /\
    lricci G y (transp S ** basis 1) (transp S ** basis 2) = &0 /\
    lricci G y (transp S ** basis 2) (transp S ** basis 1) = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`;
                   `transp (S:real^2^2) ** basis 1`; `transp (S:real^2^2) ** basis 2`]
                  RFA_S2_RIC_ORTHO) THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`;
                   `transp (S:real^2^2) ** basis 2`; `transp (S:real^2^2) ** basis 1`]
                  RFA_S2_RIC_ORTHO) THEN
    USE_THEN "on" (fun th -> SIMP_TAC[th; ARITH]) THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`;
                   `transp (S:real^2^2) ** basis 2`; `transp (S:real^2^2) ** basis 1`]
                  RFA_LSECTIONAL_SWAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (G:real^2->real^2^2) y = &2 * K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `S:real^2^2`]
                  RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_2; SUM_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w. lricci (G:real^2->real^2^2) y v w = K * (v dot (G y ** w))`
  (LABEL_TAC "ein") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `S:real^2^2`; `lricci (G:real^2->real^2^2) y`;
                   `\v w. K * (v dot ((G:real^2->real^2^2) y ** w))`;
                   `v:real^2`; `w:real^2`] RFA_BILIN_FRAME_EQ) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
      REWRITE_TAC[LINEAR_LIFT_DOT];
      GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR];
      ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_2] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    USE_THEN "on" (MP_TAC o SPECL [`a:num`; `b:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `(a = 1 \/ a = 2) /\ (b = 1 \/ b = 2)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `u:real^2`; `v:real^2`]
                RFA_GS_ORTHO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^2` (X_CHOOSE_THEN `v1:real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)))))) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `u1:real^2`; `v1:real^2`]
                RFA_S2_RIC_ORTHO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
  USE_THEN "ein" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The gradient shrinker identity in frames.  The                            *)
(* permuted product of RFA_SH_P_EQON evaluated at a frame tuple              *)
(* (RFA_S2_RHS_FRAME); dR(e_b) = 2 sum_c Ric(e_b,e_c) df(e_c) in any         *)
(* dimension (RFA_S2_SOLITON_DR: RFA_SH_P_EQON at [i;i;b] summed over i,     *)
(* with RFA_SH_CB_FRAME and RFA_HT_DSC_FRAME); in dimension 2, where         *)
(* Ric = (R/2) g, dR = R df (RFA_S2_DR_DF) and nabla df = (1/2 - R/2) g      *)
(* (RFA_S2_HESS_CONF).                                                       *)
(* ========================================================================= *)

let RFA_S2_RHS_FRAME = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) y (S:real^N^N) i j k.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(pf z)) /\
     matrix_inv(G y) = transp S ** S
     ==> ltcontr G (ltperm (\m. if m = 1 then 4 else if m = 2 then 5 else if m = 3 then 1
                                else if m = 4 then 3 else if m = 5 then 2 else m)
                          (ltprod 4 (lrm4 G) (rfa_sh_df pf))) y (rfa_ft S [i; j; k]) =
         sum(1..dimindex(:N))
           (\s. lrm4 G y (rfa_ft S [j; k; s; i]) * rfa_sh_df pf y (rfa_ft S [s]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sf 5 U (ltprod 4 (lrm4 (G:real^N->real^N^N)) (rfa_sh_df (pf:real^N->real)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`4`; `1`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                   `rfa_sh_df (pf:real^N->real)`] RFA_SF_LTPROD) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RFA_SF_LRM4; RFA_SH_DF_SF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`5`; `(\m. if m = 1 then 4 else if m = 2 then 5 else if m = 3 then 1
                            else if m = 4 then 3 else if m = 5 then 2 else m)`;
                 `U:real^N->bool`;
                 `ltprod 4 (lrm4 (G:real^N->real^N^N)) (rfa_sh_df (pf:real^N->real))`]
                RFA_SF_LTPERM) THEN
  ASM_REWRITE_TAC[RFA_SH_SIGMA_PERMUTES] THEN REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm (\m. if m = 1 then 4 else if m = 2 then 5 else if m = 3 then 1
                              else if m = 4 then 3 else if m = 5 then 2 else m)
                    (ltprod 4 (lrm4 (G:real^N->real^N^N)) (rfa_sh_df (pf:real^N->real)))`;
                 `y:real^N`; `S:real^N^N`; `rfa_ft (S:real^N^N) [i; j; k]`] RFA_LTCONTR_FRAMEV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ltperm; ltprod; lrm4; rfa_sh_df] THEN CONV_TAC RFA_TUPLE_VAL_CONV);;

let RFA_S2_SOLITON_DR = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) y (S:real^N^N) b.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S /\
     smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> drop(frechet_derivative (\x. lift(lscalar G x)) (at y) (transp S ** basis b)) =
         &2 * sum(1..dimindex(:N))
                (\c. lricci G y (transp S ** basis b) (transp S ** basis c) *
                     rfa_sh_df pf y (rfa_ft S [c]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`] RFA_SH_P_EQON) THEN
  ASM_REWRITE_TAC[rfa_eqon] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ltensor_field 3 U (lnabla 2 G (lric2 (G:real^N->real^N^N)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRIC2; rfa_sf; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. sum(1..dimindex(:N))
          (\s. lrm4 G y (rfa_ft S [i; b; s; i]) * rfa_sh_df (pf:real^N->real) y (rfa_ft S [s])) =
        lnabla 2 G (lric2 (G:real^N->real^N^N)) y (rfa_ft (S:real^N^N) [i; b; i]) -
        lnabla 2 G (lric2 G) y (rfa_ft S [i; i; b])`
  (LABEL_TAC "pi") THENL
   [X_GEN_TAC `i:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `rfa_ft (S:real^N^N) [i; i; b]`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`; `y:real^N`;
                   `S:real^N^N`; `i:num`; `i:num`; `b:num`] RFA_S2_RHS_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ltperm] THEN BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC RFA_TUPLE_VAL_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. sum(1..dimindex(:N)) (\i. lrm4 G y (rfa_ft (S:real^N^N) [i; b; s; i])) =
        --(lricci (G:real^N->real^N^N) y (transp S ** basis b) (transp S ** basis s))`
  (LABEL_TAC "lrm") THENL
   [X_GEN_TAC `s:num` THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`;
                   `transp (S:real^N^N) ** basis b`; `transp (S:real^N^N) ** basis s`]
                  RFA_RIC_FRAME_RM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`i:num`; `b:num`; `i:num`; `s:num`]
           (MP (ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`]
                       RFA_LRM4_FT_SYMS)
               (CONJ (ASSUME `metric_field U (G:real^N->real^N^N)`) (ASSUME `(y:real^N) IN U`)))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC RFA_TUPLE_VAL_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`; `b:num`]
                RFA_SH_CB_FRAME) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`; `b:num`]
                RFA_HT_DSC_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dsc") THEN DISCH_THEN(LABEL_TAC "cb") THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
       (\s. lrm4 G y (rfa_ft S [i; b; s; i]) * rfa_sh_df (pf:real^N->real) y (rfa_ft S [s]))) =
    --(sum(1..dimindex(:N)) (\c. lricci (G:real^N->real^N^N) y (transp (S:real^N^N) ** basis b)
                                   (transp S ** basis c) * rfa_sh_df pf y (rfa_ft S [c])))`
  MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[SUM_RMUL] THEN
    USE_THEN "lrm" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[REAL_MUL_LNEG; SUM_NEG];
    ALL_TAC] THEN
  USE_THEN "pi" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SUM_SUB_NUMSEG] THEN
  USE_THEN "cb" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "dsc" (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

let RFA_S2_DR_DF = prove
 (`!U (G:real^2->real^2^2) (pf:real^2->real) y v.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> drop(frechet_derivative (\x. lift(lscalar G x)) (at y) v) =
         lscalar G y * drop(frechet_derivative (\x. lift(pf x)) (at y) v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^2->real^2^2) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (\x. lift((pf:real^2->real) x)) (at y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. 1 <= b /\ b <= 2
        ==> drop(frechet_derivative (\x. lift(lscalar (G:real^2->real^2^2) x)) (at y)
                                    (transp (S:real^2^2) ** basis b)) =
            lscalar G y * drop(frechet_derivative (\x. lift((pf:real^2->real) x)) (at y)
                                                  (transp S ** basis b))`
  (LABEL_TAC "fr") THENL
   [X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `pf:real^2->real`; `y:real^2`;
                   `S:real^2^2`; `b:num`] RFA_S2_SOLITON_DR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] RFA_S2_EINSTEIN2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    REWRITE_TAC[DIMINDEX_2; SUM_2; rfa_sh_df] THEN CONV_TAC RFA_TUPLE_VAL_CONV THEN
    MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `S:real^2^2`; `b:num`; `1`] RFA_GFRAME_ORTHO) THEN
    MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `S:real^2^2`; `b:num`; `2`] RFA_GFRAME_ORTHO) THEN
    ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `b = 1 \/ b = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `S:real^2^2`; `v:real^2`]
                RFA_HT_DSC_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `S:real^2^2`; `v:real^2`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`\v. drop(frechet_derivative (\x. lift((pf:real^2->real) x)) (at y) v)`;
                 `1..dimindex(:2)`;
                 `\r. (transp (S:real^2^2) ** basis r) dot ((G:real^2->real^2^2) y ** v)`;
                 `\r. transp (S:real^2^2) ** basis r`] RFA_LINEAR_SUM_EXPAND) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; FINITE_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `r:num` THEN REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "fr" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `1 <= r`) (ASSUME `r <= 2`))]) THEN
  REAL_ARITH_TAC);;

let RFA_S2_HESS_CONF = prove
 (`!U (G:real^2->real^2^2) (pf:real^2->real) y u.
     metric_field U G /\ y IN U /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> lnabla 1 G (rfa_sh_df pf) y u = (inv(&2) - lscalar G y / &2) * lmetric2 G y u`,
  REWRITE_TAC[rfa_eqon] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] RFA_S2_EINSTEIN2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[lric2; lmetric2; CONJUNCT1 th]) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* R = C exp f.  log R - f has zero derivative in charts                     *)
(* (RFA_S2_LOGR_DERIV0); a function whose chart representatives have zero   *)
(* derivative is locally constant (RFA_S2_LOCCONST_CHART); in dimension 2    *)
(* every sectional curvature is R/2 (RFA_S2_MFD_SEC_SCAL); on a connected    *)
(* 2-d shrinker with R > 0, R = C exp f for a constant C > 0                 *)
(* (RFA_S2_SCAL_EXPF).                                                       *)
(* ========================================================================= *)

let RFA_S2_LOGR_DERIV0 = prove
 (`!U (G:real^2->real^2^2) (pf:real^2->real) z.
     metric_field U G /\ z IN U /\ smooth_map_on U (\w. lift(pf w)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u) /\
     &0 < lscalar G z
     ==> ((\w. lift(log(lscalar G w) - pf w)) has_derivative (\v. vec 0)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift(lscalar (G:real^2->real^2^2) w)) has_derivative
     frechet_derivative (\x. lift(lscalar G x)) (at z)) (at z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift((pf:real^2->real) w)) has_derivative
     frechet_derivative (\x. lift(pf x)) (at z)) (at z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((lift o log o drop) has_derivative (\x. inv(lscalar (G:real^2->real^2^2) z) % x))
    (at (lift(lscalar G z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift(log(lscalar (G:real^2->real^2^2) w) - (pf:real^2->real) w)) =
    (\w. ((lift o log o drop) o (\w. lift(lscalar G w))) w - lift(pf w))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; LIFT_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v:real^2. vec 0:real^1) =
    (\h. ((\x. inv(lscalar (G:real^2->real^2^2) z) % x) o
          frechet_derivative (\x. lift(lscalar G x)) (at z)) h -
         frechet_derivative (\x. lift((pf:real^2->real) x)) (at z) h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^2` THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_CMUL; DROP_VEC] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `pf:real^2->real`; `z:real^2`;
                   `h:real^2`] RFA_S2_DR_DF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `&0 < lscalar (G:real^2->real^2^2) z` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
  ASM_REWRITE_TAC[]);;

let RFA_S2_LOCCONST_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (h:A->real).
     smooth_manifold_atlas top atlas /\
     (!c z. c IN atlas /\ z IN IMAGE (SND c) (FST c)
            ==> ((\w. lift(h(chart_inv c w))) has_derivative (\v. vec 0)) (at z))
     ==> !x. x IN topspace top
             ==> ?W. open_in top W /\ x IN W /\ !x'. x' IN W ==> h x' = h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U phi. chart_at atlas (x:A) = (U:A->bool,phi:A->real^N)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:A->real^N) x IN IMAGE phi U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (phi:A->real^N) U` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) x`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z. z IN ball((phi:A->real^N) x,r)
        ==> (h:A->real)(chart_inv (U,phi) z) = h(chart_inv (U,phi) (phi x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w. lift((h:A->real)(chart_inv (U:A->bool,phi:A->real^N) w))`;
                   `ball((phi:A->real^N) x,r)`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`; `z:real^N`]) THEN
      ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^1` (LABEL_TAC "cst")) THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "cst" (fun th -> MP_TAC(BETA_RULE(SPEC `z:real^N` th)) THEN
                                 MP_TAC(BETA_RULE(SPEC `(phi:A->real^N) x` th))) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    REWRITE_TAC[GSYM LIFT_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{x':A | x' IN U /\ (phi:A->real^N) x' IN ball(phi x,r)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`; `euclidean:(real^N)topology`;
                   `ball((phi:A->real^N) x,r)`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL] THEN ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x':A` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->real^N) x'` o
    check (fun th -> can (find_term ((=) `ball((phi:A->real^N) x,r)`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_SIMP_TAC[]);;

let RFA_S2_MFD_SEC_SCAL = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     ~collinear {vec 0,u,v}
     ==> mfd_sectional atlas g x u v = mfd_scalar atlas g x / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sectional; mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A))
                               (g:A->real^2^2)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)) x`] RFA_S2_EINSTEIN2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;

let RFA_S2_BASIS_NONCOLL = prove
 (`~collinear {vec 0, basis 1:real^2, basis 2}`,
  REWRITE_TAC[COLLINEAR_LEMMA] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH; NOT_EXISTS_THM] THEN
  X_GEN_TAC `c:real` THEN DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$2`) THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let RFA_S2_SCAL_EXPF = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real).
     connected_space top /\ p2b_shrinker (top,atlas) g f /\
     (!x. x IN topspace top ==> &0 < mfd_scalar atlas g x)
     ==> ?C. &0 < C /\ !x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `\x:A. log(mfd_scalar atlas (g:A->real^2^2) x) - (f:A->real) x`]
                RFA_S2_LOCCONST_CHART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^2)`; `z:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `f:A->real`; `c:(A->bool)#(A->real^2)`] RFA_SH_CHART_DATA) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?U phi. c = (U:A->bool,phi:A->real^2)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    REWRITE_TAC[FST; SND] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `U:A->bool`; `phi:A->real^2`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `U:A->bool`; `phi:A->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!w. w IN IMAGE (phi:A->real^2) U
          ==> mfd_scalar atlas (g:A->real^2^2) (chart_inv (U,phi) w) =
              lscalar (metric_local atlas (U,phi) g) w`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `(U:A->bool,phi:A->real^2)`; `chart_inv (U:A->bool,phi:A->real^2) w`]
                    RFA_SH_QR_CHART) THEN
      ASM_SIMP_TAC[FST; SND];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\w. lift(log(lscalar (metric_local atlas (U,phi) (g:A->real^2^2)) w) -
                         (\y. (f:A->real)(chart_inv (U:A->bool,phi:A->real^2) y)) w)` THEN
    MP_TAC(ISPEC `IMAGE (phi:A->real^2) U` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^2) IN IMAGE (phi:A->real^2) U` ASSUME_TAC THENL
       [SUBGOAL_THEN `(w:real^2) IN ball(z,d)` MP_TAC THENL
         [REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]; ASM SET_TAC[]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_S2_LOGR_DERIV0 THEN EXISTS_TAC `IMAGE (phi:A->real^2) U` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lscalar (metric_local atlas (U,phi) (g:A->real^2^2)) z =
                  mfd_scalar atlas g (chart_inv (U:A->bool,phi:A->real^2) z)`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\x:A. log(mfd_scalar atlas (g:A->real^2^2) x) - (f:A->real) x`]
                RFA_SH_LOCCONST_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `exp(log(mfd_scalar atlas (g:A->real^2^2) x0) - (f:A->real) x0)` THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x0:A`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^2^2) x = exp(log(mfd_scalar atlas g x))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Calculus along chart curves.  Along a chart curve y                       *)
(* with y' = v and v' = -Gamma(v,v) the derivative of df(y)(v) is           *)
(* nabla df (y)(v,v) (RFA_S2_CURVE_HESS, from GEOL_FRECHET_ALONG); the first  *)
(* derivative of f o y is df(y)(y') (RFA_S2_CURVE_D1).                       *)
(* ========================================================================= *)

let RFA_S2_CURVE_HESS = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) (y:real^1->real^N) (v:real^1->real^N) t.
     open U /\ smooth_map_on U (\z. lift(pf z)) /\ y t IN U /\
     (y has_vector_derivative v t) (at t) /\
     (v has_vector_derivative --(christoffel G (y t) (v t) (v t))) (at t)
     ==> ((\r. frechet_derivative (\x. lift(pf x)) (at (y r)) (v r)) has_vector_derivative
          lift(lnabla 1 G (rfa_sh_df pf) (y t) (\m. v t))) (at t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (\x. lift((pf:real^N->real) x))
                                          (at ((y:real^1->real^N) t)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\x. lift((pf:real^N->real) x)`; `y:real^1->real^N`;
                 `v:real^1->real^N`; `(v:real^1->real^N) t`;
                 `--(christoffel (G:real^N->real^N^N) ((y:real^1->real^N) t) (v t) (v t))`;
                 `t:real^1`] GEOL_FRECHET_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[lnabla; rfa_sh_df; SUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN ASM_SIMP_TAC[LINEAR_NEG] THEN
  VECTOR_ARITH_TAC);;

let RFA_S2_CURVE_D1 = prove
 (`!U (pf:real^N->real) (y:real^1->real^N) v t.
     open U /\ smooth_map_on U (\z. lift(pf z)) /\ y t IN U /\
     (y has_vector_derivative v) (at t)
     ==> ((\r. lift(pf(y r))) has_vector_derivative
          frechet_derivative (\x. lift(pf x)) (at (y t)) v) (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^1->real^N`; `\x. lift((pf:real^N->real) x)`; `v:real^N`;
                 `frechet_derivative (\x. lift((pf:real^N->real) x)) (at ((y:real^1->real^N) t))`;
                 `t:real^1`] ODE_HAS_VECTOR_DERIVATIVE_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

